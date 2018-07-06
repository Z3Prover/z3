/*++
Copyright (c) 2006-2015 Microsoft Corporation

Module Name:

    dl_mk_coi_filter.cpp

Abstract:

    Rule transformer which removes relations which are out of the cone of
    influence of output relations

Author:
    Krystof Hoder (t-khoder)
    Andrey Rybalchenko (rybal)
    Henning Guenther (t-hennig)

--*/

#include "muz/transforms/dl_mk_coi_filter.h"
#include "muz/dataflow/dataflow.h"
#include "muz/dataflow/reachability.h"
#include "ast/ast_pp.h"
#include "tactic/generic_model_converter.h"
#include "ast/ast_util.h"

namespace datalog {
    rule_set * mk_coi_filter::operator()(rule_set const & source) {
        scoped_ptr<rule_set> result1 = top_down(source);
        scoped_ptr<rule_set> result2 = bottom_up(result1 ? *result1 : source);
        return result2 ? result2.detach() : result1.detach();
    }

    rule_set * mk_coi_filter::bottom_up(rule_set const & source) {
        dataflow_engine<reachability_info> engine(source.get_manager(), source);
        engine.run_bottom_up();
        func_decl_set unreachable;
        scoped_ptr<rule_set> res = alloc(rule_set, m_context);
        res->inherit_predicates(source);
        for (rule* r : source) {
            bool new_tail = false;
            bool contained = true;
            m_new_tail.reset();
            m_new_tail_neg.reset();
            for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                func_decl* decl_i = r->get_decl(i);
                if (m_context.has_facts(decl_i)) {
                    return nullptr;
                }

                bool reachable = engine.get_fact(decl_i).is_reachable();

                if (!reachable) {
                    unreachable.insert(decl_i);
                }

                if (r->is_neg_tail(i)) {
                    if (!reachable) {
                        if (!new_tail) {
                            for (unsigned j = 0; j < i; ++j) {
                                m_new_tail.push_back(r->get_tail(j));
                                m_new_tail_neg.push_back(r->is_neg_tail(j));
                            }
                            new_tail = true;
                        }
                    } 
                    else if (new_tail) {
                        m_new_tail.push_back(r->get_tail(i));
                        m_new_tail_neg.push_back(true);
                    }
                } 
                else {
                    SASSERT(!new_tail);
                    if (!reachable) {
                        contained = false;
                        break;
                    }
                }
            }
            if (contained) {
                if (new_tail) {
                    for (unsigned i = r->get_uninterpreted_tail_size(); i < r->get_tail_size(); ++i) {
                        m_new_tail.push_back(r->get_tail(i));
                        m_new_tail_neg.push_back(false);                        
                    }
                    rule* new_r = m_context.get_rule_manager().mk(r->get_head(), m_new_tail.size(),
                        m_new_tail.c_ptr(), m_new_tail_neg.c_ptr(), symbol::null, false);
                    res->add_rule(new_r);
                } else {
                    res->add_rule(r);
                }
            }
        }
        if (res->get_num_rules() == source.get_num_rules()) {
            TRACE("dl", tout << "No transformation\n";);
            res = nullptr;
        } 
        else {
            res->close();
        }
        
        // set to false each unreached predicate 
        if (res && m_context.get_model_converter()) {
            generic_model_converter* mc0 = alloc(generic_model_converter, m, "dl_coi");
            for (auto const& kv : engine) {
                if (!kv.m_value.is_reachable()) {
                    mc0->add(kv.m_key, m.mk_false());
                }
            }
            for (func_decl* f : unreachable) {
                mc0->add(f, m.mk_false());
            }
            m_context.add_model_converter(mc0);
        }
        CTRACE("dl", 0 != res, res->display(tout););
        return res.detach();
    }

    rule_set * mk_coi_filter::top_down(rule_set const & source) {
        func_decl_set pruned_preds;
        dataflow_engine<reachability_info> engine(source.get_manager(), source);
        engine.run_top_down();
        scoped_ptr<rule_set> res = alloc(rule_set, m_context);
        res->inherit_predicates(source);

        for (rule * r : source) {
            func_decl * pred = r->get_decl();
            if (engine.get_fact(pred).is_reachable()) {
                res->add_rule(r);
            } else if (m_context.get_model_converter()) {
                pruned_preds.insert(pred);
            }
        }

        if (res->get_num_rules() == source.get_num_rules()) {
            TRACE("dl", tout << "No transformation\n";);
            res = nullptr;
        }
        if (res && m_context.get_model_converter()) {
            generic_model_converter* mc0 = alloc(generic_model_converter, m, "dl_coi");
            for (func_decl* f : pruned_preds) {
                const rule_vector& rules = source.get_predicate_rules(f);
                expr_ref_vector fmls(m);
                for (rule * r : rules) {
                    app* head = r->get_head();
                    expr_ref_vector conj(m);
                    for (unsigned j = 0; j < head->get_num_args(); ++j) {
                        expr* arg = head->get_arg(j);
                        if (!is_var(arg)) {
                            conj.push_back(m.mk_eq(m.mk_var(j, m.get_sort(arg)), arg));
                        }
                    }
                    fmls.push_back(mk_and(conj));
                }
                expr_ref fml(m);
                fml = m.mk_or(fmls.size(), fmls.c_ptr());
                mc0->add(f, fml);
            }
            m_context.add_model_converter(mc0);
        }
        CTRACE("dl", 0 != res, res->display(tout););
        return res.detach();
    }
}
