/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_coi_filter.cpp

Abstract:

    Rule transformer which removes relations which are out of the cone of 
    influence of output relations

Author:

    Krystof Hoder (t-khoder) 2011-10-01.

Revision History:

    Andrey Rybalchenko (rybal) 2013-8-8
    Added bottom_up pruning.

--*/


#include <sstream>
#include"ast_pp.h"
#include"dl_mk_coi_filter.h"
#include"extension_model_converter.h"

namespace datalog {
  
    // -----------------------------------
    //
    // mk_coi_filter
    //
    // -----------------------------------

    rule_set * mk_coi_filter::operator()(rule_set const & source) {
        if (!m_context.xform_coi()) {
            return 0;
        }
        if (source.empty()) {
            return 0;
        }
        scoped_ptr<rule_set> result1 = top_down(source);
        scoped_ptr<rule_set> result2 = bottom_up(result1?*result1:source);
        if (!result2) {
            result2 = result1.detach();
        }
        return result2.detach();
    }

    rule_set * mk_coi_filter::bottom_up(rule_set const & source) {
        func_decl_set all, reached;
        ptr_vector<func_decl> todo;
        rule_set::decl2rules body2rules;
        // initialization for reachability
        for (rule_set::iterator it = source.begin(); it != source.end(); ++it) {
            rule * r = *it;
            all.insert(r->get_decl());
            if (r->get_uninterpreted_tail_size() == 0) {
                if (!reached.contains(r->get_decl())) {
                    reached.insert(r->get_decl());
                    todo.insert(r->get_decl());
                }
            } 
            else {
                for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                    func_decl * d = r->get_tail(i)->get_decl();
                    all.insert(d);
                    rule_set::decl2rules::obj_map_entry * e = body2rules.insert_if_not_there2(d, 0);
                    if (!e->get_data().m_value) {
                        e->get_data().m_value = alloc(ptr_vector<rule>);
                    }
                    e->get_data().m_value->push_back(r);
                    if (r->is_neg_tail(i)) {
                        // don't try COI on rule with negation.
                        return 0;
                    }
                }
            }
        }
        rel_context_base* rc = m_context.get_rel_context();
        if (rc) {
            func_decl_set::iterator fit = all.begin(), fend = all.end();
            for (; fit != fend; ++fit) {
                if (!rc->is_empty_relation(*fit) &&
                    !reached.contains(*fit)) {
                    reached.insert(*fit);
                    todo.insert(*fit);
                }
            }                 
        }
        // reachability computation
        while (!todo.empty()) {
            func_decl * d = todo.back();
            todo.pop_back();
            ptr_vector<rule> * rules; 
            if (!body2rules.find(d, rules)) continue;
            for (ptr_vector<rule>::iterator it = rules->begin(); it != rules->end(); ++it) {
                rule * r = *it;
                if (reached.contains(r->get_decl())) continue;
                bool contained = true;
                for (unsigned i = 0; contained && i < r->get_uninterpreted_tail_size(); ++i) {
                    contained = reached.contains(r->get_tail(i)->get_decl());
                }
                if (!contained) continue;
                reached.insert(r->get_decl());
                todo.insert(r->get_decl());
            }
        }

        // eliminate each rule when some body predicate is not reached
        scoped_ptr<rule_set> res = alloc(rule_set, m_context);
        res->inherit_predicates(source);
        for (rule_set::iterator it = source.begin(); it != source.end(); ++it) {
            rule * r = *it;

            bool contained = true;
            for (unsigned i = 0; contained && i < r->get_uninterpreted_tail_size(); ++i) {
                contained = reached.contains(r->get_tail(i)->get_decl());
            }
            if (contained) {
                res->add_rule(r);
            }
        }
        if (res->get_num_rules() == source.get_num_rules()) {
            TRACE("dl", tout << "No transformation\n";);
            res = 0;
        }
        else {
            res->close();
        }

        // set to false each unreached predicate 
        if (m_context.get_model_converter()) {
            extension_model_converter* mc0 = alloc(extension_model_converter, m);
            for (func_decl_set::iterator it = all.begin(); it != all.end(); ++it) {
                if (!reached.contains(*it)) {
                    mc0->insert(*it, m.mk_false());
                }
            }   
            m_context.add_model_converter(mc0);
        }
        // clean up body2rules range resources
        for (rule_set::decl2rules::iterator it = body2rules.begin(); it != body2rules.end(); ++it) {
            dealloc(it->m_value);
        }
        CTRACE("dl", 0 != res, res->display(tout););
        return res.detach();
    }

    rule_set * mk_coi_filter::top_down(rule_set const & source) {

        func_decl_set interesting_preds;
        func_decl_set pruned_preds;
        ptr_vector<func_decl> todo;
        {
            const func_decl_set& output_preds = source.get_output_predicates();
            func_decl_set::iterator oend = output_preds.end();
            for (func_decl_set::iterator it = output_preds.begin(); it!=oend; ++it) {
                todo.push_back(*it);
                interesting_preds.insert(*it);
            }
        }

        const rule_dependencies& deps = source.get_dependencies();

        while (!todo.empty()) {
            func_decl * curr = todo.back();
            todo.pop_back();
            interesting_preds.insert(curr);

            const rule_dependencies::item_set& cdeps = deps.get_deps(curr);
            rule_dependencies::item_set::iterator dend = cdeps.end();
            for (rule_dependencies::item_set::iterator it = cdeps.begin(); it != dend; ++it) {
                func_decl * dep_pred = *it;
                if (!interesting_preds.contains(dep_pred)) {
                    interesting_preds.insert(dep_pred);
                    todo.push_back(dep_pred);
                }
            }
        }

        scoped_ptr<rule_set> res = alloc(rule_set, m_context);
        res->inherit_predicates(source);

        rule_set::iterator rend = source.end();
        for (rule_set::iterator rit = source.begin(); rit != rend; ++rit) {
            rule * r = *rit;
            func_decl * pred = r->get_decl();
            if (interesting_preds.contains(pred)) {
                res->add_rule(r);
            }
            else if (m_context.get_model_converter()) {
                pruned_preds.insert(pred);
            }
        }

        if (res->get_num_rules() == source.get_num_rules()) {
            TRACE("dl", tout << "No transformation\n";);
            res = 0;
        }

        if (res && m_context.get_model_converter()) {
            func_decl_set::iterator end = pruned_preds.end();
            func_decl_set::iterator it = pruned_preds.begin();
            extension_model_converter* mc0 = alloc(extension_model_converter, m);
            for (; it != end; ++it) {
                const rule_vector& rules = source.get_predicate_rules(*it);
                expr_ref_vector fmls(m);
                for (unsigned i = 0; i < rules.size(); ++i) {
                    app* head = rules[i]->get_head();
                    expr_ref_vector conj(m);
                    for (unsigned j = 0; j < head->get_num_args(); ++j) {
                        expr* arg = head->get_arg(j);
                        if (!is_var(arg)) {
                            conj.push_back(m.mk_eq(m.mk_var(j, m.get_sort(arg)), arg));
                        }
                    }                    
                    fmls.push_back(m.mk_and(conj.size(), conj.c_ptr()));
                }
                expr_ref fml(m);
                fml = m.mk_or(fmls.size(), fmls.c_ptr());
                mc0->insert(*it, fml);
            }   
            m_context.add_model_converter(mc0);
        }
        CTRACE("dl", 0 != res, res->display(tout););
        return res.detach();
    }

};

