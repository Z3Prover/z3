/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_array_blast.cpp

Abstract:

    Remove array stores from rules.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-23

Revision History:

--*/

#include "dl_mk_array_blast.h"
#include "expr_replacer.h"

namespace datalog {


    mk_array_blast::mk_array_blast(context & ctx, unsigned priority) : 
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()), 
        a(m),
        rm(ctx.get_rule_manager()),
        m_rewriter(m, m_params){
        m_params.set_bool("expand_select_store",true);
        m_rewriter.updt_params(m_params);
    }

    mk_array_blast::~mk_array_blast() {
    }

    bool mk_array_blast::is_store_def(expr* e, expr*& x, expr*& y) {
        if (m.is_iff(e, x, y) || m.is_eq(e, x, y)) {
            if (!a.is_store(y)) {
                std::swap(x,y);
            }
            if (is_var(x) && a.is_store(y)) {
                return true;
            }
        }
        return false;
    }

    bool mk_array_blast::blast(rule& r, rule_set& rules) {
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz = r.get_tail_size();
        expr_ref_vector conjs(m), new_conjs(m);
        expr_ref tmp(m);
        expr_substitution sub(m);
        uint_set lhs_vars, rhs_vars;
        bool change = false;

        for (unsigned i = 0; i < utsz; ++i) {
            new_conjs.push_back(r.get_tail(i));
        }
        for (unsigned i = utsz; i < tsz; ++i) {
            conjs.push_back(r.get_tail(i));
        }
        flatten_and(conjs);
        for (unsigned i = 0; i < conjs.size(); ++i) {
            expr* x, *y, *e = conjs[i].get();
            
            if (is_store_def(e, x, y)) {
                // enforce topological order consistency:
                uint_set lhs;
                collect_vars(m, x, lhs_vars);
                collect_vars(m, y, rhs_vars);
                lhs = lhs_vars;
                lhs &= rhs_vars;
                if (!lhs.empty()) {
                    TRACE("dl", tout << "unusable equality " << mk_pp(e, m) << "\n";);
                    new_conjs.push_back(e);
                }
                else {
                    sub.insert(x, y);
                }
            }
            else {
                m_rewriter(e, tmp);
                change = change || (tmp != e);
                new_conjs.push_back(tmp);
            }
        }
        if (sub.empty() && !change) {
            rules.add_rule(&r);
            return false;
        }
        
        rule_ref_vector new_rules(rm);
        expr_ref fml1(m), fml2(m), body(m), head(m);
        r.to_formula(fml1);
        body = m.mk_and(new_conjs.size(), new_conjs.c_ptr());
        head = r.get_head();
        scoped_ptr<expr_replacer> replace = mk_default_expr_replacer(m);
        replace->set_substitution(&sub);
        (*replace)(body);
        m_rewriter(body);
        (*replace)(head);
        m_rewriter(head);
        fml2 = m.mk_implies(body, head);
        rm.mk_rule(fml2, new_rules, r.name());
        SASSERT(new_rules.size() == 1);

        TRACE("dl", tout << "new body " << mk_pp(fml2, m) << "\n";);
        
        rules.add_rule(new_rules[0].get());
        if (m_pc) {
            new_rules[0]->to_formula(fml2);
            m_pc->insert(fml1, fml2);
        }
        return true;
    }
    
    rule_set * mk_array_blast::operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc) {
        ref<equiv_proof_converter> epc;
        if (pc) {
            epc = alloc(equiv_proof_converter, m);
        }
        m_pc = epc.get();

        rule_set* rules = alloc(rule_set, m_ctx);
        rule_set::iterator it = source.begin(), end = source.end();
        bool change = false;
        for (; it != end; ++it) {
            change = blast(**it, *rules) || change;
        }
        if (!change) {
            dealloc(rules);
            rules = 0;
        }        
        if (pc) {
            pc = concat(pc.get(), epc.get());
        }
        return rules;        
    }

};


