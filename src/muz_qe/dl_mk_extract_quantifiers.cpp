/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_extract_quantifiers.cpp

Abstract:

    Remove universal quantifiers over interpreted predicates in the body.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-21

Revision History:

--*/

#include"dl_mk_extract_quantifiers.h"
#include"ast_pp.h"

namespace datalog {


    mk_extract_quantifiers::mk_extract_quantifiers(context & ctx) : 
        rule_transformer::plugin(101, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()) 
    {}

    mk_extract_quantifiers::~mk_extract_quantifiers() {
        for (unsigned i = 0; i < m_refs.size(); ++i) {
            dealloc(m_refs[i]);
        }
        m_quantifiers.reset();
        m_refs.reset();
    }


    void mk_extract_quantifiers::extract(rule& r, rule_set& new_rules) {
        expr_ref_vector tail(m);
        quantifier_ref_vector quantifiers(m);
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz = r.get_tail_size();
        for (unsigned i = 0; i < utsz; ++i) {
            tail.push_back(r.get_tail(i));
            if (r.is_neg_tail(i)) {
                new_rules.add_rule(&r);
                return;
            }
        }
        for (unsigned i = utsz; i < tsz; ++i) {
            app* t = r.get_tail(i);
            expr_ref_vector conjs(m);
            datalog::flatten_and(t, conjs);
            quantifier_ref qe(m);
            quantifier* q = 0;
            for (unsigned j = 0; j < conjs.size(); ++j) {
                expr* e = conjs[j].get();
                if (rule_manager::is_forall(m, e, q)) {
                    quantifiers.push_back(q);
                    qe = m.mk_exists(q->get_num_decls(), q->get_decl_sorts(), q->get_decl_names(), q->get_expr());
                    tail.push_back(qe);
                }
                else {
                    tail.push_back(e);
                }
            }
        }
        if (quantifiers.empty()) {
            new_rules.add_rule(&r);
        }
        else {
            expr_ref fml(m);
            rule_ref_vector rules(rm);
            fml = m.mk_implies(m.mk_and(tail.size(), tail.c_ptr()), r.get_head());
            rm.mk_rule(fml, rules, r.name());
            quantifier_ref_vector* qs = alloc(quantifier_ref_vector, quantifiers);
            m_refs.push_back(qs);
            for (unsigned i = 0; i < rules.size(); ++i) {
                m_quantifiers.insert(rules[i].get(), qs);
                new_rules.add_rule(rules[i].get());
            }
        }
    }
    
    rule_set * mk_extract_quantifiers::operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc) {
        m_quantifiers.reset();
        rule_set* rules = alloc(rule_set, m_ctx);
        rule_set::iterator it = source.begin(), end = source.end();
        for (; it != end; ++it) {
            extract(**it, *rules);
        }
        if (m_quantifiers.empty()) {
            dealloc(rules);
            rules = 0;
        }        
        return rules;        
    }

};


