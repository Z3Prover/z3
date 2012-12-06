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

    app_ref mk_extract_quantifiers::ensure_app(expr* e) {
        if (is_app(e)) {
            return app_ref(to_app(e), m);
        }
        else {
            return app_ref(m.mk_eq(e, m.mk_true()), m);
        }
    }

    void mk_extract_quantifiers::ensure_predicate(expr* e, unsigned& max_var, app_ref_vector& tail) {
        SASSERT(is_app(e));
        SASSERT(to_app(e)->get_decl()->get_family_id() == null_family_id);
        app* a = to_app(e);
        expr_ref_vector args(m);        
        for (unsigned i = 0; i < a->get_num_args(); ++i) {
            expr* arg = a->get_arg(i);
            if (is_var(arg) || m.is_value(arg)) {
                args.push_back(arg);
            }
            else {
                expr_ref new_var(m);
                new_var = m.mk_var(++max_var, m.get_sort(arg));
                args.push_back(new_var);
                tail.push_back(m.mk_eq(new_var, arg));
            }
        }
        tail.push_back(m.mk_app(a->get_decl(), args.size(), args.c_ptr()));
    }


    void mk_extract_quantifiers::extract(rule& r, rule_set& new_rules) {
        app_ref_vector tail(m);
        quantifier_ref_vector quantifiers(m);
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz = r.get_tail_size();
        var_counter vc(true);
        unsigned max_var = vc.get_max_var(r);
        for (unsigned i = 0; i < utsz; ++i) {
            tail.push_back(r.get_tail(i));
            if (r.is_neg_tail(i)) {
                new_rules.add_rule(&r);
                return;
            }
        }
        var_subst vs(m, true);
        for (unsigned i = utsz; i < tsz; ++i) {
            app* t = r.get_tail(i);
            expr_ref_vector conjs(m);
            datalog::flatten_and(t, conjs);
            expr_ref qe(m);
            quantifier* q = 0;
            for (unsigned j = 0; j < conjs.size(); ++j) {
                expr* e = conjs[j].get();
                if (rule_manager::is_forall(m, e, q)) {
                    quantifiers.push_back(q);
                    expr_ref_vector sub(m);
                    ptr_vector<sort> fv;
                    unsigned num_decls = q->get_num_decls();
                    get_free_vars(q, fv);
                    for (unsigned k = 0; k < fv.size(); ++k) {
                        unsigned idx = fv.size()-k-1;
                        if (!fv[idx]) {
                            fv[idx] = m.mk_bool_sort();
                        }
                        sub.push_back(m.mk_var(idx, fv[idx]));
                    }
                    for (unsigned k = 0; k < num_decls; ++k) {
                        sub.push_back(m.mk_var(num_decls+max_var-k, q->get_decl_sort(k)));
                    }
                    max_var += num_decls;                    
                    vs(q->get_expr(), sub.size(), sub.c_ptr(), qe);
                    ensure_predicate(qe, max_var, tail);
                }
                else {
                    tail.push_back(ensure_app(e));
                }
            }
        }
        if (quantifiers.empty()) {
            new_rules.add_rule(&r);
        }
        else {
            rule_ref new_rule(rm);
            TRACE("dl", 
                  tout << mk_pp(r.get_head(), m) << " :- \n";
                  for (unsigned i = 0; i < tail.size(); ++i) {
                      tout << "  " << mk_pp(tail[i].get(), m) << "\n";
                  });
            new_rule = rm.mk(r.get_head(), tail.size(), tail.c_ptr(), 0, r.name(), false);
            quantifier_ref_vector* qs = alloc(quantifier_ref_vector, quantifiers);
            m_refs.push_back(qs);
            new_rules.add_rule(new_rule);
            m_quantifiers.insert(new_rule, qs);
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


