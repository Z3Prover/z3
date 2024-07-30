/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    mbp_basic_tg.cpp

Abstract:

    Apply rules for model based projection for basic types, on a term graph

Author:

    Hari Govind V K (hgvk94) 2023-03-07

Revision History:

--*/

#include "qe/mbp/mbp_basic_tg.h"
#include "ast/ast.h"
#include "ast/expr_functors.h"
#include "util/debug.h"
#include "util/memory_manager.h"

struct mbp_basic_tg::impl {
    ast_manager &m;
    mbp::term_graph &m_tg;
    // TODO: cache mdl evaluation eventhough we extend m_mdl
    model &m_mdl;

    // set of variables on which to apply MBP rules
    obj_hashtable<app> &m_vars_set;

    // variables created in the last iteration of MBP application
    app_ref_vector m_new_vars;

    expr_sparse_mark &m_seen;

    expr_ref_vector terms;
    bool m_use_mdl;

    void mark_seen(expr *t) { m_seen.mark(t); }
    bool is_seen(expr *t) { return m_seen.is_marked(t); }

    // Split on all ite terms, irrespective of whether
    // they contain variables/are c-ground
    bool apply() {
        std::function<bool(expr *)> should_split, is_true, is_false;
        if (!m_use_mdl) {
            should_split = [&](expr *t) { return m_tg.has_val_in_class(t); };
            is_true = [&](expr *t) {
                return m_tg.has_val_in_class(t) && m_mdl.is_true(t);
            };
            is_false = [&](expr *t) {
                return m_tg.has_val_in_class(t) && m_mdl.is_false(t);
            };
        } else {
            should_split = [](expr *t) { return true; };
            is_true = [&](expr *t) { return m_mdl.is_true(t); };
            is_false = [&](expr *t) { return m_mdl.is_false(t); };
        }

        expr *c, *th, *el;
        expr_ref nterm(m);
        bool progress = false;
        TRACE("mbp_tg", tout << "Iterating over terms of tg";);
        // Not resetting terms because get_terms calls resize on terms
        m_tg.get_terms(terms, false);
        for (expr *term : terms) {
            if (is_seen(term)) continue;
            TRACE("mbp_tg", tout << "Processing " << expr_ref(term, m) << "\n";);
            if (m.is_ite(term, c, th, el) && should_split(c)) {
                mark_seen(term);
                progress = true;
                if (m_mdl.is_true(c)) {
                    m_tg.add_lit(c);
                    m_tg.add_eq(term, th);
                } else {
                    nterm = mk_not(m, c);
                    m_tg.add_lit(nterm);
                    m_tg.add_eq(term, el);
                }
            }
            if (m.is_implies(term, c, th)) {
                if (is_true(th) || is_false(c)) {
                    mark_seen(term);
                    progress = true;
                    if (is_true(th))
                        m_tg.add_lit(th);
                    else if (is_false(c))
                        m_tg.add_lit(c);
                    m_tg.add_eq(term, m.mk_true());
                } else if (is_true(c) && is_false(th)) {
                    mark_seen(term);
                    progress = true;
                    m_tg.add_eq(term, m.mk_false());
                }
            }
            if (m.is_or(term) || m.is_and(term)) {
                bool is_or = m.is_or(term);
                app *c = to_app(term);
                bool t = is_or ? any_of(*c, is_true) : all_of(*c, is_true);
                bool f = is_or ? all_of(*c, is_false) : any_of(*c, is_false);
                if (t || f) {
                    mark_seen(term);
                    progress = true;
                    m_tg.add_eq(term, t ? m.mk_true() : m.mk_false());
                    if (f) {
                        for (auto a : *c) {
                            if (is_false(a)) {
                                m_tg.add_lit(mk_not(m, a));
                                if (!is_or) break;
                            }
                        }
                    } else {
                        for (auto a : *c) {
                            if (is_true(a)) {
                                m_tg.add_lit(a);
                                if (is_or) break;
                            }
                        }
                    }
                }
            }
            if (m_use_mdl && m.is_distinct(term)) {
                mark_seen(term);
                progress = true;
                bool eq = false;
                app *c = to_app(term);
                for (auto a1 : *c) {
                    for (auto a2 : *c) {
                        if (a1 == a2) continue;
                        expr_ref e(m.mk_eq(a1, a2), m);
                        if (m_mdl.is_true(e)) {
                            m_tg.add_eq(a1, a2);
                            eq = true;
                            break;
                        } else {
                            SASSERT(m_mdl.is_false(e));
                            m_tg.add_deq(a1, a2);
                        }
                    }
                }
                if (eq)
                    m_tg.add_eq(term, m.mk_false());
                else
                    m_tg.add_eq(term, m.mk_true());
            }
        }
        return progress;
    }

    impl(ast_manager &man, mbp::term_graph &tg, model &mdl,
         obj_hashtable<app> &vars_set, expr_sparse_mark &seen)
        : m(man), m_tg(tg), m_mdl(mdl), m_vars_set(vars_set), m_new_vars(m),
          m_seen(seen), terms(m), m_use_mdl(false) {}
};

bool mbp_basic_tg::apply() { return m_impl->apply(); }
void mbp_basic_tg::use_model() { m_impl->m_use_mdl = true; }
void mbp_basic_tg::get_new_vars(app_ref_vector *&t) { t = &m_impl->m_new_vars; }
family_id mbp_basic_tg::get_family_id() const {
    return m_impl->m.get_basic_family_id();
}
mbp_basic_tg::mbp_basic_tg(ast_manager &man, mbp::term_graph &tg, model &mdl,
                           obj_hashtable<app> &vars_set,
                           expr_sparse_mark &seen) {
    m_impl = alloc(mbp_basic_tg::impl, man, tg, mdl, vars_set, seen);
}
mbp_basic_tg::~mbp_basic_tg() { dealloc(m_impl); }
