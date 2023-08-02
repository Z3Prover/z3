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

    bool apply() {
        if (!m_use_mdl) return false;
        expr *term, *c, *th, *el;
        expr_ref nterm(m);
        bool progress = false;
        TRACE("mbp_tg", tout << "Iterating over terms of tg";);
        // Not resetting terms because get_terms calls resize on terms
        m_tg.get_terms(terms, false);
        for (unsigned i = 0; i < terms.size(); i++) {
            term = terms.get(i);
            // Unsupported operators
            SASSERT(!m.is_and(term));
            SASSERT(!m.is_or(term));
            SASSERT(!m.is_distinct(term));
            SASSERT(!m.is_implies(term));

            if (is_seen(term)) continue;
            if (m_tg.is_cgr(term)) continue;
            if (m.is_ite(term, c, th, el)) {
                mark_seen(term);
                progress = true;
                if (m_mdl.is_true(c)) {
                    m_tg.add_lit(c);
                    m_tg.add_eq(term, th);
                } else {
                    if (m.is_not(c))
                        nterm = to_app(c)->get_arg(0);
                    else
                        nterm = m.mk_not(c);
                    m_tg.add_lit(nterm);
                    m_tg.add_eq(term, el);
                }
                continue;
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
