/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    mbp_dt_tg.cpp

Abstract:

    Apply rules for model based projection for datatypes on a term graph

Author:

    Hari Govind V K (hgvk94) 2023-03-07

Revision History:

--*/
#include "qe/mbp/mbp_dt_tg.h"
#include "qe/mbp/mbp_qel_util.h"
#include "util/memory_manager.h"

namespace mbp {

struct mbp_dt_tg::impl {
    ast_manager &m;
    datatype_util m_dt_util;
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

    bool is_var(expr *t) { return is_uninterp_const(t) && has_var(t); }

    bool has_var(expr *t) { return contains_vars(t, m_vars_set, m); }

    bool is_constructor(expr *t) {
        return is_app(t) && m_dt_util.is_constructor(to_app(t)->get_decl()) &&
               has_var(t);
    }

    bool is_constructor_app(expr *e, expr *&cons, expr *&rhs) {
        if (!m.is_eq(e, cons, rhs)) return false;
        // TODO: does it matter whether vars in cons appear in rhs?
        if (is_constructor(cons)) {
            return true;
        } else if (is_constructor(rhs)) {
            cons = rhs;
            rhs = to_app(e)->get_arg(0);
            return true;
        }
        return false;
    }

    impl(ast_manager &man, mbp::term_graph &tg, model &mdl,
         obj_hashtable<app> &vars_set, expr_sparse_mark &seen)
        : m(man), m_dt_util(m), m_tg(tg), m_mdl(mdl), m_vars_set(vars_set),
          m_new_vars(m), m_seen(seen), terms(m), m_use_mdl(false) {}

    // rewrite head(x) with y
    // and x with list(y, z)
    void rm_accessor(expr *term) {
        SASSERT(is_app(term) &&
                m_dt_util.is_accessor(to_app(term)->get_decl()) &&
                has_var(to_app(term)->get_arg(0)));
        TRACE("mbp_tg", tout << "applying rm_accessor on " << expr_ref(term, m););
        expr *v = to_app(term)->get_arg(0);
        expr_ref sel(m);
        app_ref u(m);
        app_ref_vector new_vars(m);
        func_decl *cons =
            m_dt_util.get_accessor_constructor(to_app(term)->get_decl());
        ptr_vector<func_decl> const *accessors =
            m_dt_util.get_constructor_accessors(cons);
        for (unsigned i = 0; i < accessors->size(); i++) {
            func_decl *d = accessors->get(i);
            sel = m.mk_app(d, v);
            u = m_tg.get_const_in_class(sel);
            if (u) {
                new_vars.push_back(u);
                continue;
            }
            u = new_var(d->get_range(), m);
            m_new_vars.push_back(u);
            m_tg.add_var(u);
            new_vars.push_back(u);
            m_tg.add_eq(sel, u);
            m_mdl.register_decl(u->get_decl(), m_mdl(sel));
        }
        expr_ref new_cons(m.mk_app(cons, new_vars), m);
        m_tg.add_eq(v, new_cons);
    }

    // rewrite cons(v, u) = x with v = head(x) and u = tail(x)
    // where u or v contain variables
    void deconstruct_eq(expr *cons, expr *rhs) {
        TRACE("mbp_tg",
              tout << "applying deconstruct_eq on " << expr_ref(cons, m););
        ptr_vector<func_decl> const *accessors =
            m_dt_util.get_constructor_accessors(to_app(cons)->get_decl());
        for (unsigned i = 0; i < accessors->size(); i++) {
            expr_ref a(m.mk_app(accessors->get(i), rhs), m);
            expr *newRhs = to_app(cons)->get_arg(i);
            m_tg.add_eq(a, newRhs);
        }
        func_decl *is_cons =
            m_dt_util.get_constructor_recognizer(to_app(cons)->get_decl());
        expr_ref is(m.mk_app(is_cons, rhs), m);
        m_tg.add_lit(is);
    }

    // rewrite cons(v, u) != x into one of !cons(x) or v != head(x) or u !=
    // tail(x) where u or v contain variables
    void deconstruct_neq(expr *cons, expr *rhs) {
        TRACE("mbp_tg",
              tout << "applying deconstruct_neq on " << expr_ref(cons, m););
        ptr_vector<func_decl> const *accessors =
            m_dt_util.get_constructor_accessors(to_app(cons)->get_decl());
        func_decl *is_cons =
            m_dt_util.get_constructor_recognizer(to_app(cons)->get_decl());
        expr_ref a(m.mk_app(is_cons, rhs), m);
        if (m_mdl.is_false(a)) {
            expr_ref not_cons(m.mk_not(a), m);
            m_tg.add_lit(not_cons);
            return;
        }
        m_tg.add_lit(a);

        for (unsigned i = 0; i < accessors->size(); i++) {
            expr_ref a(m.mk_app(accessors->get(i), rhs), m);
            expr *newRhs = to_app(cons)->get_arg(i);
            if (!m_mdl.are_equal(a, newRhs)) {
                m_tg.add_deq(a, newRhs);
                break;
            }
        }
    }

    bool apply() {
        expr *cons, *rhs, *f, *term;
        bool progress = false;
        m_new_vars.reset();
        TRACE("mbp_tg", tout << "Iterating over terms of tg";);
        // Not resetting terms because get_terms calls resize on terms
        m_tg.get_terms(terms, false);
        for (unsigned i = 0; i < terms.size(); i++) {
            term = terms.get(i);
            if (is_seen(term)) continue;
            if (m_tg.is_cgr(term)) continue;
            if (is_app(term) &&
                m_dt_util.is_accessor(to_app(term)->get_decl()) &&
                has_var(to_app(term)->get_arg(0))) {
                mark_seen(term);
                progress = true;
                rm_accessor(term);
                continue;
            }
            if (is_constructor_app(term, cons, rhs)) {
                mark_seen(term);
                progress = true;
                deconstruct_eq(cons, rhs);
                continue;
            }
            if (m_use_mdl && m.is_not(term, f) &&
                is_constructor_app(f, cons, rhs)) {
                mark_seen(term);
                progress = true;
                deconstruct_neq(cons, rhs);
                continue;
            }
        }
        return progress;
    }
};

bool mbp_dt_tg::apply() { return m_impl->apply(); }
mbp_dt_tg::mbp_dt_tg(ast_manager &man, mbp::term_graph &tg, model &mdl,
                     obj_hashtable<app> &vars_set, expr_sparse_mark &seen) {
    m_impl = alloc(mbp_dt_tg::impl, man, tg, mdl, vars_set, seen);
}
void mbp_dt_tg::use_model() { m_impl->m_use_mdl = true; }
void mbp_dt_tg::get_new_vars(app_ref_vector *&t) { t = &m_impl->m_new_vars; }
family_id mbp_dt_tg::get_family_id() const {
    return m_impl->m_dt_util.get_family_id();
}
mbp_dt_tg::~mbp_dt_tg() { dealloc(m_impl); }

} // namespace mbp
