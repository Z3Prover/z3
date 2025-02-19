/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    array_peq.cpp

Abstract:

  Partial equality for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2015-06-13
    Hari Govind V K

Revision History:

--*/
#include "ast/array_peq.h"

#define PARTIAL_EQ "!partial_eq"
bool is_partial_eq(const func_decl *f) {
    SASSERT(f);
    return f->get_name() == PARTIAL_EQ;
}

bool is_partial_eq(const expr *a) {
    SASSERT(a);
    return is_app(a) && is_partial_eq(to_app(a)->get_decl());
}

app_ref mk_peq(expr *e0, expr *e1, vector<expr_ref_vector> const &indices,
               ast_manager &m) {
    peq p(e0, e1, indices, m);
    return p.mk_peq();
}

app_ref peq::mk_eq(app_ref_vector &aux_consts, bool stores_on_rhs) {
    if (!m_eq) {
        expr_ref lhs(m_lhs, m), rhs(m_rhs, m);
        if (!stores_on_rhs) { std::swap(lhs, rhs); }
        // lhs = (...(store (store rhs i0 v0) i1 v1)...)
        sort *val_sort = get_array_range(lhs->get_sort());
        for (expr_ref_vector const &diff : m_diff_indices) {
            ptr_vector<expr> store_args;
            store_args.push_back(rhs);
            store_args.append(diff.size(), diff.data());
            app_ref val(m.mk_fresh_const("diff", val_sort), m);
            store_args.push_back(val);
            aux_consts.push_back(val);
            rhs = m_arr_u.mk_store(store_args);
        }
        m_eq = m.mk_eq(lhs, rhs);
    }
    return m_eq;
}

app_ref peq::mk_peq() {
    if (!m_peq) {
        ptr_vector<expr> args;
        args.push_back(m_lhs);
        args.push_back(m_rhs);
        for (auto const &v : m_diff_indices) {
            args.append(v.size(), v.data());
        }
        m_peq = m.mk_app(m_decl, args.size(), args.data());
    }
    return m_peq;
}

peq::peq(expr *lhs, expr *rhs, vector<expr_ref_vector> const &diff_indices,
         ast_manager &m)
    : m(m), m_lhs(lhs, m), m_rhs(rhs, m), m_diff_indices(diff_indices),
      m_decl(m), m_peq(m), m_eq(m), m_arr_u(m) {
    SASSERT(m_arr_u.is_array(lhs));
    SASSERT(m_arr_u.is_array(rhs));
    SASSERT(lhs->get_sort() == rhs->get_sort());
    ptr_vector<sort> sorts;
    sorts.push_back(m_lhs->get_sort());
    sorts.push_back(m_rhs->get_sort());

    for (auto const &v : diff_indices) {
        SASSERT(v.size() == get_array_arity(m_lhs->get_sort()));
        for (expr *e : v) sorts.push_back(e->get_sort());
    }
    m_decl = m.mk_func_decl(symbol(PARTIAL_EQ), sorts.size(), sorts.data(),
                            m.mk_bool_sort());
}

peq::peq(app *p, ast_manager &m)
    : m(m), m_lhs(p->get_arg(0), m), m_rhs(p->get_arg(1), m),
      m_decl(p->get_decl(), m), m_peq(p, m), m_eq(m), m_arr_u(m),
      m_name(symbol(PARTIAL_EQ)) {
    SASSERT(is_partial_eq(p));

    SASSERT(m_arr_u.is_array(m_lhs));
    SASSERT(m_arr_u.is_array(m_rhs));
    SASSERT(m_lhs->get_sort() == m_rhs->get_sort());
    unsigned arity = get_array_arity(m_lhs->get_sort());
    for (unsigned i = 2; i < p->get_num_args(); i += arity) {
        SASSERT(arity + i <= p->get_num_args());
        expr_ref_vector vec(m);
        vec.append(arity, p->get_args() + i);
        m_diff_indices.push_back(std::move(vec));
    }
}
