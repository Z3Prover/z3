/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    array_peq.h

Abstract:

  Partial equality for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2015-06-13
    Hari Govind V K

Revision History:

--*/
#pragma once

#include "ast/array_decl_plugin.h"
#include "ast/ast.h"

/**
 * \brief utility class for partial equalities
 *
 * A partial equality (a ==I b), for two arrays a, b and a finite set of indices
 * I holds iff (forall i :: i \not\in I => a[i] == b[i]). In other words, peq is
 * a restricted form of the extensionality axiom
 *
 * Using this class, we denote (a =I b) as f(a,b,i0,i1,...),
 * where f is an uninterpreted predicate with the name PARTIAL_EQ and
 * I = {i0,i1,...}
 */

class peq {
    ast_manager &m;
    expr_ref m_lhs;
    expr_ref m_rhs;
    vector<expr_ref_vector> m_diff_indices;
    func_decl_ref m_decl; // the partial equality declaration
    app_ref m_peq;        // partial equality application
    app_ref m_eq;         // equivalent std equality using def. of partial eq
    array_util m_arr_u;
    symbol m_name;

  public:
    peq(app *p, ast_manager &m);

    peq(expr *lhs, expr *rhs, vector<expr_ref_vector> const &diff_indices,
        ast_manager &m);

    expr_ref lhs() { return m_lhs; }

    expr_ref rhs() { return m_rhs; }

    void get_diff_indices(vector<expr_ref_vector> &result) {
        result.append(m_diff_indices);
    }

    /** Convert peq into a peq expression */
    app_ref mk_peq();

    /** Convert peq into an equality

        For peq of the form (a =I b) returns (a = b[i0 := v0, i1 := v1, ...])
        where i0, i1 \in I, and v0, v1 are fresh skolem constants

        Skolems are returned in aux_consts

        The left and right hand arguments are reversed when stores_on_rhs is
       false
     */
    app_ref mk_eq(app_ref_vector &aux_consts, bool stores_on_rhs = true);
};

/**
 * mk (e0 ==indices e1)
 *
 * result has stores if either e0 or e1 or an index term has stores
 */
app_ref mk_peq(expr *e0, expr *e1, vector<expr_ref_vector> const &indices,
               ast_manager &m);

bool is_partial_eq(const func_decl *f);

bool is_partial_eq(const expr *a);

inline bool is_peq(const func_decl *f) { return is_partial_eq(f); }
inline bool is_peq(const expr *a) { return is_partial_eq(a); }
