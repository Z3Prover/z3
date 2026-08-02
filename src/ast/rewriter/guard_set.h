/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    guard_set.h

Abstract:

    A conjunction of derivative cofactor guards over the element variable
    v0 = (:var 0), interpreted as the set of element values satisfying it.
    Two representations by element sort:
      * character sort:  the exact, compact seq::range_predicate.
      * any other sort:  the guard predicate kept symbolically and decided by a
        candidate basis -- the element values mentioned in the guards, plus one
        fresh value.  This is sound and complete for the
        {true,false,=,<=,and,or,not} grammar the derivatives emit (over a general
        element sort only equalities appear).

    Extracted from seq_monadic.cpp.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_range_collapse.h"

class guard_set {
public:
    // Cache of guard expression -> its range predicate (null value: unsupported guard).
    // Only meaningful for the character sort, and only valid while every guard_set sharing
    // it uses the same element variable v0 (v0 is hash-consed per element sort).
    typedef obj_map<expr, seq::range_predicate*> rp_cache;
    static void dealloc_cache(rp_cache& c);

private:
    ast_manager&         m;
    seq_util&            u;
    sort*                m_sort;
    expr*                m_v0;
    bool                 m_is_char;
    bool                 m_ok = true;      // false: an unsupported guard was conjoined
    rp_cache*            m_rp_cache = nullptr;
    seq::range_predicate m_rp;             // char representation
    expr_ref             m_guard;          // generic representation (conjunction over v0)

    // ---- generic path: candidate basis ----

    // element values compared to v0 by the equalities in `g`.
    void collect_consts(expr* g, ptr_vector<expr>& out) const;

    // evaluate `g` at v0 := cand ; l_undef on a construct outside the grammar.
    lbool eval_at(expr* g, expr* cand) const;

    // a value of m_sort distinct from every element of `consts`, if one can be built.
    bool mk_fresh(ptr_vector<expr> const& consts, expr_ref& out) const;

    lbool generic_eval(expr_ref* witness) const;

public:
    guard_set(ast_manager& _m, seq_util& _u, sort* elem_sort, expr* v0,
              rp_cache* cache = nullptr);

    bool ok() const { return m_ok; }

    // AND in a cofactor guard g (a Boolean over v0).
    void conjoin(expr* g);

    // l_false = empty, l_true = non-empty (sets *witness if non-null to a concrete
    // element of the set), l_undef = unknown / unsupported guard.
    lbool eval(expr_ref* witness) const;
};
