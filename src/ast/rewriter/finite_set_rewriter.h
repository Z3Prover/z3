/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_rewriter.h

Abstract:

    Rewriting Simplification for finite sets

Sample rewrite rules:
    set.union s set.empty -> s
    set.intersect s set.empty -> set.empty
    set.in x (set.singleton y) -> x = y
    set.subset(x,y) -> set.intersect(x,y) = x
    set.union(x, x) -> x
    set.intersect(x, x) -> x
    set.difference(x, x) -> set.empty


Generally this module implements basic algebraic simplification rules for finite sets
where the signature is defined in finite_set_decl_plugin.h.
   
--*/
#pragma once

#include "ast/finite_set_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/params.h"

/**
   \brief Cheap rewrite rules for finite sets
*/
class finite_set_rewriter {
    friend class finite_set_rewriter_test;
    ast_manager &m;
    finite_set_util  u;
    expr_ref_vector m_pinned;
    expr_mark m_is_min;
    
    expr * min(expr *a);
    std::pair<expr *, expr *> get_min(expr *a);
    bool is_less(expr *a, expr *b);
    expr *mk_union(expr *a, expr *b);
    bool from_unique_values(expr *a);

    // Rewrite rules for set operations
    br_status mk_union(unsigned num_args, expr *const *args, expr_ref &result);
    br_status mk_intersect(unsigned num_args, expr *const *args, expr_ref &result);
    br_status mk_difference(expr *arg1, expr *arg2, expr_ref &result);
    br_status mk_subset(expr *arg1, expr *arg2, expr_ref &result);
    br_status mk_singleton(expr *arg1, expr_ref &result);
    br_status mk_in(expr *arg1, expr *arg2, expr_ref &result);
    br_status mk_size(expr *arg, expr_ref &result);

public:
    finite_set_rewriter(ast_manager & m, params_ref const & p = params_ref()):
        m(m), u(m), m_pinned(m) {
    }
    
    family_id get_fid() const { return u.get_family_id(); }
    finite_set_util& util() { return u; }

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);   

    br_status mk_eq_core(expr *a, expr *b, expr_ref &result);
};

