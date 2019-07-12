/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    array_rewriter.h

Abstract:

    Basic rewriting rules for Arrays.

Author:

    Leonardo (leonardo) 2011-04-06

Notes:

--*/
#ifndef ARRAY_REWRITER_H_
#define ARRAY_REWRITER_H_

#include "ast/array_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/lbool.h"
#include "util/params.h"

/**
   \brief Cheap rewrite rules for Arrays
*/
class array_rewriter {
    array_util    m_util;
    bool          m_sort_store;
    bool          m_expand_select_store;
    bool          m_expand_store_eq;
    bool          m_expand_select_ite;
    template<bool CHECK_DISEQ>
    lbool compare_args(unsigned num_args, expr * const * args1, expr * const * args2);
    void mk_eq(expr* e, expr* lhs, expr* rhs, expr_ref_vector& fmls);

    sort_ref get_map_array_sort(func_decl* f, unsigned num_args, expr* const* args);

    bool add_store(expr_ref_vector& args, unsigned num_idxs, expr* e, expr* store_val, vector<expr_ref_vector>& stores);

public:    
    array_rewriter(ast_manager & m, params_ref const & p = params_ref()):
        m_util(m) {
        updt_params(p);

    }
    ast_manager & m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }
    array_util& util() { return m_util; }

    void set_expand_select_store(bool f) { m_expand_select_store = f; }
    void set_expand_select_ite(bool f) { m_expand_select_ite = f; }
    void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    br_status mk_store_core(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_select_core(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_map_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    void mk_store(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_select(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_map(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    bool has_index_set(expr* e, expr_ref& e0, vector<expr_ref_vector>& indices);


    // The following methods never return BR_FAILED
    br_status mk_set_union(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_set_intersect(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_set_complement(expr * arg, expr_ref & result);
    br_status mk_set_difference(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_set_subset(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_eq_core(expr * lhs, expr * rhs, expr_ref & result);

    expr_ref mk_set_difference(expr* a, expr* b) {
        expr_ref result(m());
        mk_set_difference(a, b, result);
        return result;
    }

    expr_ref mk_set_intersect(expr* a, expr* b) {
        expr_ref result(m());
        expr* args[2] = { a, b };
        mk_set_intersect(2, args, result);
        return result;
    }

};

#endif
