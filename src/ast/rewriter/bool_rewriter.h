/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bool_rewriter.h

Abstract:

    Basic rewriting rules for Boolean operators.

Author:

    Leonardo (leonardo) 2011-04-04

Notes:

--*/
#ifndef BOOL_REWRITER_H_
#define BOOL_REWRITER_H_

#include"ast.h"
#include"rewriter.h"
#include"params.h"

/**
   \brief Apply basic Boolean rewriting operations.

   Only depth 1 simplifications are performed.

   Note: there are no recursive calls. 

   Note: arguments of AC operators are not sorted.
   Note: arguments of = and xor are also not sorted.
   
   Note: By default, (AND A B) is not rewritten as (NOT (OR (NOT A) (NOT B)))

   Note: AND OR operators are flattened only if mk_flat_app, mk_flat_or, mk_flat_and are used.
   
   The following operators are expanded:
   - => (implies)
   - xor
   - nand
   - nor
   - iff    
   
   All methods run in time almost linear on the number of arguments.
   Actually, this is not true when flattening is enabled.
   A better approximation is O(Sum_{t \in args} size1(t)).
   Where size1(t) = max{t->get_num_args(), 1}.
*/
class bool_rewriter {
    ast_manager &  m_manager;
    bool           m_flat;
    bool           m_local_ctx;
    bool           m_elim_and;
    bool           m_blast_distinct;
    unsigned       m_blast_distinct_threshold;
    bool           m_ite_extra_rules;
    unsigned       m_local_ctx_limit;
    unsigned       m_local_ctx_cost;

    br_status mk_flat_and_core(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_flat_or_core(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_nflat_and_core(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_nflat_or_core(unsigned num_args, expr * const * args, expr_ref & result);

    void mk_and_as_or(unsigned num_args, expr * const * args, expr_ref & result);

    expr * mk_or_app(unsigned num_args, expr * const * args);
    bool simp_nested_not_or(unsigned num_args, expr * const * args, expr_fast_mark1 & neg_lits, expr_fast_mark2 & pos_lits, expr_ref & result);
    expr * simp_arg(expr * arg, expr_fast_mark1 & neg_lits, expr_fast_mark2 & pos_lits, bool & modified);
    void mk_nested_ite(expr * new_c, expr * new_t, expr * new_e, expr_ref & result);
    bool simp_nested_eq_ite(expr * t, expr_fast_mark1 & neg_lits, expr_fast_mark2 & pos_lits, expr_ref & result);
    bool local_ctx_simp(unsigned num_args, expr * const * args, expr_ref & result);
    br_status try_ite_value(app * ite, app * val, expr_ref & result);

public:
    bool_rewriter(ast_manager & m, params_ref const & p = params_ref()):m_manager(m), m_local_ctx_cost(0) { updt_params(p); }
    ast_manager & m() const { return m_manager; }
    family_id get_fid() const { return m().get_basic_family_id(); }
    bool is_eq(expr * t) const { return m().is_eq(t) || m().is_iff(t); }
    
    bool flat() const { return m_flat; }
    void set_flat(bool f) { m_flat = f; }
    bool elim_and() const { return m_elim_and; }
    void set_elim_and(bool f) { m_elim_and = f; }
    void reset_local_ctx_cost() { m_local_ctx_cost = 0; }
    
    void updt_params(params_ref const & p);

    static void get_param_descrs(param_descrs & r);

    // The core methods return true if a rewrite-step/simplification was applied
    // to the arguments, and the result is stored in 'result'. Otherwise, they return false
    // and result.get == 0.
    
    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    void mk_app(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
        if (mk_app_core(f, num_args, args, result) == BR_FAILED)
            result = m().mk_app(f, num_args, args);
    }
    
    br_status mk_eq_core(expr * lhs, expr * rhs, expr_ref & result);
    br_status mk_distinct_core(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_iff_core(expr * lhs, expr * rhs, expr_ref & result) { return mk_eq_core(lhs, rhs, result); }
    br_status mk_and_core(unsigned num_args, expr * const * args, expr_ref & result) {
        if (m_elim_and) {
            mk_and_as_or(num_args, args, result);
            return BR_DONE;
        }
        else if (m_flat) {
            return mk_flat_and_core(num_args, args, result);
        }
        else {
            return mk_nflat_and_core(num_args, args, result);
        }
    }
    br_status mk_or_core(unsigned num_args, expr * const * args, expr_ref & result) {
        return m_flat ?
            mk_flat_or_core(num_args, args, result) :
            mk_nflat_or_core(num_args, args, result);
    }
    br_status mk_ite_core(expr * c, expr * t, expr * e, expr_ref & result);
    br_status mk_not_core(expr * t, expr_ref & result);

    void mk_eq(expr * lhs, expr * rhs, expr_ref & result) {
        if (mk_eq_core(lhs, rhs, result) == BR_FAILED)
            result = m().mk_eq(lhs, rhs);
    }
    void mk_iff(expr * lhs, expr * rhs, expr_ref & result) { mk_eq(lhs, rhs, result); }
    void mk_xor(expr * lhs, expr * rhs, expr_ref & result);
    void mk_and(unsigned num_args, expr * const * args, expr_ref & result) {
        if (mk_and_core(num_args, args, result) == BR_FAILED) {
            SASSERT(!m_elim_and);
            result = m().mk_and(num_args, args);
        }
    }
    void mk_or(unsigned num_args, expr * const * args, expr_ref & result) {
        if (mk_or_core(num_args, args, result) == BR_FAILED)
            result = m().mk_or(num_args, args);
    }
    void mk_and(expr * arg1, expr * arg2, expr_ref & result) {
        expr * args[2] = {arg1, arg2};
        mk_and(2, args, result);
    }
    void mk_or(expr * arg1, expr * arg2, expr_ref & result) {
        expr * args[2] = {arg1, arg2};
        mk_or(2, args, result);
    }
    void mk_and(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {
        expr * args[3] = {arg1, arg2, arg3};
        mk_and(3, args, result);
    }
    void mk_or(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {
        expr * args[3] = {arg1, arg2, arg3};
        mk_or(3, args, result);
    }
    void mk_implies(expr * lhs, expr * rhs, expr_ref & result);
    void mk_ite(expr * c, expr * t, expr * e, expr_ref & result) {
        if (mk_ite_core(c, t, e, result) == BR_FAILED)
            result = m().mk_ite(c, t, e);
    }
    void mk_distinct(unsigned num_args, expr * const * args, expr_ref & result) {
        if (mk_distinct_core(num_args, args, result) == BR_FAILED)
            result = m().mk_distinct(num_args, args);
    }
    void mk_not(expr * t, expr_ref & result) {
        if (mk_not_core(t, result) == BR_FAILED)
            result = m().mk_not(t);
    }

    void mk_nand(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_nor(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_nand(expr * arg1, expr * arg2, expr_ref & result);
    void mk_nor(expr * arg1, expr * arg2, expr_ref & result);
};

struct bool_rewriter_cfg : public default_rewriter_cfg {
    bool_rewriter m_r;
    bool flat_assoc(func_decl * f) const { return m_r.flat() && (m_r.m().is_and(f) || m_r.m().is_or(f)); }
    bool rewrite_patterns() const { return false; }
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = 0;
        if (f->get_family_id() != m_r.get_fid())
            return BR_FAILED;
        return m_r.mk_app_core(f, num, args, result);
    }
    bool_rewriter_cfg(ast_manager & m, params_ref const & p):m_r(m, p) {}
};

class bool_rewriter_star : public rewriter_tpl<bool_rewriter_cfg> {
    bool_rewriter_cfg m_cfg;
public:
    bool_rewriter_star(ast_manager & m, params_ref const & p):
        rewriter_tpl<bool_rewriter_cfg>(m, false, m_cfg),
        m_cfg(m, p) {}
};

#endif
