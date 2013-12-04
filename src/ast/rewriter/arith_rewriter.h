/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    arith_rewriter.h

Abstract:

    Basic rewriting rules for arithmetic

Author:

    Leonardo (leonardo) 2011-04-10

Notes:

--*/
#ifndef _ARITH_REWRITER_H_
#define _ARITH_REWRITER_H_

#include"poly_rewriter.h"
#include"arith_decl_plugin.h"

class arith_rewriter_core {
protected:
    typedef rational numeral;
    arith_util  m_util;
    bool        m_expand_power;
    bool        m_mul2power;
    bool        m_expand_tan;
    
    ast_manager & m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }
    
    bool is_numeral(expr * n) const { return m_util.is_numeral(n); }
    bool is_numeral(expr * n, numeral & r) const { return m_util.is_numeral(n, r); }
    bool is_zero(expr * n) const { return m_util.is_zero(n); }
    bool is_minus_one(expr * n) const { return m_util.is_minus_one(n); }
    void normalize(numeral & c, sort * s) {}
    app * mk_numeral(numeral const & r, sort * s) { return m_util.mk_numeral(r, s); }
    decl_kind add_decl_kind() const { return OP_ADD; }
    decl_kind mul_decl_kind() const { return OP_MUL; }
    bool use_power() const { return m_mul2power && !m_expand_power; }
    decl_kind power_decl_kind() const { return OP_POWER; }
public:
    arith_rewriter_core(ast_manager & m):m_util(m) {}
};

class arith_rewriter : public poly_rewriter<arith_rewriter_core> {
    bool m_arith_lhs;
    bool m_gcd_rounding;
    bool m_eq2ineq;
    bool m_elim_to_real;
    bool m_push_to_real;
    bool m_anum_simp;
    bool m_elim_rem;
    unsigned m_max_degree;

    void get_coeffs_gcd(expr * t, numeral & g, bool & first, unsigned & num_consts);
    enum const_treatment { CT_FLOOR, CT_CEIL, CT_FALSE };
    bool div_polynomial(expr * t, numeral const & g, const_treatment ct, expr_ref & result);
    enum op_kind { LE, GE, EQ };
    static op_kind inv(op_kind k) { return k == LE ? GE : (k == GE ? LE : EQ); }
    bool is_bound(expr * arg1, expr * arg2, op_kind kind, expr_ref & result);
    br_status mk_le_ge_eq_core(expr * arg1, expr * arg2, op_kind kind, expr_ref & result);

    bool elim_to_real_var(expr * var, expr_ref & new_var);
    bool elim_to_real_mon(expr * monomial, expr_ref & new_monomial);
    bool elim_to_real_pol(expr * p, expr_ref & new_p);
    bool elim_to_real(expr * arg1, expr * arg2, expr_ref & new_arg1, expr_ref & new_arg2);

    void updt_local_params(params_ref const & p);

    bool is_anum_simp_target(unsigned num_args, expr * const * args);

    br_status mk_div_irrat_rat(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_div_rat_irrat(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_div_irrat_irrat(expr * arg1, expr * arg2, expr_ref & result);
    
    bool is_reduce_power_target(expr * arg, bool is_eq);
    expr * reduce_power(expr * arg, bool is_eq);
    br_status reduce_power(expr * arg1, expr * arg2, op_kind kind, expr_ref & result);

    bool is_pi_multiple(expr * t, rational & k);
    bool is_pi_offset(expr * t, rational & k, expr * & m);
    bool is_2_pi_integer(expr * t);
    bool is_2_pi_integer_offset(expr * t, expr * & m);
    bool is_pi_integer(expr * t);
    bool is_pi_integer_offset(expr * t, expr * & m);
    expr * mk_sin_value(rational const & k);
    app * mk_sqrt(rational const & k);

public:
    arith_rewriter(ast_manager & m, params_ref const & p = params_ref()):
        poly_rewriter<arith_rewriter_core>(m, p) {
        updt_local_params(p);
    }

    void updt_params(params_ref const & p);

    static void get_param_descrs(param_descrs & r);

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    void mk_app(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
        if (mk_app_core(f, num_args, args, result) == BR_FAILED)
            result = m().mk_app(f, num_args, args);
    }

    br_status mk_eq_core(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_le_core(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_lt_core(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_ge_core(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_gt_core(expr * arg1, expr * arg2, expr_ref & result);

    br_status mk_add_core(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_mul_core(unsigned num_args, expr * const * args, expr_ref & result);

    void mk_eq(expr * arg1, expr * arg2, expr_ref & result) {
        if (mk_eq_core(arg1, arg2, result) == BR_FAILED)
            result = m_util.mk_eq(arg1, arg2);
    }
    void mk_le(expr * arg1, expr * arg2, expr_ref & result) {
        if (mk_le_core(arg1, arg2, result) == BR_FAILED)
            result = m_util.mk_le(arg1, arg2);
    }
    void mk_lt(expr * arg1, expr * arg2, expr_ref & result) { mk_lt_core(arg1, arg2, result); }
    void mk_ge(expr * arg1, expr * arg2, expr_ref & result) {
        if (mk_ge_core(arg1, arg2, result) == BR_FAILED)
            result = m_util.mk_ge(arg1, arg2);
    }
    void mk_gt(expr * arg1, expr * arg2, expr_ref & result) { mk_gt_core(arg1, arg2, result); }

    br_status mk_abs_core(expr * arg, expr_ref & result);

    br_status mk_div_core(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_idiv_core(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_mod_core(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_rem_core(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_power_core(expr* arg1, expr* arg2, expr_ref & result);
    void mk_div(expr * arg1, expr * arg2, expr_ref & result) {
        if (mk_div_core(arg1, arg2, result) == BR_FAILED)
            result = m().mk_app(get_fid(), OP_DIV, arg1, arg2);
    }
    void mk_idiv(expr * arg1, expr * arg2, expr_ref & result) {
        if (mk_idiv_core(arg1, arg2, result) == BR_FAILED)
            result = m().mk_app(get_fid(), OP_IDIV, arg1, arg2);
    }
    void mk_mod(expr * arg1, expr * arg2, expr_ref & result) {
        if (mk_mod_core(arg1, arg2, result) == BR_FAILED)
            result = m().mk_app(get_fid(), OP_MOD, arg1, arg2);
    }
    void mk_rem(expr * arg1, expr * arg2, expr_ref & result) {
        if (mk_rem_core(arg1, arg2, result) == BR_FAILED)
            result = m().mk_app(get_fid(), OP_REM, arg1, arg2);
    }
    
    br_status mk_to_int_core(expr * arg, expr_ref & result);
    br_status mk_to_real_core(expr * arg, expr_ref & result);
    void mk_to_int(expr * arg, expr_ref & result) { 
        if (mk_to_int_core(arg, result) == BR_FAILED)
            result = m().mk_app(get_fid(), OP_TO_INT, 1, &arg); 
    }
    void mk_to_real(expr * arg, expr_ref & result) { 
        if (mk_to_real_core(arg, result) == BR_FAILED)  
            result = m().mk_app(get_fid(), OP_TO_REAL, 1, &arg); 
    }
    br_status mk_is_int(expr * arg, expr_ref & result);

    void set_cancel(bool f);

    br_status mk_sin_core(expr * arg, expr_ref & result);
    br_status mk_cos_core(expr * arg, expr_ref & result);
    br_status mk_tan_core(expr * arg, expr_ref & result);

    br_status mk_asin_core(expr * arg, expr_ref & result);
    br_status mk_acos_core(expr * arg, expr_ref & result);
    br_status mk_atan_core(expr * arg, expr_ref & result);

    br_status mk_sinh_core(expr * arg, expr_ref & result);
    br_status mk_cosh_core(expr * arg, expr_ref & result);
    br_status mk_tanh_core(expr * arg, expr_ref & result);
};

#endif
