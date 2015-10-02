/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    arith_simplifier_plugin.h

Abstract:

    Simplifier for the arithmetic family.

Author:

    Leonardo (leonardo) 2008-01-08
    
--*/
#ifndef ARITH_SIMPLIFIER_PLUGIN_H_
#define ARITH_SIMPLIFIER_PLUGIN_H_

#include"basic_simplifier_plugin.h"
#include"poly_simplifier_plugin.h"
#include"arith_decl_plugin.h"
#include"arith_simplifier_params.h"

/**
   \brief Simplifier for the arith family.
*/
class arith_simplifier_plugin : public poly_simplifier_plugin {
public:
    enum op_kind {
        LE, GE, EQ
    };
protected:
    arith_simplifier_params & m_params;
    arith_util                m_util;
    basic_simplifier_plugin & m_bsimp;
    expr_ref                  m_int_zero;
    expr_ref                  m_real_zero;

    bool is_neg_poly(expr * t) const;

    template<op_kind k>
    void mk_le_ge_eq_core(expr * arg1, expr * arg2, expr_ref & result);

    void prop_mod_const(expr * e, unsigned depth, numeral const& k, expr_ref& result);

    void gcd_reduce_monomial(expr_ref_vector& monomials, numeral& k);

    void div_monomial(expr_ref_vector& monomials, numeral const& g);
    void get_monomial_gcd(expr_ref_vector& monomials, numeral& g);

public:
    arith_simplifier_plugin(ast_manager & m, basic_simplifier_plugin & b, arith_simplifier_params & p);
    ~arith_simplifier_plugin();
    arith_util & get_arith_util() { return m_util; }
    virtual numeral norm(const numeral & n) { return n; }
    virtual bool is_numeral(expr * n, rational & val) const { bool f; return m_util.is_numeral(n, val, f); }
    bool is_numeral(expr * n) const { return m_util.is_numeral(n); }
    virtual bool is_minus_one(expr * n) const { numeral tmp; return is_numeral(n, tmp) && tmp.is_minus_one(); }
    virtual expr * get_zero(sort * s) const { return m_util.is_int(s) ? m_int_zero.get() : m_real_zero.get(); }

    virtual app * mk_numeral(numeral const & n) { return m_util.mk_numeral(n, m_curr_sort->get_decl_kind() == INT_SORT); }
    app * mk_numeral(numeral const & n, bool is_int) { return m_util.mk_numeral(n, is_int); }
    bool is_int_sort(sort const * s) const { return m_util.is_int(s); }
    bool is_real_sort(sort const * s) const { return m_util.is_real(s); }
    bool is_arith_sort(sort const * s) const { return is_int_sort(s) || is_real_sort(s); }
    bool is_int(expr const * n) const { return m_util.is_int(n); }
    bool is_le(expr const * n) const { return m_util.is_le(n); }
    bool is_ge(expr const * n) const { return m_util.is_ge(n); }

    virtual bool is_le_ge(expr * n) const { return is_le(n) || is_ge(n); }
    
    void mk_le(expr * arg1, expr * arg2, expr_ref & result);
    void mk_ge(expr * arg1, expr * arg2, expr_ref & result);
    void mk_lt(expr * arg1, expr * arg2, expr_ref & result);
    void mk_gt(expr * arg1, expr * arg2, expr_ref & result);
    void mk_arith_eq(expr * arg1, expr * arg2, expr_ref & result);
    void mk_div(expr * arg1, expr * arg2, expr_ref & result);
    void mk_idiv(expr * arg1, expr * arg2, expr_ref & result);
    void mk_mod(expr * arg1, expr * arg2, expr_ref & result);
    void mk_rem(expr * arg1, expr * arg2, expr_ref & result);
    void mk_to_real(expr * arg, expr_ref & result);
    void mk_to_int(expr * arg, expr_ref & result);
    void mk_is_int(expr * arg, expr_ref & result);
    void mk_abs(expr * arg, expr_ref & result);

    virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    virtual bool reduce_eq(expr * lhs, expr * rhs, expr_ref & result);

    bool is_arith_term(expr * n) const;

    void gcd_normalize(numeral & coeff, expr_ref& term);

};

#endif /* ARITH_SIMPLIFIER_PLUGIN_H_ */
