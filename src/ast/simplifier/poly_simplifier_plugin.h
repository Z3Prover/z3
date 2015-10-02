/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    poly_simplifier_plugin.h

Abstract:

    Abstract class for families that have polynomials.

Author:

    Leonardo (leonardo) 2008-01-08
    
--*/
#ifndef POLY_SIMPLIFIER_PLUGIN_H_
#define POLY_SIMPLIFIER_PLUGIN_H_

#include "simplifier_plugin.h"

/**
   \brief Abstract class that provides simplification functions for polynomials.
*/
class poly_simplifier_plugin : public simplifier_plugin {
protected:
    typedef rational numeral;
    decl_kind          m_ADD;
    decl_kind          m_MUL;
    decl_kind          m_SUB;
    decl_kind          m_UMINUS;
    decl_kind          m_NUM;
    sort *             m_curr_sort;
    expr *             m_curr_sort_zero;

    expr * mk_add(unsigned num_args, expr * const * args);
    expr * mk_add(expr * arg1, expr * arg2) { expr * args[2] = { arg1, arg2 }; return mk_add(2, args); }
    expr * mk_mul(unsigned num_args, expr * const * args);
    expr * mk_mul(expr * arg1, expr * arg2) { expr * args[2] = { arg1, arg2 }; return mk_mul(2, args); }
    expr * mk_sub(unsigned num_args, expr * const * args) { return m_manager.mk_app(m_fid, m_SUB, num_args, args); }
    expr * mk_uminus(expr * arg) { return m_manager.mk_app(m_fid, m_UMINUS, arg); }

    void process_monomial(unsigned num_args, expr * const * args, numeral & k, ptr_buffer<expr> & result);
    void mk_monomial(unsigned num_args, expr * * args, expr_ref & result);
    bool eq_monomials_modulo_k(expr * n1, expr * n2);
    bool merge_monomials(bool inv, expr * n1, expr * n2, expr_ref & result);
    template<bool Inv>
    void add_monomial_core(expr * n, expr_ref_vector & result);
    void add_monomial(bool inv, expr * n, expr_ref_vector & result);
    template<bool Inv>
    void process_sum_of_monomials_core(expr * n, expr_ref_vector & result);
    void process_sum_of_monomials(bool inv, expr * n, expr_ref_vector & result);
    void process_sum_of_monomials(bool inv, expr * n, expr_ref_vector & result, numeral & k);
    void mk_sum_of_monomials(expr_ref_vector & monomials, expr_ref & result);
    template<bool Inv>
    void mk_add_core_core(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_add_core(bool inv, unsigned num_args, expr * const * args, expr_ref & result);
    void append_to_monomial(expr * n, numeral & k, ptr_buffer<expr> & result);
    expr * mk_mul(numeral const & c, expr * body);
    void mk_sum_of_monomials_core(unsigned sz, expr ** ms, expr_ref & result);
    bool is_simple_sum_of_monomials(expr_ref_vector & monomials);
    bool is_simple_monomial(expr * m, expr * & x);

public:
    poly_simplifier_plugin(symbol const & fname, ast_manager & m, decl_kind add, decl_kind mul, decl_kind uminus, decl_kind sub, decl_kind num);
    virtual ~poly_simplifier_plugin() {}

    /** 
        \brief Return true if the given expression is a numeral, and store its value in \c val.
    */
    virtual bool is_numeral(expr * n, numeral & val) const = 0;
    bool is_numeral(expr * n) const { return is_app_of(n, m_fid, m_NUM); }
    bool is_zero(expr * n) const { 
        SASSERT(m_curr_sort_zero != 0);
        SASSERT(m_manager.get_sort(n) == m_manager.get_sort(m_curr_sort_zero)); 
        return n == m_curr_sort_zero; 
    }
    bool is_zero_safe(expr * n) {
        set_curr_sort(m_manager.get_sort(n));
        return is_zero(n);
    }
    virtual bool is_minus_one(expr * n) const = 0;
    virtual expr * get_zero(sort * s) const = 0;
    

    /**
       \brief Return true if n is of the form (* -1 r)
    */
    bool is_times_minus_one(expr * n, expr * & r) const {
        if (is_mul(n) && to_app(n)->get_num_args() == 2 && is_minus_one(to_app(n)->get_arg(0))) {
            r = to_app(n)->get_arg(1);
            return true;
        }
        return false;
    }
    
    /**
       \brief Return true if n is of the form: a <= b or a >= b.
    */
    virtual bool is_le_ge(expr * n) const = 0;
    
    /**
       \brief Return a constant representing the giving numeral and sort m_curr_sort.
    */
    virtual app * mk_numeral(numeral const & n) = 0;
    app * mk_zero() { return mk_numeral(numeral::zero()); }
    app * mk_one() { return mk_numeral(numeral::one()); }
    app * mk_minus_one() { return mk_numeral(numeral::minus_one()); }
    
    /**
       \brief Normalize the given numeral with respect to m_curr_sort
    */
    virtual numeral norm(numeral const & n) = 0;

    void set_curr_sort(sort * s) { 
        if (s != m_curr_sort) { 
            // avoid virtual function call
            m_curr_sort = s; 
            m_curr_sort_zero = get_zero(m_curr_sort); 
        } 
    }
    void set_curr_sort(expr * n) { set_curr_sort(m_manager.get_sort(n)); }

    bool is_add(expr const * n) const { return is_app_of(n, m_fid, m_ADD); }
    bool is_mul(expr const * n) const { return is_app_of(n, m_fid, m_MUL); }
    void mk_add(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_add(expr * arg1, expr * arg2, expr_ref & result);
    void mk_sub(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_sub(expr * arg1, expr * arg2, expr_ref & result);
    void mk_uminus(expr * arg, expr_ref & result);
    void mk_mul(unsigned num_args, expr * const * args, expr_ref & result);
    void mk_mul(expr * arg1, expr * arg2, expr_ref & result);
    
    virtual bool reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result);

    virtual bool reduce(func_decl * f, unsigned num_args, rational const * mults, expr * const * args, expr_ref & result);
    virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
        return simplifier_plugin::reduce(f, num_args, args, result);
    }


    expr * get_monomial_body(expr * m);
    int get_monomial_body_order(expr * m);
    void get_monomial_coeff(expr * m, numeral & result);
    void inv_monomial(expr * n, expr_ref & result);

    bool is_var_plus_ground(expr * n, bool & inv, var * & v, expr_ref & t);

#ifdef Z3DEBUG
    bool wf_monomial(expr * m) const;
    bool wf_polynomial(expr * m) const;
#endif
};

#endif /* POLY_SIMPLIFIER_PLUGIN_H_ */
