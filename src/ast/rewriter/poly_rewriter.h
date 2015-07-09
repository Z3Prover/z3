/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    poly_rewriter.h

Abstract:

    Basic rewriting rules for Polynomials.

Author:

    Leonardo (leonardo) 2011-04-08

Notes:

--*/
#ifndef POLY_REWRITER_H_
#define POLY_REWRITER_H_

#include"ast.h"
#include"obj_hashtable.h"
#include"rewriter_types.h"
#include"params.h"

template<typename Config>
class poly_rewriter : public Config {
protected:
    typedef typename Config::numeral numeral; 
    sort *   m_curr_sort;
    obj_map<expr, unsigned> m_expr2pos;
    bool                    m_flat;
    bool                    m_som;
    unsigned                m_som_blowup;
    bool                    m_sort_sums;
    bool                    m_hoist_mul;
    bool                    m_hoist_cmul;
    
    bool is_numeral(expr * n) const { return Config::is_numeral(n); }
    bool is_numeral(expr * n, numeral & r) const { return Config::is_numeral(n, r); }
    bool is_zero(expr * n) const { return Config::is_zero(n); }
    bool is_minus_one(expr * n) const { return Config::is_minus_one(n); }
    void normalize(numeral & c) { Config::normalize(c, m_curr_sort); }
    app * mk_numeral(numeral const & r) { return Config::mk_numeral(r, m_curr_sort); }
    decl_kind add_decl_kind() const { return Config::add_decl_kind(); }
    decl_kind mul_decl_kind() const { return Config::mul_decl_kind(); }
    bool use_power() const { return Config::use_power(); }
    decl_kind power_decl_kind() const { return Config::power_decl_kind(); }
    bool is_power(expr * t) const { return is_app_of(t, get_fid(), power_decl_kind()); }
    expr * get_power_body(expr * t, rational & k);
    struct mon_pw_lt; // functor used to sort monomial elements when use_power() == true

    expr * mk_mul_app(unsigned num_args, expr * const * args);
    expr * mk_mul_app(numeral const & c, expr * arg);
    expr * mk_add_app(unsigned num_args, expr * const * args);

    br_status mk_flat_mul_core(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_nflat_mul_core(unsigned num_args, expr * const * args, expr_ref & result);

    expr * get_power_product(expr * t);
    expr * get_power_product(expr * t, numeral & a);

    br_status mk_flat_add_core(unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_nflat_add_core(unsigned num_args, expr * const * args, expr_ref & result);

    void set_curr_sort(sort * s) { m_curr_sort = s; }

    expr * const * get_monomials(expr * & t, unsigned & sz) {
        if (is_add(t)) {
            sz = to_app(t)->get_num_args();
            return to_app(t)->get_args();
        }
        else {
            sz = 1;
            return &t;
        }
    }

    br_status cancel_monomials(expr * lhs, expr * rhs, bool move, expr_ref & lhs_result, expr_ref & rhs_result);

    bool hoist_multiplication(expr_ref& som);
    expr* merge_muls(expr* x, expr* y);

    struct hoist_cmul_lt;
    bool is_mul(expr * t, numeral & c, expr * & pp);
    void hoist_cmul(expr_ref_buffer & args);
    
public:
    poly_rewriter(ast_manager & m, params_ref const & p = params_ref()):
        Config(m), 
        m_curr_sort(0),
        m_sort_sums(false) {
        updt_params(p);
        SASSERT(!m_som || m_flat); // som of monomials form requires flattening to be enabled.
        SASSERT(!m_som || !m_hoist_mul); // som is mutually exclusive with hoisting multiplication.
        updt_params(p);
    }

    ast_manager & m() const { return Config::m(); }
    family_id get_fid() const { return Config::get_fid(); }

    void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);

    void set_flat(bool f) { m_flat = f; }

    void set_sort_sums(bool f) { m_sort_sums = f; }

    bool is_add(expr * n) const { return is_app_of(n, get_fid(), add_decl_kind()); }
    bool is_mul(expr * n) const { return is_app_of(n, get_fid(), mul_decl_kind()); }
    bool is_add(func_decl * f) const { return is_decl_of(f, get_fid(), add_decl_kind()); }
    bool is_mul(func_decl * f) const { return is_decl_of(f, get_fid(), mul_decl_kind()); }

    br_status mk_mul_core(unsigned num_args, expr * const * args, expr_ref & result) {
        SASSERT(num_args > 0);
        if (num_args == 1) {
            result = args[0];
            return BR_DONE;
        }
        set_curr_sort(m().get_sort(args[0]));
        return m_flat ?
            mk_flat_mul_core(num_args, args, result) :
            mk_nflat_mul_core(num_args, args, result);
    }
    br_status mk_add_core(unsigned num_args, expr * const * args, expr_ref & result) {
        SASSERT(num_args > 0);
        if (num_args == 1) {
            result = args[0];
            return BR_DONE;
        }
        set_curr_sort(m().get_sort(args[0]));
        return m_flat ?
            mk_flat_add_core(num_args, args, result) :
            mk_nflat_add_core(num_args, args, result);
    }
    void mk_add(unsigned num_args, expr * const * args, expr_ref & result) {
        if (mk_add_core(num_args, args, result) == BR_FAILED)
            result = mk_add_app(num_args, args);
    }
    void mk_add(expr* a1, expr* a2, expr_ref& result) {
        expr* args[2] = { a1, a2 };
        mk_add(2, args, result);
    }

    void mk_mul(unsigned num_args, expr * const * args, expr_ref & result) {
        if (mk_mul_core(num_args, args, result) == BR_FAILED)
            result = mk_mul_app(num_args, args);
    }
    void mk_mul(expr* a1, expr* a2, expr_ref& result) {
        expr* args[2] = { a1, a2 };
        mk_mul(2, args, result);
    }
    // The result of the following functions is never BR_FAILED
    br_status mk_uminus(expr * arg, expr_ref & result);
    br_status mk_sub(unsigned num_args, expr * const * args, expr_ref & result);
    
    void mk_sub(expr* a1, expr* a2, expr_ref& result) {
        expr* args[2] = { a1, a2 };
        mk_sub(2, args, result);
    }
};


#endif
