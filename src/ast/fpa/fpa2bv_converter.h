/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_converter.h

Abstract:

    Conversion routines for Floating Point -> Bit-Vector

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/
#ifndef FPA2BV_CONVERTER_H_
#define FPA2BV_CONVERTER_H_

#include"ast.h"
#include"obj_hashtable.h"
#include"ref_util.h"
#include"fpa_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"basic_simplifier_plugin.h"

typedef enum { BV_RM_TIES_TO_EVEN, BV_RM_TIES_TO_AWAY, BV_RM_TO_POSITIVE, BV_RM_TO_NEGATIVE, BV_RM_TO_ZERO = 4 } BV_RM_VAL;

struct func_decl_triple {
        func_decl_triple () { f_sgn = 0; f_sig = 0; f_exp = 0; }
        func_decl_triple (func_decl * sgn, func_decl * sig, func_decl * exp)
        {
            f_sgn = sgn;
            f_sig = sig;
            f_exp = exp;
        }
        func_decl * f_sgn;
        func_decl * f_sig;        
        func_decl * f_exp;        
    };

class fpa2bv_converter {
protected:
    ast_manager              & m;
    basic_simplifier_plugin    m_simp;
    fpa_util                   m_util;
    bv_util                    m_bv_util;
    arith_util                 m_arith_util;
    mpf_manager              & m_mpf_manager;
    unsynch_mpz_manager      & m_mpz_manager;    
    fpa_decl_plugin          * m_plugin;
    bool                       m_hi_fp_unspecified;

    obj_map<func_decl, expr*>  m_const2bv;
    obj_map<func_decl, expr*>  m_rm_const2bv;
    obj_map<func_decl, func_decl*>  m_uf2bvuf;
    obj_hashtable<func_decl>   m_decls_to_hide;
    
public:
    fpa2bv_converter(ast_manager & m);    
    ~fpa2bv_converter();

    fpa_util & fu() { return m_util; }
    bv_util & bu() { return m_bv_util; }
    arith_util & au() { return m_arith_util; }

    bool is_float(sort * s) { return m_util.is_float(s); }
    bool is_float(expr * e) { return is_app(e) && m_util.is_float(to_app(e)->get_decl()->get_range()); }
    bool is_rm(expr * e) { return is_app(e) && m_util.is_rm(e); }
    bool is_rm(sort * s) { return m_util.is_rm(s); }
    bool is_float_family(func_decl * f) { return f->get_family_id() == m_util.get_family_id(); }

    void mk_fp(expr * sign, expr * exponent, expr * significand, expr_ref & result);
    void mk_fp(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    void split_fp(expr * e, expr * & sgn, expr * & exp, expr * & sig) const;
    void split_fp(expr * e, expr_ref & sgn, expr_ref & exp, expr_ref & sig) const;

    void mk_eq(expr * a, expr * b, expr_ref & result);
    void mk_ite(expr * c, expr * t, expr * f, expr_ref & result);
    void mk_distinct(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    void mk_rounding_mode(func_decl * f, expr_ref & result);
    void mk_numeral(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    virtual void mk_const(func_decl * f, expr_ref & result);
    virtual void mk_rm_const(func_decl * f, expr_ref & result);
    virtual void mk_uninterpreted_function(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_var(unsigned base_inx, sort * srt, expr_ref & result);

    void mk_pinf(func_decl * f, expr_ref & result);
    void mk_ninf(func_decl * f, expr_ref & result);
    void mk_nan(func_decl * f, expr_ref & result);
    void mk_nzero(func_decl *f, expr_ref & result);
    void mk_pzero(func_decl *f, expr_ref & result);    

    void mk_add(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_sub(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_neg(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_mul(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_div(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_rem(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_abs(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_min(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_max(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_fma(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_sqrt(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_round_to_integral(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    void mk_float_eq(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_lt(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_gt(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_le(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_ge(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    void mk_is_zero(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_nzero(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_pzero(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_negative(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_positive(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_nan(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_inf(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_normal(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_subnormal(func_decl * f, unsigned num, expr * const * args, expr_ref & result);    

    void mk_to_fp(func_decl * f, unsigned num, expr * const * args, expr_ref & result);    
    void mk_to_fp_float(func_decl * f, sort * s, expr * rm, expr * x, expr_ref & result);    
    void mk_to_fp_signed(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_to_fp_unsigned(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_to_ieee_bv(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_to_fp_real(func_decl * f, sort * s, expr * rm, expr * x, expr_ref & result);
    void mk_to_fp_real_int(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    void mk_to_ubv(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_to_sbv(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_to_real(func_decl * f, unsigned num, expr * const * args, expr_ref & result);    

    void set_unspecified_fp_hi(bool v) { m_hi_fp_unspecified = v; }

    virtual expr_ref mk_min_unspecified(func_decl * f, expr * x, expr * y);
    virtual expr_ref mk_max_unspecified(func_decl * f, expr * x, expr * y);

    expr_ref mk_to_ubv_unspecified(unsigned width);
    expr_ref mk_to_sbv_unspecified(unsigned width);
    expr_ref mk_to_real_unspecified();

    obj_map<func_decl, expr*> const & const2bv() const { return m_const2bv; }
    obj_map<func_decl, expr*> const & rm_const2bv() const { return m_rm_const2bv; }
    obj_map<func_decl, func_decl*> const & uf2bvuf() const { return m_uf2bvuf; }
    obj_hashtable<func_decl> const & decls_to_hide() const { return m_decls_to_hide; }

    void reset(void);

    void dbg_decouple(const char * prefix, expr_ref & e);
    expr_ref_vector m_extra_assertions;

protected:
    void mk_one(func_decl *f, expr_ref sign, expr_ref & result);

    void mk_is_nan(expr * e, expr_ref & result);
    void mk_is_inf(expr * e, expr_ref & result);
    void mk_is_pinf(expr * e, expr_ref & result);
    void mk_is_ninf(expr * e, expr_ref & result);
    void mk_is_pos(expr * e, expr_ref & result);
    void mk_is_neg(expr * e, expr_ref & result);
    void mk_is_zero(expr * e, expr_ref & result);
    void mk_is_nzero(expr * e, expr_ref & result);
    void mk_is_pzero(expr * e, expr_ref & result);
    void mk_is_denormal(expr * e, expr_ref & result);
    void mk_is_normal(expr * e, expr_ref & result);

    void mk_is_rm(expr * e, BV_RM_VAL rm, expr_ref & result);

    void mk_top_exp(unsigned sz, expr_ref & result);
    void mk_bot_exp(unsigned sz, expr_ref & result);
    void mk_min_exp(unsigned ebits, expr_ref & result);
    void mk_max_exp(unsigned ebits, expr_ref & result);

    void mk_leading_zeros(expr * e, unsigned max_bits, expr_ref & result);

    void mk_bias(expr * e, expr_ref & result);
    void mk_unbias(expr * e, expr_ref & result);

    void unpack(expr * e, expr_ref & sgn, expr_ref & sig, expr_ref & exp, expr_ref & lz, bool normalize);
    void round(sort * s, expr_ref & rm, expr_ref & sgn, expr_ref & sig, expr_ref & exp, expr_ref & result);        
    expr_ref mk_rounding_decision(expr * rm, expr * sgn, expr * last, expr * round, expr * sticky);

    void add_core(unsigned sbits, unsigned ebits, expr_ref & rm,
        expr_ref & c_sgn, expr_ref & c_sig, expr_ref & c_exp, expr_ref & d_sgn, expr_ref & d_sig, expr_ref & d_exp,
        expr_ref & res_sgn, expr_ref & res_sig, expr_ref & res_exp);

    app * mk_fresh_const(char const * prefix, unsigned sz);

    void mk_to_bv(func_decl * f, unsigned num, expr * const * args, bool is_signed, expr_ref & result);

    void mk_uninterpreted_output(sort * rng, func_decl * fbv, expr_ref_buffer & new_args, expr_ref & result);
};

#endif
