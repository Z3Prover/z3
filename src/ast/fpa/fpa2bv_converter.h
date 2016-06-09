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
#include"array_decl_plugin.h"
#include"datatype_decl_plugin.h"
#include"dl_decl_plugin.h"
#include"pb_decl_plugin.h"
#include"seq_decl_plugin.h"
#include"basic_simplifier_plugin.h"

class fpa2bv_converter {
public:
    typedef obj_map<func_decl, std::pair<app *, app *> > special_t;
    typedef obj_map<func_decl, expr*> const2bv_t;
    typedef obj_map<func_decl, func_decl*> uf2bvuf_t;

protected:
    ast_manager              & m;
    basic_simplifier_plugin    m_simp;
    fpa_util                   m_util;
    bv_util                    m_bv_util;
    arith_util                 m_arith_util;
    array_util                 m_array_util;
    datatype_util              m_dt_util;
    seq_util                   m_seq_util;
    mpf_manager              & m_mpf_manager;
    unsynch_mpz_manager      & m_mpz_manager;
    fpa_decl_plugin          * m_plugin;
    bool                       m_hi_fp_unspecified;

    const2bv_t                 m_const2bv;
    const2bv_t                 m_rm_const2bv;
    uf2bvuf_t                  m_uf2bvuf;
    special_t                  m_min_max_specials;

    friend class fpa2bv_model_converter;

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
    
    void mk_fp(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    
    void split_fp(expr * e, expr * & sgn, expr * & exp, expr * & sig) const;
    void split_fp(expr * e, expr_ref & sgn, expr_ref & exp, expr_ref & sig) const;

    void mk_eq(expr * a, expr * b, expr_ref & result);
    void mk_ite(expr * c, expr * t, expr * f, expr_ref & result);
    void mk_distinct(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    void mk_rounding_mode(decl_kind k, expr_ref & result);
    void mk_numeral(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_numeral(sort * s, mpf const & v, expr_ref & result);
    virtual void mk_const(func_decl * f, expr_ref & result);
    virtual void mk_rm_const(func_decl * f, expr_ref & result);
    virtual void mk_function(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
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
    void mk_fma(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_sqrt(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_round_to_integral(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_abs(sort * s, expr_ref & x, expr_ref & result);

    void mk_float_eq(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_lt(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_gt(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_le(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_ge(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_eq(sort * s, expr_ref & x, expr_ref & y, expr_ref & result);
    void mk_float_lt(sort * s, expr_ref & x, expr_ref & y, expr_ref & result);
    void mk_float_gt(sort *, expr_ref & x, expr_ref & y, expr_ref & result);
    void mk_float_le(sort * s, expr_ref & x, expr_ref & y, expr_ref & result);
    void mk_float_ge(sort * s, expr_ref & x, expr_ref & y, expr_ref & result);

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

    void mk_min(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_min_i(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    virtual expr_ref mk_min_max_unspecified(func_decl * f, expr * x, expr * y);

    void mk_max(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_max_i(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    expr_ref mk_to_ubv_unspecified(unsigned ebits, unsigned sbits, unsigned width);
    expr_ref mk_to_sbv_unspecified(unsigned ebits, unsigned sbits, unsigned width);
    expr_ref mk_to_real_unspecified(unsigned ebits, unsigned sbits);
    expr_ref mk_to_ieee_bv_unspecified(unsigned ebits, unsigned sbits);

    void reset(void);

    void dbg_decouple(const char * prefix, expr_ref & e);
    expr_ref_vector m_extra_assertions;
    
    special_t const & get_min_max_specials() const { return m_min_max_specials; };
    const2bv_t const & get_const2bv() const { return m_const2bv; };
    const2bv_t const & get_rm_const2bv() const { return m_rm_const2bv; };
    uf2bvuf_t const & get_uf2bvuf() const { return m_uf2bvuf; };

protected:
    void mk_one(func_decl *f, expr_ref & sign, expr_ref & result);

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

    void add_core(unsigned sbits, unsigned ebits,
        expr_ref & c_sgn, expr_ref & c_sig, expr_ref & c_exp, expr_ref & d_sgn, expr_ref & d_sig, expr_ref & d_exp,
        expr_ref & res_sgn, expr_ref & res_sig, expr_ref & res_exp);

    app * mk_fresh_const(char const * prefix, unsigned sz);

    void mk_to_bv(func_decl * f, unsigned num, expr * const * args, bool is_signed, expr_ref & result);

    sort_ref replace_float_sorts(sort * s);
    func_decl_ref replace_function(func_decl * f);
    expr_ref replace_float_arg(expr * a);
    void mk_function_output(sort * rng, func_decl * fbv, expr * const * new_args, expr_ref & result);
    func_decl * get_bv_uf(func_decl * f, sort * bv_rng, unsigned arity);

private:
    void mk_nan(sort * s, expr_ref & result);
    void mk_nzero(sort * s, expr_ref & result);
    void mk_pzero(sort * s, expr_ref & result);
    void mk_zero(sort * s, expr_ref & sgn, expr_ref & result);
    void mk_ninf(sort * s, expr_ref & result);
    void mk_pinf(sort * s, expr_ref & result);

    void mk_one(sort * s, expr_ref & sign, expr_ref & result);
    void mk_neg(sort * s, expr_ref & x, expr_ref & result);
    void mk_add(sort * s, expr_ref & bv_rm, expr_ref & x, expr_ref & y, expr_ref & result);
    void mk_sub(sort * s, expr_ref & bv_rm, expr_ref & x, expr_ref & y, expr_ref & result);
    void mk_mul(sort * s, expr_ref & bv_rm, expr_ref & x, expr_ref & y, expr_ref & result);
    void mk_div(sort * s, expr_ref & bv_rm, expr_ref & x, expr_ref & y, expr_ref & result);
    void mk_rem(sort * s, expr_ref & x, expr_ref & y, expr_ref & result);
    void mk_round_to_integral(sort * s, expr_ref & rm, expr_ref & x, expr_ref & result);

    void mk_to_fp_float(sort * s, expr * rm, expr * x, expr_ref & result);
};

#endif
