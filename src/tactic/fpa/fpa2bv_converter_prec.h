/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_converter_prec.h

Abstract:

    Conversion routines for Floating Point -> Bit-Vector

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/
#ifndef _FPA2BV_CONVERTER_PREC
#define _FPA2BV_CONVERTER_PREC

#include"ast.h"
#include"obj_hashtable.h"
#include"ref_util.h"
#include"fpa_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"model_converter.h"
#include"basic_simplifier_plugin.h"
#include"fpa2bv_converter.h"

#define MAX_PRECISION 100
#define MIN_PRECISION 0

class fpa2bv_prec_model_converter;

enum fpa_approximation_mode { 
    FPAA_PRECISE,      // Always use precise encoding
    FPAA_FIXBITS,      // Approximate by fixing some bits of the encoding
    FPAA_SMALL_FLOATS  // Approximate by using smaller floats
};

#define FPAA_DEFAULT_MODE FPAA_SMALL_FLOATS

class fpa2bv_converter_prec : public fpa2bv_converter {
    fpa_approximation_mode m_mode;

    void fix_bits(unsigned prec, expr_ref rounded, unsigned sbits, unsigned ebits);//expr_ref& fixed,
    
    void mk_small_op(func_decl * f, unsigned prec, unsigned num, expr * const * args, func_decl_ref & small_op, expr_ref_vector & cast_args);
    void mk_small_op(func_decl * f, unsigned new_ebits, unsigned new_sbits, unsigned num, expr * const * args, func_decl_ref & small_op, expr_ref_vector & cast_args);
    void mk_cast_small_to_big(func_decl * big_fd, expr * arg, expr_ref & result);
    void mk_cast_small_to_big(unsigned sbits, unsigned ebits, expr * arg, expr_ref & result);
    void match_sorts(expr * a, expr * b, expr_ref & n_a, expr_ref & n_b);
    void establish_sort(unsigned num, expr * const * args, unsigned & ebits, unsigned & sbits);
public:
    fpa2bv_converter_prec(ast_manager & m, fpa_approximation_mode mode);    

    void mk_const(func_decl * f, unsigned prec, expr_ref & result);

    void mk_eq(expr * a, expr * b, expr_ref & result);
    void mk_ite(expr * c, expr * t, expr * f, expr_ref & result);    

    void mk_add(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_sub(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_uminus(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_mul(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_div(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_remainder(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_abs(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_min(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_max(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_fusedma(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_sqrt(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_round_to_integral(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);

    void mk_float_eq(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_lt(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_gt(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_le(func_decl * f, unsigned num, expr * const * args, expr_ref & result);
    void mk_float_ge(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    /*
    void mk_is_zero(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_nzero(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_pzero(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_sign_minus(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_nan(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_inf(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_normal(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
    void mk_is_subnormal(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
	*/



    void reset() {
        dec_ref_map_key_values(m, m_const2bv);
        dec_ref_map_key_values(m, m_rm_const2bv);
    }
};



#endif
