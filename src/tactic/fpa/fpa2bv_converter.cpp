/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_converter.cpp

Abstract:

    Conversion routines for Floating Point -> Bit-Vector

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/
#include"ast_smt2_pp.h"
#include"well_sorted.h"

#include"fpa2bv_converter.h"

#define BVULT(X,Y,R) { expr_ref bvult_eq(m), bvult_not(m); m_simp.mk_eq(X, Y, bvult_eq); m_simp.mk_not(bvult_eq, bvult_not); m_simp.mk_and(m_bv_util.mk_ule(X,Y), bvult_not, R); }
#define BVSLT(X,Y,R) { expr_ref bvslt_eq(m), bvslt_not(m); m_simp.mk_eq(X, Y, bvslt_eq); m_simp.mk_not(bvslt_eq, bvslt_not); m_simp.mk_and(m_bv_util.mk_sle(X,Y), bvslt_not, R); }

fpa2bv_converter::fpa2bv_converter(ast_manager & m) : 
    m(m),
    m_simp(m),
    m_util(m),
	m_mpf_manager(m_util.fm()),
	m_mpz_manager(m_mpf_manager.mpz_manager()),
    m_bv_util(m),
    extra_assertions(m) {
    m_plugin = static_cast<float_decl_plugin*>(m.get_plugin(m.get_family_id("float")));
}

fpa2bv_converter::~fpa2bv_converter() {
    dec_ref_map_key_values(m, m_const2bv);
	dec_ref_map_key_values(m, m_rm_const2bv);
}

void fpa2bv_converter::mk_eq(expr * a, expr * b, expr_ref & result) {
    SASSERT(is_app_of(a, m_plugin->get_family_id(), OP_TO_FLOAT));
    SASSERT(is_app_of(b, m_plugin->get_family_id(), OP_TO_FLOAT));

    expr_ref sgn(m), s(m), e(m);
    m_simp.mk_eq(to_app(a)->get_arg(0), to_app(b)->get_arg(0), sgn);
    m_simp.mk_eq(to_app(a)->get_arg(1), to_app(b)->get_arg(1), s);
    m_simp.mk_eq(to_app(a)->get_arg(2), to_app(b)->get_arg(2), e);

    // The SMT FPA theory asks for _one_ NaN value, but the bit-blasting
    // has many, like IEEE754. This encoding of equality makes it look like
    // a single NaN again. 
    expr_ref both_the_same(m), a_is_nan(m), b_is_nan(m), both_are_nan(m);
    m_simp.mk_and(sgn, s, e, both_the_same);
    mk_is_nan(a, a_is_nan);
    mk_is_nan(b, b_is_nan);
    m_simp.mk_and(a_is_nan, b_is_nan, both_are_nan);
    m_simp.mk_or(both_are_nan, both_the_same, result);
}

void fpa2bv_converter::mk_ite(expr * c, expr * t, expr * f, expr_ref & result) {
    SASSERT(is_app_of(t, m_plugin->get_family_id(), OP_TO_FLOAT));
    SASSERT(is_app_of(f, m_plugin->get_family_id(), OP_TO_FLOAT));

    expr_ref sgn(m), s(m), e(m);
    m_simp.mk_ite(c, to_app(t)->get_arg(0), to_app(f)->get_arg(0), sgn);
    m_simp.mk_ite(c, to_app(t)->get_arg(1), to_app(f)->get_arg(1), s);
    m_simp.mk_ite(c, to_app(t)->get_arg(2), to_app(f)->get_arg(2), e);

    mk_triple(sgn, s, e, result);
}

void fpa2bv_converter::mk_value(func_decl * f, unsigned num, expr * const * args, expr_ref & result) { 
    SASSERT(num == 0);
    SASSERT(f->get_num_parameters() == 1);
    SASSERT(f->get_parameter(0).is_external());

    unsigned p_id = f->get_parameter(0).get_ext_id();
    mpf const & v = m_plugin->get_value(p_id);

    unsigned sbits = v.get_sbits();
    unsigned ebits = v.get_ebits();

    bool sign = m_util.fm().sgn(v);
    mpz const & sig = m_util.fm().sig(v);
    mpf_exp_t const & exp = m_util.fm().exp(v);

    if (m_util.fm().is_nan(v))
        mk_nan(f, result);
    else if (m_util.fm().is_inf(v)) {
        if (m_util.fm().sgn(v))
            mk_minus_inf(f, result);
        else
            mk_plus_inf(f, result);
    }
    else {
        expr_ref bv_sgn(m), bv_sig(m), e(m), biased_exp(m);
        bv_sgn = m_bv_util.mk_numeral( (sign) ? 1 : 0, 1);
        bv_sig = m_bv_util.mk_numeral(rational(sig), sbits-1);
        e = m_bv_util.mk_numeral(exp, ebits);

        mk_bias(e, biased_exp);

        mk_triple(bv_sgn, bv_sig, biased_exp, result);
        TRACE("fpa2bv_dbg", tout << "value of [" << sign << " " << m_mpz_manager.to_string(sig) << " " << exp << "] is " 
                                 << mk_ismt2_pp(result, m) << std::endl;);
                        
    }
}

void fpa2bv_converter::mk_const(func_decl * f, expr_ref & result) {
    SASSERT(f->get_family_id() == null_family_id);
    SASSERT(f->get_arity() == 0);
    expr * r;
    if (m_const2bv.find(f, r)) {
        result = r;
    }
    else {
        sort * srt = f->get_range();
        SASSERT(is_float(srt));
        unsigned ebits = m_util.get_ebits(srt);
        unsigned sbits = m_util.get_sbits(srt);
        
#ifdef _DEBUG
        std::string p("fpa2bv");
        std::string name = f->get_name().str();
        
        expr * sgn = m.mk_fresh_const((p + "_sgn_" + name).c_str(), m_bv_util.mk_sort(1));
        expr * s = m.mk_fresh_const((p + "_sig_" + name).c_str(), m_bv_util.mk_sort(sbits-1));
        expr * e = m.mk_fresh_const((p + "_exp_" + name).c_str(), m_bv_util.mk_sort(ebits));
#else
        expr * sgn = m.mk_fresh_const(0, m_bv_util.mk_sort(1));
        expr * s = m.mk_fresh_const(0, m_bv_util.mk_sort(sbits-1));
        expr * e = m.mk_fresh_const(0, m_bv_util.mk_sort(ebits));
#endif
        
        mk_triple(sgn, s, e, result);

        m_const2bv.insert(f, result);
        m.inc_ref(f);
        m.inc_ref(result);        
    }
}


void fpa2bv_converter::mk_rm_const(func_decl * f, expr_ref & result) {
    SASSERT(f->get_family_id() == null_family_id);
    SASSERT(f->get_arity() == 0);
    expr * r;
    if (m_rm_const2bv.find(f, r)) {
        result = r;
    }
    else {
		SASSERT(is_rm_sort(f->get_range()));

        result = m.mk_fresh_const(
            #ifdef _DEBUG
            "fpa2bv_rm"
            #else
            0
            #endif
            , m_bv_util.mk_sort(3));

        m_rm_const2bv.insert(f, result);
        m.inc_ref(f);
        m.inc_ref(result);
    }
}

void fpa2bv_converter::mk_plus_inf(func_decl * f, expr_ref & result) {
    sort * srt = f->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);
    expr_ref top_exp(m);
    mk_top_exp(ebits, top_exp);
    mk_triple(m_bv_util.mk_numeral(0, 1),
              m_bv_util.mk_numeral(0, sbits-1),
              top_exp,
              result);
}

void fpa2bv_converter::mk_minus_inf(func_decl * f, expr_ref & result) {
    sort * srt = f->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);
    expr_ref top_exp(m);
    mk_top_exp(ebits, top_exp);
    mk_triple(m_bv_util.mk_numeral(1, 1),
              m_bv_util.mk_numeral(0, sbits-1),
              top_exp,
              result);
}

void fpa2bv_converter::mk_nan(func_decl * f, expr_ref & result) {
    sort * srt = f->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);
    expr_ref top_exp(m);
    mk_top_exp(ebits, top_exp);
    mk_triple(m_bv_util.mk_numeral(0, 1),
              m_bv_util.mk_numeral(1, sbits-1),
              top_exp,
              result);
}

void fpa2bv_converter::mk_nzero(func_decl *f, expr_ref & result) {
    sort * srt = f->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);
    expr_ref bot_exp(m);
    mk_bot_exp(ebits, bot_exp);
    mk_triple(m_bv_util.mk_numeral(1, 1),
              m_bv_util.mk_numeral(0, sbits-1),
              bot_exp,
              result);
}

void fpa2bv_converter::mk_pzero(func_decl *f, expr_ref & result) {
    sort * srt = f->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);
    expr_ref bot_exp(m);
    mk_bot_exp(ebits, bot_exp);
    mk_triple(m_bv_util.mk_numeral(0, 1),
              m_bv_util.mk_numeral(0, sbits-1),
              bot_exp,
              result);
}

void fpa2bv_converter::add_core(unsigned sbits, unsigned ebits, expr_ref & rm,
    expr_ref & c_sgn, expr_ref & c_sig, expr_ref & c_exp, expr_ref & d_sgn, expr_ref & d_sig, expr_ref & d_exp,
    expr_ref & res_sgn, expr_ref & res_sig, expr_ref & res_exp)
{
    // c/d are now such that c_exp >= d_exp.

    expr_ref exp_delta(m);
    exp_delta = m_bv_util.mk_bv_sub(c_exp, d_exp);

    dbg_decouple("fpa2bv_add_exp_delta", exp_delta);

    // cap the delta
    expr_ref cap(m);
    cap = m_bv_util.mk_numeral(sbits+2, ebits);
    m_simp.mk_ite(m_bv_util.mk_ule(cap, exp_delta), cap, exp_delta, exp_delta);

    dbg_decouple("fpa2bv_add_exp_delta_capped", exp_delta);

    // Three extra bits for c/d
    c_sig = m_bv_util.mk_concat(c_sig, m_bv_util.mk_numeral(0, 3));
    d_sig = m_bv_util.mk_concat(d_sig, m_bv_util.mk_numeral(0, 3));

    SASSERT(is_well_sorted(m, c_sig));
    SASSERT(is_well_sorted(m, d_sig));

    // Alignment shift with sticky bit computation.
    expr_ref big_d_sig(m);
    big_d_sig = m_bv_util.mk_concat(d_sig, m_bv_util.mk_numeral(0, sbits+3));
    
    SASSERT(is_well_sorted(m, big_d_sig));

    expr_ref shifted_big(m), shifted_d_sig(m), sticky_raw(m), sticky(m);
    shifted_big = m_bv_util.mk_bv_lshr(big_d_sig, m_bv_util.mk_concat(m_bv_util.mk_numeral(0, (2*(sbits+3))-ebits), exp_delta));
    shifted_d_sig = m_bv_util.mk_extract((2*(sbits+3)-1), (sbits+3), shifted_big);
    SASSERT(is_well_sorted(m, shifted_d_sig));

    sticky_raw = m_bv_util.mk_extract(sbits+2, 0, shifted_big);    
    expr_ref sticky_eq(m); 
    m_simp.mk_eq(sticky_raw, m_bv_util.mk_numeral(0, sbits+3), sticky_eq);
    m_simp.mk_ite(sticky_eq, 
                  m_bv_util.mk_numeral(0, sbits+3), 
                  m_bv_util.mk_numeral(1, sbits+3),
                  sticky);    
    SASSERT(is_well_sorted(m, sticky));
    
    expr * or_args[2] = { shifted_d_sig.get(), sticky.get() };
    shifted_d_sig = m_bv_util.mk_bv_or(2, or_args);
    SASSERT(is_well_sorted(m, shifted_d_sig));

    expr_ref eq_sgn(m), neq_sgn(m);
    m_simp.mk_eq(c_sgn, d_sgn, eq_sgn);    
    
    // two extra bits for catching the overflow.
    c_sig = m_bv_util.mk_zero_extend(2, c_sig);
    shifted_d_sig = m_bv_util.mk_zero_extend(2, shifted_d_sig);

    SASSERT(m_bv_util.get_bv_size(c_sig) == sbits+5);
    SASSERT(m_bv_util.get_bv_size(shifted_d_sig) == sbits+5);

    dbg_decouple("fpa2bv_add_c_sig", c_sig);
    dbg_decouple("fpa2bv_add_shifted_d_sig", shifted_d_sig);

    expr_ref sum(m);
    m_simp.mk_ite(eq_sgn, 
                  m_bv_util.mk_bv_add(c_sig, shifted_d_sig),
                  m_bv_util.mk_bv_sub(c_sig, shifted_d_sig),                  
                  sum);

    SASSERT(is_well_sorted(m, sum));

    dbg_decouple("fpa2bv_add_sum", sum);    

    expr_ref sign_bv(m), n_sum(m);
    sign_bv = m_bv_util.mk_extract(sbits+4, sbits+4, sum);        
    n_sum = m_bv_util.mk_bv_neg(sum);

    dbg_decouple("fpa2bv_add_sign_bv", sign_bv);    
    dbg_decouple("fpa2bv_add_n_sum", n_sum);         
	
	family_id bvfid = m_bv_util.get_fid();

    expr_ref res_sgn_c1(m), res_sgn_c2(m), res_sgn_c3(m);
    res_sgn_c1 = m.mk_app(bvfid, OP_BAND, m_bv_util.mk_bv_not(c_sgn), d_sgn, sign_bv);
    res_sgn_c2 = m.mk_app(bvfid, OP_BAND, c_sgn, m_bv_util.mk_bv_not(d_sgn), m_bv_util.mk_bv_not(sign_bv));
    res_sgn_c3 = m.mk_app(bvfid, OP_BAND, c_sgn, d_sgn);
    expr * res_sgn_or_args[3] = { res_sgn_c1.get(), res_sgn_c2.get(), res_sgn_c3.get() };   
    res_sgn = m_bv_util.mk_bv_or(3, res_sgn_or_args);

    expr_ref res_sig_eq(m), sig_abs(m);
    m_simp.mk_eq(sign_bv, m_bv_util.mk_numeral(1, 1), res_sig_eq);
	m_simp.mk_ite(res_sig_eq, n_sum, sum, sig_abs);

    dbg_decouple("fpa2bv_add_sig_abs", sig_abs);

    res_sig = m_bv_util.mk_extract(sbits+3, 0, sig_abs);
    res_exp = m_bv_util.mk_sign_extend(2, c_exp); // rounder requires 2 extra bits!
}

void fpa2bv_converter::mk_add(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 3);
	
	expr_ref rm(m), x(m), y(m);
	rm = args[0];
    x = args[1];
    y = args[2];

    expr_ref nan(m), nzero(m), pzero(m);
    mk_nan(f, nan);
    mk_nzero(f, nzero); 
    mk_pzero(f, pzero);

    expr_ref x_is_nan(m), x_is_zero(m), x_is_pos(m), x_is_neg(m), x_is_inf(m);
    expr_ref y_is_nan(m), y_is_zero(m), y_is_pos(m), y_is_neg(m), y_is_inf(m);
    mk_is_nan(x, x_is_nan);
    mk_is_zero(x, x_is_zero);
    mk_is_pos(x, x_is_pos);
    mk_is_neg(x, x_is_neg);
    mk_is_inf(x, x_is_inf);
    mk_is_nan(y, y_is_nan);
    mk_is_zero(y, y_is_zero);
    mk_is_pos(y, y_is_pos);
    mk_is_neg(y, y_is_neg);
    mk_is_inf(y, y_is_inf);

    dbg_decouple("fpa2bv_add_x_is_nan", x_is_nan);
    dbg_decouple("fpa2bv_add_x_is_zero", x_is_zero);
    dbg_decouple("fpa2bv_add_x_is_pos", x_is_pos);
    dbg_decouple("fpa2bv_add_x_is_neg", x_is_neg);
    dbg_decouple("fpa2bv_add_x_is_inf", x_is_inf);
    dbg_decouple("fpa2bv_add_y_is_nan", y_is_nan);
    dbg_decouple("fpa2bv_add_y_is_zero", y_is_zero);
    dbg_decouple("fpa2bv_add_y_is_pos", y_is_pos);
    dbg_decouple("fpa2bv_add_y_is_neg", y_is_neg);
    dbg_decouple("fpa2bv_add_y_is_inf", y_is_inf);

    expr_ref c1(m), c2(m), c3(m), c4(m), c5(m), c6(m);
    expr_ref v1(m), v2(m), v3(m), v4(m), v5(m), v6(m), v7(m);
    
    m_simp.mk_or(x_is_nan, y_is_nan, c1);
    v1 = nan;
    
    mk_is_inf(x, c2);
    expr_ref nx(m), ny(m), nx_xor_ny(m), inf_xor(m);    
    mk_is_neg(x, nx);
    mk_is_neg(y, ny);
    m_simp.mk_xor(nx, ny, nx_xor_ny);
    m_simp.mk_and(y_is_inf, nx_xor_ny, inf_xor);
    mk_ite(inf_xor, nan, x, v2);
    
    mk_is_inf(y, c3);
    expr_ref xy_is_neg(m), v3_and(m);    
    m_simp.mk_xor(x_is_neg, y_is_neg, xy_is_neg);
    m_simp.mk_and(x_is_inf, xy_is_neg, v3_and);
    mk_ite(v3_and, nan, y, v3);
    
    expr_ref rm_is_to_neg(m), v4_and(m);    
    m_simp.mk_and(x_is_zero, y_is_zero, c4);
    mk_is_rm(rm, BV_RM_TO_NEGATIVE, rm_is_to_neg);
	mk_ite(rm_is_to_neg, nzero, pzero, v4);
    m_simp.mk_and(x_is_neg, y_is_neg, v4_and);
    mk_ite(v4_and, x, v4, v4);

    c5 = x_is_zero;
    v5 = y;

    c6 = y_is_zero;
    v6 = x;

    // Actual addition.
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());
    SASSERT(ebits <= sbits);

    expr_ref a_sgn(m), a_sig(m), a_exp(m), b_sgn(m), b_sig(m), b_exp(m);
    unpack(x, a_sgn, a_sig, a_exp, true);
    unpack(y, b_sgn, b_sig, b_exp, false);

    dbg_decouple("fpa2bv_add_unpack_a_sgn", a_sgn);
    dbg_decouple("fpa2bv_add_unpack_a_sig", a_sig);
    dbg_decouple("fpa2bv_add_unpack_a_exp", a_exp);
    dbg_decouple("fpa2bv_add_unpack_b_sgn", b_sgn);
    dbg_decouple("fpa2bv_add_unpack_b_sig", b_sig);
    dbg_decouple("fpa2bv_add_unpack_b_exp", b_exp);

    expr_ref swap_cond(m);
    swap_cond = m_bv_util.mk_sle(a_exp, b_exp);

    expr_ref c_sgn(m), c_sig(m), c_exp(m), d_sgn(m), d_sig(m), d_exp(m);
    m_simp.mk_ite(swap_cond, b_sgn, a_sgn, c_sgn);
    m_simp.mk_ite(swap_cond, b_sig, a_sig, c_sig); // has sbits
    m_simp.mk_ite(swap_cond, b_exp, a_exp, c_exp); // has ebits
    m_simp.mk_ite(swap_cond, a_sgn, b_sgn, d_sgn);
    m_simp.mk_ite(swap_cond, a_sig, b_sig, d_sig); // has sbits
    m_simp.mk_ite(swap_cond, a_exp, b_exp, d_exp); // has ebits    

    expr_ref res_sgn(m), res_sig(m), res_exp(m);
    add_core(sbits, ebits, rm,
             c_sgn, c_sig, c_exp, d_sgn, d_sig, d_exp, 
             res_sgn, res_sig, res_exp);

    expr_ref is_zero_sig(m);
    m_simp.mk_eq(res_sig, m_bv_util.mk_numeral(0, sbits+4), is_zero_sig);

    SASSERT(is_well_sorted(m, is_zero_sig));

    dbg_decouple("fpa2bv_add_is_zero_sig", is_zero_sig);
    
    expr_ref zero_case(m);
    mk_ite(rm_is_to_neg, nzero, pzero, zero_case);

    expr_ref rounded(m);
    round(f->get_range(), rm, res_sgn, res_sig, res_exp, rounded);

    mk_ite(is_zero_sig, zero_case, rounded, v7);
    
    mk_ite(c6, v6, v7, result);
    mk_ite(c5, v5, result, result);
    mk_ite(c4, v4, result, result);
    mk_ite(c3, v3, result, result);
    mk_ite(c2, v2, result, result);
    mk_ite(c1, v1, result, result);

    SASSERT(is_well_sorted(m, result));

    TRACE("fpa2bv_add", tout << "ADD = " << mk_ismt2_pp(result, m) << std::endl; );
}

void fpa2bv_converter::mk_sub(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 3);
    expr_ref t(m);
    mk_uminus(f, 1, &args[2], t);
    expr * nargs[3] = { args[0], args[1], t.get() };
    mk_add(f, 3, nargs, result);
}

void fpa2bv_converter::mk_uminus(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    expr * sgn, * s, * e;
    split(args[0], sgn, s, e);
    expr_ref c(m), nsgn(m);
    mk_is_nan(args[0], c);    
    nsgn = m_bv_util.mk_bv_not(sgn);    
    expr_ref r_sgn(m);
    m_simp.mk_ite(c, sgn, nsgn, r_sgn);
    mk_triple(r_sgn, s, e, result);
}

void fpa2bv_converter::mk_mul(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 3);
	
	expr_ref rm(m), x(m), y(m);
	rm = args[0];
    x = args[1];
    y = args[2];

    expr_ref nan(m), nzero(m), pzero(m), ninf(m), pinf(m);
    mk_nan(f, nan);
    mk_nzero(f, nzero); 
    mk_pzero(f, pzero);
    mk_minus_inf(f, ninf);
    mk_plus_inf(f, pinf);        

    expr_ref x_is_nan(m), x_is_zero(m), x_is_pos(m), x_is_inf(m);
    expr_ref y_is_nan(m), y_is_zero(m), y_is_pos(m), y_is_inf(m);
    mk_is_nan(x, x_is_nan);
    mk_is_zero(x, x_is_zero);
    mk_is_pos(x, x_is_pos);
    mk_is_inf(x, x_is_inf);
    mk_is_nan(y, y_is_nan);
    mk_is_zero(y, y_is_zero);
    mk_is_pos(y, y_is_pos);
    mk_is_inf(y, y_is_inf);

    dbg_decouple("fpa2bv_mul_x_is_nan", x_is_nan);
    dbg_decouple("fpa2bv_mul_x_is_zero", x_is_zero);
    dbg_decouple("fpa2bv_mul_x_is_pos", x_is_pos);
    dbg_decouple("fpa2bv_mul_x_is_inf", x_is_inf);
    dbg_decouple("fpa2bv_mul_y_is_nan", y_is_nan);
    dbg_decouple("fpa2bv_mul_y_is_zero", y_is_zero);
    dbg_decouple("fpa2bv_mul_y_is_pos", y_is_pos);
    dbg_decouple("fpa2bv_mul_y_is_inf", y_is_inf);

    expr_ref c1(m), c2(m), c3(m), c4(m), c5(m), c6(m);
    expr_ref v1(m), v2(m), v3(m), v4(m), v5(m), v6(m), v7(m);

    // (x is NaN) || (y is NaN) -> NaN
    m_simp.mk_or(x_is_nan, y_is_nan, c1);
    v1 = nan;
    
    // (x is +oo) -> if (y is 0) then NaN else inf with y's sign.
    mk_is_pinf(x, c2);
    expr_ref y_sgn_inf(m);
    mk_ite(y_is_pos, pinf, ninf, y_sgn_inf);
    mk_ite(y_is_zero, nan, y_sgn_inf, v2);
                
    // (y is +oo) -> if (x is 0) then NaN else inf with x's sign.
    mk_is_pinf(y, c3);
    expr_ref x_sgn_inf(m);
    mk_ite(x_is_pos, pinf, ninf, x_sgn_inf);
    mk_ite(x_is_zero, nan, x_sgn_inf, v3);
    
    // (x is -oo) -> if (y is 0) then NaN else inf with -y's sign.    
    mk_is_ninf(x, c4);
    expr_ref neg_y_sgn_inf(m);
    mk_ite(y_is_pos, ninf, pinf, neg_y_sgn_inf);
    mk_ite(y_is_zero, nan, neg_y_sgn_inf, v4);

    // (y is -oo) -> if (x is 0) then NaN else inf with -x's sign.    
    mk_is_ninf(y, c5);
    expr_ref neg_x_sgn_inf(m);
    mk_ite(x_is_pos, ninf, pinf, neg_x_sgn_inf);
    mk_ite(x_is_zero, nan, neg_x_sgn_inf, v5);

    // (x is 0) || (y is 0) -> x but with sign = x.sign ^ y.sign
    m_simp.mk_or(x_is_zero, y_is_zero, c6);
    expr_ref sign_xor(m);
    m_simp.mk_xor(x_is_pos, y_is_pos, sign_xor);
    mk_ite(sign_xor, nzero, pzero, v6);
        
    // else comes the actual multiplication.
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());
    SASSERT(ebits <= sbits);

    expr_ref a_sgn(m), a_sig(m), a_exp(m), b_sgn(m), b_sig(m), b_exp(m);
    unpack(x, a_sgn, a_sig, a_exp, true);
    unpack(y, b_sgn, b_sig, b_exp, true);    

    expr_ref lz_a(m), lz_b(m);
    mk_leading_zeros(a_sig, ebits+2, lz_a);
    mk_leading_zeros(b_sig, ebits+2, lz_b);

    expr_ref a_sig_ext(m), b_sig_ext(m);
    a_sig_ext = m_bv_util.mk_zero_extend(sbits, a_sig);
    b_sig_ext = m_bv_util.mk_zero_extend(sbits, b_sig);

    expr_ref a_exp_ext(m), b_exp_ext(m);
    a_exp_ext = m_bv_util.mk_sign_extend(2, a_exp);
    b_exp_ext = m_bv_util.mk_sign_extend(2, b_exp);

    expr_ref res_sgn(m), res_sig(m), res_exp(m);
    expr * signs[2] = { a_sgn, b_sgn };
    res_sgn = m_bv_util.mk_bv_xor(2, signs);

    dbg_decouple("fpa2bv_mul_res_sgn", res_sgn);

    res_exp = m_bv_util.mk_bv_sub(
                m_bv_util.mk_bv_add(a_exp_ext, b_exp_ext),
                m_bv_util.mk_bv_add(lz_a, lz_b));

    expr_ref product(m);
    product = m_bv_util.mk_bv_mul(a_sig_ext, b_sig_ext);

    dbg_decouple("fpa2bv_mul_product", product);

    SASSERT(m_bv_util.get_bv_size(product) == 2*sbits);

    expr_ref sticky(m);
    sticky = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, m_bv_util.mk_extract(sbits-4, 0, product));    
    res_sig = m_bv_util.mk_concat(m_bv_util.mk_extract(2*sbits-1, sbits-3, product), sticky);

    round(f->get_range(), rm, res_sgn, res_sig, res_exp, v7);

    // And finally, we tie them together.    
    mk_ite(c6, v6, v7, result);
    mk_ite(c5, v5, result, result);
    mk_ite(c4, v4, result, result);
    mk_ite(c3, v3, result, result);
    mk_ite(c2, v2, result, result);
    mk_ite(c1, v1, result, result);

    SASSERT(is_well_sorted(m, result));

    TRACE("fpa2bv_mul", tout << "MUL = " << mk_ismt2_pp(result, m) << std::endl; );
}

void fpa2bv_converter::mk_div(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 3);
	
	expr_ref rm(m), x(m), y(m);
	rm = args[0];
    x = args[1];
    y = args[2];

    expr_ref nan(m), nzero(m), pzero(m), ninf(m), pinf(m);
    mk_nan(f, nan);
    mk_nzero(f, nzero); 
    mk_pzero(f, pzero);
    mk_minus_inf(f, ninf);
    mk_plus_inf(f, pinf);        

    expr_ref x_is_nan(m), x_is_zero(m), x_is_pos(m), x_is_inf(m);
    expr_ref y_is_nan(m), y_is_zero(m), y_is_pos(m), y_is_inf(m);
    mk_is_nan(x, x_is_nan);
    mk_is_zero(x, x_is_zero);
    mk_is_pos(x, x_is_pos);
    mk_is_inf(x, x_is_inf);    
    mk_is_nan(y, y_is_nan);
    mk_is_zero(y, y_is_zero);
    mk_is_pos(y, y_is_pos);
    mk_is_inf(y, y_is_inf);    

    dbg_decouple("fpa2bv_div_x_is_nan", x_is_nan);
    dbg_decouple("fpa2bv_div_x_is_zero", x_is_zero);
    dbg_decouple("fpa2bv_div_x_is_pos", x_is_pos);
    dbg_decouple("fpa2bv_div_x_is_inf", x_is_inf);
    dbg_decouple("fpa2bv_div_y_is_nan", y_is_nan);
    dbg_decouple("fpa2bv_div_y_is_zero", y_is_zero);
    dbg_decouple("fpa2bv_div_y_is_pos", y_is_pos);
    dbg_decouple("fpa2bv_div_y_is_inf", y_is_inf);    

    expr_ref c1(m), c2(m), c3(m), c4(m), c5(m), c6(m);
    expr_ref v1(m), v2(m), v3(m), v4(m), v5(m), v6(m), v7(m);

    // (x is NaN) || (y is NaN) -> NaN
    m_simp.mk_or(x_is_nan, y_is_nan, c1);
    v1 = nan;
    
    // (x is +oo) -> if (y is oo) then NaN else inf with y's sign.
    mk_is_pinf(x, c2);
    expr_ref y_sgn_inf(m);
    mk_ite(y_is_pos, pinf, ninf, y_sgn_inf);
    mk_ite(y_is_inf, nan, y_sgn_inf, v2);
                
    // (y is +oo) -> if (x is oo) then NaN else 0 with sign x.sgn ^ y.sgn
    mk_is_pinf(y, c3);
    expr_ref xy_zero(m), signs_xor(m);
    m_simp.mk_xor(x_is_pos, y_is_pos, signs_xor);
    mk_ite(signs_xor, nzero, pzero, xy_zero);
    mk_ite(x_is_inf, nan, xy_zero, v3);
    
    // (x is -oo) -> if (y is oo) then NaN else inf with -y's sign.    
    mk_is_ninf(x, c4);
    expr_ref neg_y_sgn_inf(m);
    mk_ite(y_is_pos, ninf, pinf, neg_y_sgn_inf);
    mk_ite(y_is_inf, nan, neg_y_sgn_inf, v4);

    // (y is -oo) -> if (x is oo) then NaN else 0 with sign x.sgn ^ y.sgn
    mk_is_ninf(y, c5);
    mk_ite(x_is_inf, nan, xy_zero, v5);

    // (y is 0) -> if (x is 0) then NaN else inf with x's sign.
    c6 = y_is_zero;    
    expr_ref x_sgn_inf(m);
    mk_ite(x_is_pos, pinf, ninf, x_sgn_inf);
    mk_ite(x_is_zero, nan, x_sgn_inf, v6);

    // else comes the actual division.
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());
    SASSERT(ebits <= sbits);

    expr_ref a_sgn(m), a_sig(m), a_exp(m), b_sgn(m), b_sig(m), b_exp(m);
    unpack(x, a_sgn, a_sig, a_exp, true);
    unpack(y, b_sgn, b_sig, b_exp, true);
    
    unsigned extra_bits = sbits+2;
    expr_ref a_sig_ext(m), b_sig_ext(m);
    a_sig_ext = m_bv_util.mk_concat(a_sig, m_bv_util.mk_numeral(0, sbits + extra_bits));
    b_sig_ext = m_bv_util.mk_zero_extend(sbits + extra_bits, b_sig);

    expr_ref a_exp_ext(m), b_exp_ext(m);
    a_exp_ext = m_bv_util.mk_sign_extend(2, a_exp);
    b_exp_ext = m_bv_util.mk_sign_extend(2, b_exp);

    expr_ref res_sgn(m), res_sig(m), res_exp(m);
    expr * signs[2] = { a_sgn, b_sgn };
    res_sgn = m_bv_util.mk_bv_xor(2, signs);

    res_exp = m_bv_util.mk_bv_sub(a_exp_ext, b_exp_ext);        

    expr_ref quotient(m);
    quotient = m.mk_app(m_bv_util.get_fid(), OP_BUDIV, a_sig_ext, b_sig_ext);

    dbg_decouple("fpa2bv_div_quotient", quotient);

    SASSERT(m_bv_util.get_bv_size(quotient) == (sbits + sbits + extra_bits));    

    expr_ref sticky(m);
    sticky = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, m_bv_util.mk_extract(extra_bits-2, 0, quotient));
    res_sig = m_bv_util.mk_concat(m_bv_util.mk_extract(extra_bits+sbits+1, extra_bits-1, quotient), sticky);

    SASSERT(m_bv_util.get_bv_size(res_sig) == (sbits + 4));   

    round(f->get_range(), rm, res_sgn, res_sig, res_exp, v7);

    // And finally, we tie them together.    
    mk_ite(c6, v6, v7, result);
    mk_ite(c5, v5, result, result);
    mk_ite(c4, v4, result, result);
    mk_ite(c3, v3, result, result);
    mk_ite(c2, v2, result, result);
    mk_ite(c1, v1, result, result);

    SASSERT(is_well_sorted(m, result));

    TRACE("fpa2bv_div", tout << "DIV = " << mk_ismt2_pp(result, m) << std::endl; );
}

void fpa2bv_converter::mk_remainder(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
	
    // Remainder is always exact, so there is no rounding mode.
	expr_ref x(m), y(m);
    x = args[0];
    y = args[1];

    expr_ref nan(m), nzero(m), pzero(m), ninf(m), pinf(m);
    mk_nan(f, nan);
    mk_nzero(f, nzero); 
    mk_pzero(f, pzero);
    mk_minus_inf(f, ninf);
    mk_plus_inf(f, pinf);        

    expr_ref x_is_nan(m), x_is_zero(m), x_is_pos(m), x_is_inf(m);
    expr_ref y_is_nan(m), y_is_zero(m), y_is_pos(m), y_is_inf(m);
    mk_is_nan(x, x_is_nan);
    mk_is_zero(x, x_is_zero);
    mk_is_pos(x, x_is_pos);
    mk_is_inf(x, x_is_inf);    
    mk_is_nan(y, y_is_nan);
    mk_is_zero(y, y_is_zero);
    mk_is_pos(y, y_is_pos);
    mk_is_inf(y, y_is_inf);    

    dbg_decouple("fpa2bv_rem_x_is_nan", x_is_nan);
    dbg_decouple("fpa2bv_rem_x_is_zero", x_is_zero);
    dbg_decouple("fpa2bv_rem_x_is_pos", x_is_pos);
    dbg_decouple("fpa2bv_rem_x_is_inf", x_is_inf);
    dbg_decouple("fpa2bv_rem_y_is_nan", y_is_nan);
    dbg_decouple("fpa2bv_rem_y_is_zero", y_is_zero);
    dbg_decouple("fpa2bv_rem_y_is_pos", y_is_pos);
    dbg_decouple("fpa2bv_rem_y_is_inf", y_is_inf); 

    expr_ref c1(m), c2(m), c3(m), c4(m), c5(m), c6(m);
    expr_ref v1(m), v2(m), v3(m), v4(m), v5(m), v6(m), v7(m);

    // (x is NaN) || (y is NaN) -> NaN
    m_simp.mk_or(x_is_nan, y_is_nan, c1);
    v1 = nan;

    // (x is +-oo) -> NaN
    c2 = x_is_inf;
    v2 = nan;
    
    // (y is +-oo) -> x
    c3 = y_is_inf;
    v3 = x;

    // (x is 0) -> x
    c4 = x_is_zero;
    v4 = x;
    
    // (y is 0) -> NaN.
    c5 = y_is_zero;
    v5 = nan;

    // else the actual remainder.
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());    

    expr_ref a_sgn(m), a_sig(m), a_exp(m);
    expr_ref b_sgn(m), b_sig(m), b_exp(m);
    unpack(x, a_sgn, a_sig, a_exp, true);
    unpack(y, b_sgn, b_sig, b_exp, true);
    
    BVSLT(a_exp, b_exp, c6);
    v6 = x;

    // max. exponent difference is (2^ebits) - 3
    const mpz & two_to_ebits = fu().fm().m_powers2(ebits);
    mpz max_exp_diff;
    m_mpz_manager.sub(two_to_ebits, 3, max_exp_diff);
    SASSERT(m_mpz_manager.is_int64(max_exp_diff));
    SASSERT(m_mpz_manager.get_uint64(max_exp_diff) <= UINT_MAX);

    unsigned int max_exp_diff_ui = (unsigned int)m_mpz_manager.get_uint64(max_exp_diff);
    m_mpz_manager.del(max_exp_diff);

    expr_ref exp_diff(m);
    exp_diff = m_bv_util.mk_bv_sub(a_exp, b_exp);
    dbg_decouple("fpa2bv_rem_exp_diff", exp_diff);

    // CMW: This creates _huge_ bit-vectors, which is potentially sub-optimal,
    // but calculating this via rem = x - y * nearest(x/y) creates huge circuits.
    expr_ref huge_sig(m), shifted_sig(m), huge_rem(m);
    huge_sig = m_bv_util.mk_zero_extend(max_exp_diff_ui, a_sig);
    shifted_sig = m_bv_util.mk_bv_shl(huge_sig, m_bv_util.mk_zero_extend(max_exp_diff_ui + sbits - ebits, exp_diff));
    huge_rem = m_bv_util.mk_bv_urem(shifted_sig, m_bv_util.mk_zero_extend(max_exp_diff_ui, b_sig));
    dbg_decouple("fpa2bv_rem_huge_rem", huge_rem);

    expr_ref res_sgn(m), res_sig(m), res_exp(m);
    res_sgn = a_sgn;
    res_sig = m_bv_util.mk_concat(m_bv_util.mk_extract(sbits, 0, huge_rem),
                                  m_bv_util.mk_numeral(0, 3));
    res_exp = m_bv_util.mk_sign_extend(2, b_exp);
    
    expr_ref rm(m);
    rm = m_bv_util.mk_numeral(BV_RM_TIES_TO_EVEN, 3);
    round(f->get_range(), rm, res_sgn, res_sig, res_exp, v7);

    // And finally, we tie them together.        
    mk_ite(c6, v6, v7, result);
    mk_ite(c5, v5, result, result);
    mk_ite(c4, v4, result, result);
    mk_ite(c3, v3, result, result);
    mk_ite(c2, v2, result, result);
    mk_ite(c1, v1, result, result);

    SASSERT(is_well_sorted(m, result));

    TRACE("fpa2bv_rem", tout << "REM = " << mk_ismt2_pp(result, m) << std::endl; );
}

void fpa2bv_converter::mk_abs(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    expr * sgn, * s, * e;
    split(args[0], sgn, s, e);
    mk_triple(m_bv_util.mk_numeral(0, 1), s, e, result);
}

void fpa2bv_converter::mk_min(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
    
    expr * x = args[0], * y = args[1];

    expr * x_sgn, * x_sig, * x_exp;
    expr * y_sgn, * y_sig, * y_exp;
    split(x, x_sgn, x_sig, x_exp);
    split(y, y_sgn, y_sig, y_exp);

    expr_ref c1(m), c2(m), y_is_nan(m), x_is_nzero(m), y_is_zero(m), c2_and(m);
    mk_is_nan(x, c1);
    mk_is_nan(y, y_is_nan);
    mk_is_nzero(x, x_is_nzero);
    mk_is_zero(y, y_is_zero);
    m_simp.mk_and(x_is_nzero, y_is_zero, c2_and);
    m_simp.mk_or(y_is_nan, c2_and, c2);
    
    expr_ref c3(m);
    mk_float_lt(f, num, args, c3);

    expr_ref r_sgn(m), r_sig(m), r_exp(m);
    
    expr_ref c3xy(m), c2c3(m);
    m_simp.mk_ite(c3, x_sgn, y_sgn, c3xy);
    m_simp.mk_ite(c2, x_sgn, c3xy, c2c3);
    m_simp.mk_ite(c1, y_sgn, c2c3, r_sgn);

    expr_ref c3xy_sig(m), c2c3_sig(m);
    m_simp.mk_ite(c3, x_sig, y_sig, c3xy_sig);
    m_simp.mk_ite(c2, x_sig, c3xy_sig, c2c3_sig);
    m_simp.mk_ite(c1, y_sig, c2c3_sig, r_sig);

    expr_ref c3xy_exp(m), c2c3_exp(m);
    m_simp.mk_ite(c3, x_exp, y_exp, c3xy_exp);
    m_simp.mk_ite(c2, x_exp, c3xy_exp, c2c3_exp);
    m_simp.mk_ite(c1, y_exp, c2c3_exp, r_exp);

    mk_triple(r_sgn, r_sig, r_exp, result);
}

void fpa2bv_converter::mk_max(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
    
    expr * x = args[0], * y = args[1];

    expr * x_sgn, * x_sig, * x_exp;
    expr * y_sgn, * y_sig, * y_exp;
    split(x, x_sgn, x_sig, x_exp);
    split(y, y_sgn, y_sig, y_exp);

    expr_ref c1(m), c2(m), y_is_nan(m), y_is_nzero(m), x_is_zero(m), xy_is_zero(m);
    mk_is_nan(x, c1);
    mk_is_nan(y, y_is_nan);
    mk_is_nzero(y, y_is_nzero);
    mk_is_zero(x, x_is_zero);
    m_simp.mk_and(y_is_nzero, x_is_zero, xy_is_zero);
    m_simp.mk_or(y_is_nan, xy_is_zero, c2);
    
    expr_ref c3(m);
    mk_float_gt(f, num, args, c3);

    expr_ref r_sgn(m), r_sig(m), r_exp(m);
    
    expr_ref c3xy_sgn(m), c2c3_sgn(m);
    m_simp.mk_ite(c3, x_sgn, y_sgn, c3xy_sgn);
    m_simp.mk_ite(c2, x_sgn, c3xy_sgn, c2c3_sgn);
    m_simp.mk_ite(c1, y_sgn, c2c3_sgn, r_sgn);

    expr_ref c3xy_sig(m), c2c3_sig(m);
    m_simp.mk_ite(c3, x_sig, y_sig, c3xy_sig);
    m_simp.mk_ite(c2, x_sig, c3xy_sig, c2c3_sig);
    m_simp.mk_ite(c1, y_sig, c2c3_sig, r_sig);

    expr_ref c3xy_exp(m), c2c3_exp(m);
    m_simp.mk_ite(c3, x_exp, y_exp, c3xy_exp);
    m_simp.mk_ite(c2, x_exp, c3xy_exp, c2c3_exp);
    m_simp.mk_ite(c1, y_exp, c2c3_exp, r_exp);

    mk_triple(r_sgn, r_sig, r_exp, result);
}

void fpa2bv_converter::mk_fusedma(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 4);
	
    // fusedma means (x * y) + z
	expr_ref rm(m), x(m), y(m), z(m);
	rm = args[0];
    x = args[1];
    y = args[2];
    z = args[3];

    expr_ref nan(m), nzero(m), pzero(m), ninf(m), pinf(m);
    mk_nan(f, nan);
    mk_nzero(f, nzero); 
    mk_pzero(f, pzero);
    mk_minus_inf(f, ninf);
    mk_plus_inf(f, pinf);        

    expr_ref x_is_nan(m), x_is_zero(m), x_is_pos(m), x_is_inf(m);
    expr_ref y_is_nan(m), y_is_zero(m), y_is_pos(m), y_is_inf(m);
    expr_ref z_is_nan(m), z_is_zero(m), z_is_pos(m), z_is_inf(m);
    mk_is_nan(x, x_is_nan);
    mk_is_zero(x, x_is_zero);
    mk_is_pos(x, x_is_pos);
    mk_is_inf(x, x_is_inf);
    mk_is_nan(y, y_is_nan);
    mk_is_zero(y, y_is_zero);
    mk_is_pos(y, y_is_pos);
    mk_is_inf(y, y_is_inf);
    mk_is_nan(z, z_is_nan);
    mk_is_zero(z, z_is_zero);
    mk_is_pos(z, z_is_pos);
    mk_is_inf(z, z_is_inf);

    dbg_decouple("fpa2bv_fma_x_is_nan", x_is_nan);
    dbg_decouple("fpa2bv_fma_x_is_zero", x_is_zero);
    dbg_decouple("fpa2bv_fma_x_is_pos", x_is_pos);
    dbg_decouple("fpa2bv_fma_x_is_inf", x_is_inf);
    dbg_decouple("fpa2bv_fma_y_is_nan", y_is_nan);
    dbg_decouple("fpa2bv_fma_y_is_zero", y_is_zero);
    dbg_decouple("fpa2bv_fma_y_is_pos", y_is_pos);
    dbg_decouple("fpa2bv_fma_y_is_inf", y_is_inf);
    dbg_decouple("fpa2bv_fma_z_is_nan", z_is_nan);
    dbg_decouple("fpa2bv_fma_z_is_zero", z_is_zero);
    dbg_decouple("fpa2bv_fma_z_is_pos", z_is_pos);
    dbg_decouple("fpa2bv_fma_z_is_inf", z_is_inf);

    expr_ref c1(m), c2(m), c3(m), c4(m), c5(m), c6(m);
    expr_ref v1(m), v2(m), v3(m), v4(m), v5(m), v6(m), v7(m);

    // (x is NaN) || (y is NaN) -> NaN
    m_simp.mk_or(x_is_nan, y_is_nan, c1);
    v1 = nan;
    
    // (x is +oo) -> if (y is 0) then NaN else inf with y's sign.
    mk_is_pinf(x, c2);
    expr_ref y_sgn_inf(m);
    mk_ite(y_is_pos, pinf, ninf, y_sgn_inf);
    mk_ite(y_is_zero, nan, y_sgn_inf, v2);
                
    // (y is +oo) -> if (x is 0) then NaN else inf with x's sign.
    mk_is_pinf(y, c3);
    expr_ref x_sgn_inf(m);
    mk_ite(x_is_pos, pinf, ninf, x_sgn_inf);
    mk_ite(x_is_zero, nan, x_sgn_inf, v3);
    
    // (x is -oo) -> if (y is 0) then NaN else inf with -y's sign.    
    mk_is_ninf(x, c4);
    expr_ref neg_y_sgn_inf(m);
    mk_ite(y_is_pos, ninf, pinf, neg_y_sgn_inf);
    mk_ite(y_is_zero, nan, neg_y_sgn_inf, v4);

    // (y is -oo) -> if (x is 0) then NaN else inf with -x's sign.    
    mk_is_ninf(y, c5);
    expr_ref neg_x_sgn_inf(m);
    mk_ite(x_is_pos, ninf, pinf, neg_x_sgn_inf);
    mk_ite(x_is_zero, nan, neg_x_sgn_inf, v5);

    // (x is 0) || (y is 0) -> x but with sign = x.sign ^ y.sign
    m_simp.mk_or(x_is_zero, y_is_zero, c6);
    expr_ref sign_xor(m);
    m_simp.mk_xor(x_is_pos, y_is_pos, sign_xor);
    mk_ite(sign_xor, nzero, pzero, v6);
        
    // else comes the fused multiplication.
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());
    SASSERT(ebits <= sbits);

    expr_ref rm_is_to_neg(m);
    mk_is_rm(rm, BV_RM_TO_NEGATIVE, rm_is_to_neg);

    expr_ref a_sgn(m), a_sig(m), a_exp(m);
    expr_ref b_sgn(m), b_sig(m), b_exp(m);
    expr_ref c_sgn(m), c_sig(m), c_exp(m);
    unpack(x, a_sgn, a_sig, a_exp, true);
    unpack(y, b_sgn, b_sig, b_exp, true);
    unpack(z, c_sgn, c_sig, c_exp, false);

    expr_ref lz_a(m), lz_b(m);
    mk_leading_zeros(a_sig, ebits+2, lz_a);
    mk_leading_zeros(b_sig, ebits+2, lz_b);

    expr_ref a_sig_ext(m), b_sig_ext(m);
    a_sig_ext = m_bv_util.mk_zero_extend(sbits, a_sig);
    b_sig_ext = m_bv_util.mk_zero_extend(sbits, b_sig);

    expr_ref a_exp_ext(m), b_exp_ext(m);
    a_exp_ext = m_bv_util.mk_sign_extend(2, a_exp);
    b_exp_ext = m_bv_util.mk_sign_extend(2, b_exp);

    expr_ref mul_sgn(m), mul_sig(m), mul_exp(m);
    expr * signs[2] = { a_sgn, b_sgn };
    mul_sgn = m_bv_util.mk_bv_xor(2, signs);

    dbg_decouple("fpa2bv_fma_mul_sgn", mul_sgn);

    mul_exp = m_bv_util.mk_bv_sub(
                m_bv_util.mk_bv_add(a_exp_ext, b_exp_ext),
                m_bv_util.mk_bv_add(lz_a, lz_b));
    
    mul_sig = m_bv_util.mk_bv_mul(a_sig_ext, b_sig_ext);

    dbg_decouple("fpa2bv_fma_mul_sig", mul_sig);

    SASSERT(m_bv_util.get_bv_size(mul_sig) == 2*sbits);

    // The result in `product' represents a number of the form 1.*** (unpacked)
    // (product = mul_sgn/mul_sig/mul_exp and c_sgn/c_sig/c_exp is unpacked w/o normalization).

    // extend c.
    c_sig = m_bv_util.mk_concat(c_sig, m_bv_util.mk_numeral(0, sbits));
    c_exp = m_bv_util.mk_sign_extend(2, c_exp);

    expr_ref swap_cond(m);
    swap_cond = m_bv_util.mk_sle(mul_exp, c_exp);
    SASSERT(is_well_sorted(m, swap_cond));

    expr_ref e_sgn(m), e_sig(m), e_exp(m), f_sgn(m), f_sig(m), f_exp(m);
    m_simp.mk_ite(swap_cond, c_sgn, mul_sgn, e_sgn);
    m_simp.mk_ite(swap_cond, c_sig, mul_sig, e_sig); // has 2 * sbits
    m_simp.mk_ite(swap_cond, c_exp, mul_exp, e_exp); // has ebits + 2
    m_simp.mk_ite(swap_cond, mul_sgn, c_sgn, f_sgn);
    m_simp.mk_ite(swap_cond, mul_sig, c_sig, f_sig); // has 2 * sbits
    m_simp.mk_ite(swap_cond, mul_exp, c_exp, f_exp); // has ebits + 2

    SASSERT(is_well_sorted(m, e_sgn));
    SASSERT(is_well_sorted(m, e_sig));
    SASSERT(is_well_sorted(m, e_exp));
    SASSERT(is_well_sorted(m, f_sgn));
    SASSERT(is_well_sorted(m, f_sig));
    SASSERT(is_well_sorted(m, f_exp));

    expr_ref res_sgn(m), res_sig(m), res_exp(m);
    add_core(2 * sbits, ebits + 2, rm,
             e_sgn, e_sig, e_exp, f_sgn, f_sig, f_exp, 
             res_sgn, res_sig, res_exp);

    // Note: res_sig is now 2 * sbits + 4, i.e., `sbits' too much, which should go into a sticky bit.
    unsigned sig_size = m_bv_util.get_bv_size(res_sig);
    SASSERT(sig_size == (2*sbits+4));

    // Note: res_exp is 2 bits too wide.
    unsigned exp_size = m_bv_util.get_bv_size(res_exp);
    SASSERT(exp_size == ebits+4);
    res_exp = m_bv_util.mk_extract(ebits+1, 0, res_exp);

    expr_ref sticky(m);
    sticky = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, m_bv_util.mk_extract(sbits, 0, res_sig));    
    res_sig = m_bv_util.mk_concat(m_bv_util.mk_extract(2*sbits+3, sbits+1, res_sig), sticky);        

    sig_size = m_bv_util.get_bv_size(res_sig);    
    SASSERT(sig_size == sbits+4);    

    expr_ref is_zero_sig(m);
    m_simp.mk_eq(res_sig, m_bv_util.mk_numeral(0, sbits+4), is_zero_sig);

    SASSERT(is_well_sorted(m, is_zero_sig));

    dbg_decouple("fpa2bv_fma_is_zero_sig", is_zero_sig);
    
    expr_ref zero_case(m);
    mk_ite(rm_is_to_neg, nzero, pzero, zero_case);

    expr_ref rounded(m);
    round(f->get_range(), rm, res_sgn, res_sig, res_exp, rounded);

    mk_ite(is_zero_sig, zero_case, rounded, v7);

    // And finally, we tie them together.
    mk_ite(c6, v6, v7, result);
    mk_ite(c5, v5, result, result);
    mk_ite(c4, v4, result, result);
    mk_ite(c3, v3, result, result);
    mk_ite(c2, v2, result, result);
    mk_ite(c1, v1, result, result);

    SASSERT(is_well_sorted(m, result));

    TRACE("fpa2bv_mul", tout << "MUL = " << mk_ismt2_pp(result, m) << std::endl; );
}

void fpa2bv_converter::mk_sqrt(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    NOT_IMPLEMENTED_YET();
}

void fpa2bv_converter::mk_round_to_integral(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
	
	expr_ref rm(m), x(m);
	rm = args[0];
    x = args[1];

    expr_ref nan(m), nzero(m), pzero(m), ninf(m), pinf(m);
    mk_nan(f, nan);
    mk_nzero(f, nzero); 
    mk_pzero(f, pzero);          

    expr_ref x_is_zero(m), x_is_pos(m);
    mk_is_zero(x, x_is_zero);
    mk_is_pos(x, x_is_pos);
    
    dbg_decouple("fpa2bv_r2i_x_is_zero", x_is_zero);
    dbg_decouple("fpa2bv_r2i_x_is_pos", x_is_pos);    

    expr_ref c1(m), c2(m), c3(m), c4(m);
    expr_ref v1(m), v2(m), v3(m), v4(m), v5(m);

    mk_is_nan(x, c1);
    v1 = nan;

    mk_is_inf(x, c2);
    v2 = x;
    
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());
    SASSERT(ebits < sbits);

    expr_ref a_sgn(m), a_sig(m), a_exp(m);
    unpack(x, a_sgn, a_sig, a_exp, true);

    expr_ref exp_is_small(m);
    m_simp.mk_eq(m_bv_util.mk_extract(ebits-1, ebits-1, a_exp),
                 m_bv_util.mk_numeral(1, 1),
                 exp_is_small);
    dbg_decouple("fpa2bv_r2i_exp_is_small", exp_is_small);
    c3 = exp_is_small;
    mk_ite(x_is_pos, pzero, nzero, v3);
    
    expr_ref exp_is_large(m);
    exp_is_large = m_bv_util.mk_sle(m_bv_util.mk_numeral(sbits-1, ebits), a_exp);
    dbg_decouple("fpa2bv_r2i_exp_is_large", exp_is_large);
    c4 = exp_is_large;
    v4 = x;

    // The actual rounding.
    expr_ref res_sgn(m), res_sig(m), res_exp(m);
    res_sgn = a_sgn;
    res_exp = m_bv_util.mk_concat(m_bv_util.mk_numeral(0, 2), a_exp);

    expr_ref shift(m), r_shifted(m), l_shifted(m);
    shift = m_bv_util.mk_bv_sub(m_bv_util.mk_numeral(sbits-1, ebits+1), 
                                m_bv_util.mk_sign_extend(1, a_exp));
    r_shifted = m_bv_util.mk_bv_lshr(a_sig, m_bv_util.mk_zero_extend(sbits-ebits-1, shift));
    SASSERT(m_bv_util.get_bv_size(r_shifted) == sbits);
    l_shifted = m_bv_util.mk_bv_shl(r_shifted, m_bv_util.mk_zero_extend(sbits-ebits-1, shift));    
    SASSERT(m_bv_util.get_bv_size(l_shifted) == sbits);

    res_sig = m_bv_util.mk_concat(m_bv_util.mk_numeral(0, 1), 
              m_bv_util.mk_concat(l_shifted, 
                                  m_bv_util.mk_numeral(0, 3)));

    SASSERT(m_bv_util.get_bv_size(res_sig) == (sbits + 4));

    round(f->get_range(), rm, res_sgn, res_sig, res_exp, v5);

    // And finally, we tie them together.
    mk_ite(c4, v4, v5, result);
    mk_ite(c3, v3, result, result);
    mk_ite(c2, v2, result, result);
    mk_ite(c1, v1, result, result);

    SASSERT(is_well_sorted(m, result));

    TRACE("fpa2bv_round_to_integral", tout << "ROUND2INTEGRAL = " << mk_ismt2_pp(result, m) << std::endl; );
}

void fpa2bv_converter::mk_float_eq(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);

    expr * x = args[0], * y = args[1];

    expr_ref c1(m), c2(m), x_is_nan(m), y_is_nan(m), x_is_zero(m), y_is_zero(m);
    mk_is_nan(x, x_is_nan);
    mk_is_nan(y, y_is_nan);
    m_simp.mk_or(x_is_nan, y_is_nan, c1);
    mk_is_zero(x, x_is_zero);
    mk_is_zero(y, y_is_zero);
    m_simp.mk_and(x_is_zero, y_is_zero, c2);

    expr * x_sgn, * x_sig, * x_exp;
    expr * y_sgn, * y_sig, * y_exp;
    split(x, x_sgn, x_sig, x_exp);
    split(y, y_sgn, y_sig, y_exp);
    
    expr_ref x_eq_y_sgn(m), x_eq_y_exp(m), x_eq_y_sig(m);
    m_simp.mk_eq(x_sgn, y_sgn, x_eq_y_sgn);
    m_simp.mk_eq(x_exp, y_exp, x_eq_y_exp);
    m_simp.mk_eq(x_sig, y_sig, x_eq_y_sig);

    expr_ref c3(m), t4(m);
    m_simp.mk_not(x_eq_y_sgn, c3);
    m_simp.mk_and(x_eq_y_exp, x_eq_y_sig, t4);

    expr_ref c3t4(m), c2else(m);
    m_simp.mk_ite(c3, m.mk_false(), t4, c3t4);
    m_simp.mk_ite(c2, m.mk_true(), c3t4, c2else);

    m_simp.mk_ite(c1, m.mk_false(), c2else, result);
}

void fpa2bv_converter::mk_float_lt(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);

    expr * x = args[0], * y = args[1];
    
    expr_ref c1(m), c2(m), x_is_nan(m), y_is_nan(m), x_is_zero(m), y_is_zero(m);
    mk_is_nan(x, x_is_nan);
    mk_is_nan(y, y_is_nan);
    m_simp.mk_or(x_is_nan, y_is_nan, c1);
    mk_is_zero(x, x_is_zero);
    mk_is_zero(y, y_is_zero);
    m_simp.mk_and(x_is_zero, y_is_zero, c2);

    expr * x_sgn, * x_sig, * x_exp;
    expr * y_sgn, * y_sig, * y_exp;
    split(x, x_sgn, x_sig, x_exp);
    split(y, y_sgn, y_sig, y_exp);

    expr_ref c3(m), t3(m), t4(m);

    m_simp.mk_eq(x_sgn, m_bv_util.mk_numeral(1, 1), c3);

    expr_ref y_sgn_eq_0(m), y_lt_x_exp(m), y_lt_x_sig(m), y_eq_x_exp(m), y_le_x_sig_exp(m), t3_or(m);
    m_simp.mk_eq(y_sgn, m_bv_util.mk_numeral(0, 1), y_sgn_eq_0);
    BVULT(y_exp, x_exp, y_lt_x_exp);
    BVULT(y_sig, x_sig, y_lt_x_sig);
    m_simp.mk_eq(y_exp, x_exp, y_eq_x_exp);
    m_simp.mk_and(y_eq_x_exp, y_lt_x_sig, y_le_x_sig_exp);
    m_simp.mk_or(y_lt_x_exp, y_le_x_sig_exp, t3_or);
    m_simp.mk_ite(y_sgn_eq_0, m.mk_true(), t3_or, t3);

    expr_ref y_sgn_eq_1(m), x_lt_y_exp(m), x_eq_y_exp(m), x_lt_y_sig(m), x_le_y_sig_exp(m), t4_or(m);
    m_simp.mk_eq(y_sgn, m_bv_util.mk_numeral(1, 1), y_sgn_eq_1);
    BVULT(x_exp, y_exp, x_lt_y_exp);
    m_simp.mk_eq(x_exp, y_exp, x_eq_y_exp);
    BVULT(x_sig, y_sig, x_lt_y_sig);
    m_simp.mk_and(x_eq_y_exp, x_lt_y_sig, x_le_y_sig_exp);
    m_simp.mk_or(x_lt_y_exp, x_le_y_sig_exp, t4_or);
    m_simp.mk_ite(y_sgn_eq_1, m.mk_false(), t4_or, t4);

    expr_ref c3t3t4(m), c2else(m);
    m_simp.mk_ite(c3, t3, t4, c3t3t4);
    m_simp.mk_ite(c2, m.mk_false(), c3t3t4, c2else);
    m_simp.mk_ite(c1, m.mk_false(), c2else, result);
}

void fpa2bv_converter::mk_float_gt(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);

    expr * x = args[0], * y = args[1];

    expr_ref t3(m);
    mk_float_le(f, num, args, t3);

    expr_ref nan_or(m), xy_zero(m), not_t3(m), r_else(m);
    expr_ref x_is_nan(m), y_is_nan(m), x_is_zero(m), y_is_zero(m);
    mk_is_nan(x, x_is_nan);
    mk_is_nan(y, y_is_nan);
    m_simp.mk_or(x_is_nan, y_is_nan, nan_or);
    mk_is_zero(x, x_is_zero);
    mk_is_zero(y, y_is_zero);
    m_simp.mk_and(x_is_zero, y_is_zero, xy_zero);
    m_simp.mk_not(t3, not_t3);
    m_simp.mk_ite(xy_zero, m.mk_false(), not_t3, r_else);
    m_simp.mk_ite(nan_or, m.mk_false(), r_else, result);
}

void fpa2bv_converter::mk_float_le(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
    expr_ref a(m), b(m);
    mk_float_lt(f, num, args, a);
    mk_float_eq(f, num, args, b);
    m_simp.mk_or(a, b, result);
}

void fpa2bv_converter::mk_float_ge(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
    expr_ref a(m), b(m);
    mk_float_gt(f, num, args, a);
    mk_float_eq(f, num, args, b);
    m_simp.mk_or(a, b, result);
}

void fpa2bv_converter::mk_is_zero(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    mk_is_zero(args[0], result);
}

void fpa2bv_converter::mk_is_nzero(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    expr_ref a0_is_neg(m), a0_is_zero(m);
    mk_is_neg(args[0], a0_is_neg);
    mk_is_zero(args[0], a0_is_zero);
    m_simp.mk_and(a0_is_neg, a0_is_zero, result);
}

void fpa2bv_converter::mk_is_pzero(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    expr_ref a0_is_pos(m), a0_is_zero(m);
    mk_is_pos(args[0], a0_is_pos);
    mk_is_zero(args[0], a0_is_zero);
    m_simp.mk_and(a0_is_pos, a0_is_zero, result);
}

void fpa2bv_converter::mk_is_sign_minus(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    mk_is_neg(args[0], result);
}

void fpa2bv_converter::mk_to_float(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    if (num == 3 && m_bv_util.is_bv(args[0]) && 
        m_bv_util.is_bv(args[1]) && m_bv_util.is_bv(args[2])) {
        // Theoretically, the user could have thrown in it's own triple of bit-vectors. 
        // Just keep it here, as there will be something else that uses it.
        mk_triple(args[0], args[1], args[2], result);
    }
    else {
        SASSERT(num == 2);
        SASSERT(m_util.is_float(f->get_range()));        
        unsigned ebits = m_util.get_ebits(f->get_range());
        unsigned sbits = m_util.get_sbits(f->get_range());
    
        SASSERT(m_util.is_rm(to_app(args[0])->get_decl()->get_range()));                
        mpf_rounding_mode rm = static_cast<mpf_rounding_mode>(to_app(args[1])->get_decl_kind());
    
        rational q;
        SASSERT(m_util.au().is_numeral(args[1]));    
        m_util.au().is_numeral(args[1], q);

        mpf v;
        m_util.fm().set(v, ebits, sbits, rm, q.to_mpq());
    
        expr * sgn = m_bv_util.mk_numeral((m_util.fm().sgn(v)) ? 1 : 0, 1);
        expr * s = m_bv_util.mk_numeral(m_util.fm().sig(v), sbits-1);
        expr * e = m_bv_util.mk_numeral(m_util.fm().exp(v), ebits);

        mk_triple(sgn, s, e, result);

        m_util.fm().del(v);
    }
}

void fpa2bv_converter::split(expr * e, expr * & sgn, expr * & sig, expr * & exp) const {
    SASSERT(is_app_of(e, m_plugin->get_family_id(), OP_TO_FLOAT));
    SASSERT(to_app(e)->get_num_args() == 3);
    
    sgn = to_app(e)->get_arg(0);
    sig = to_app(e)->get_arg(1);
    exp = to_app(e)->get_arg(2);
}

void fpa2bv_converter::mk_is_nan(expr * e, expr_ref & result) {
    expr * sgn, * sig, * exp;
    split(e, sgn, sig, exp);
    
    // exp == 1^n , sig != 0
    expr_ref sig_is_zero(m), sig_is_not_zero(m), exp_is_top(m), top_exp(m);
    mk_top_exp(m_bv_util.get_bv_size(exp), top_exp);

    m_simp.mk_eq(sig, m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(sig)), sig_is_zero);
    m_simp.mk_not(sig_is_zero, sig_is_not_zero);
    m_simp.mk_eq(exp, top_exp, exp_is_top);
    m_simp.mk_and(exp_is_top, sig_is_not_zero, result);
}

void fpa2bv_converter::mk_is_inf(expr * e, expr_ref & result) {
    expr * sgn, * sig, * exp;
    split(e, sgn, sig, exp);
    expr_ref eq1(m), eq2(m), top_exp(m);
    mk_top_exp(m_bv_util.get_bv_size(exp), top_exp);
    m_simp.mk_eq(sig, m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(sig)), eq1);
    m_simp.mk_eq(exp, top_exp, eq2);
    m_simp.mk_and(eq1, eq2, result);
}

void fpa2bv_converter::mk_is_pinf(expr * e, expr_ref & result) {
    expr_ref e_is_pos(m), e_is_inf(m);
    mk_is_pos(e, e_is_pos);
    mk_is_inf(e, e_is_inf);
    m_simp.mk_and(e_is_pos, e_is_inf, result);
}

void fpa2bv_converter::mk_is_ninf(expr * e, expr_ref & result) {
    expr_ref e_is_neg(m), e_is_inf(m);
    mk_is_neg(e, e_is_neg);
    mk_is_inf(e, e_is_inf);
    m_simp.mk_and(e_is_neg, e_is_inf, result);
}

void fpa2bv_converter::mk_is_pos(expr * e, expr_ref & result) {
    SASSERT(is_app_of(e, m_plugin->get_family_id(), OP_TO_FLOAT));
    SASSERT(to_app(e)->get_num_args() == 3);
    expr * a0 = to_app(e)->get_arg(0);
    m_simp.mk_eq(a0, m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(a0)), result);
}

void fpa2bv_converter::mk_is_neg(expr * e, expr_ref & result) {
    SASSERT(is_app_of(e, m_plugin->get_family_id(), OP_TO_FLOAT));
    SASSERT(to_app(e)->get_num_args() == 3);
    expr * a0 = to_app(e)->get_arg(0);
    m_simp.mk_eq(a0, m_bv_util.mk_numeral(1, m_bv_util.get_bv_size(a0)), result);
}

void fpa2bv_converter::mk_is_zero(expr * e, expr_ref & result) {
    expr * sgn, * sig, * exp;
    split(e, sgn, sig, exp);
    expr_ref eq1(m), eq2(m), bot_exp(m);
    mk_bot_exp(m_bv_util.get_bv_size(exp), bot_exp);
    m_simp.mk_eq(sig, m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(sig)), eq1);
    m_simp.mk_eq(exp, bot_exp, eq2);
    m_simp.mk_and(eq1, eq2, result);
}

void fpa2bv_converter::mk_is_nzero(expr * e, expr_ref & result) {
    expr * sgn, * sig, * exp;
    split(e, sgn, sig, exp);
    expr_ref e_is_zero(m), eq(m);
    mk_is_zero(e, e_is_zero);
    m_simp.mk_eq(sgn, m_bv_util.mk_numeral(1, 1), eq);
    m_simp.mk_and(eq, e_is_zero, result);
}

void fpa2bv_converter::mk_is_pzero(expr * e, expr_ref & result) {
    expr * sgn, * sig, * exp;
    split(e, sgn, sig, exp);
    expr_ref e_is_zero(m), eq(m);
    mk_is_zero(e, e_is_zero);
    m_simp.mk_eq(sgn, m_bv_util.mk_numeral(0, 1), eq);
    m_simp.mk_and(eq, e_is_zero, result);
}

void fpa2bv_converter::mk_is_denormal(expr * e, expr_ref & result) {
    expr * sgn, * sig, * exp;
    split(e, sgn, sig, exp);
    m_simp.mk_eq(exp, m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(exp)), result);
}

void fpa2bv_converter::mk_is_normal(expr * e, expr_ref & result) {    
    expr * sgn, * sig, * exp;
    split(e, sgn, sig, exp);

    expr_ref is_special(m), is_denormal(m);
    mk_is_denormal(e, is_denormal);
    unsigned ebits = m_bv_util.get_bv_size(exp);
    m_simp.mk_eq(exp, m_bv_util.mk_numeral(fu().fm().m_powers2.m1(ebits), ebits), is_special);

    expr_ref or_ex(m);
    m_simp.mk_or(is_special, is_denormal, or_ex);
    m_simp.mk_not(or_ex, result);
}

void fpa2bv_converter::mk_is_rm(expr * e, BV_RM_VAL rm, expr_ref & result) {
	SASSERT(m_bv_util.is_bv(e) && m_bv_util.get_bv_size(e) == 3);
    expr_ref rm_num(m);
    rm_num = m_bv_util.mk_numeral(rm, 3);
	switch(rm)
	{
	case BV_RM_TIES_TO_AWAY: 
	case BV_RM_TIES_TO_EVEN: 
	case BV_RM_TO_NEGATIVE:
	case BV_RM_TO_POSITIVE: return m_simp.mk_eq(e, rm_num, result);
	case BV_RM_TO_ZERO: 
	default:
        rm_num = m_bv_util.mk_numeral(BV_RM_TO_POSITIVE, 3);
        expr_ref r(m); r = m_bv_util.mk_ule(e, rm_num);
        return m_simp.mk_not(r, result);
	}
}

void fpa2bv_converter::mk_top_exp(unsigned sz, expr_ref & result) {
    result = m_bv_util.mk_numeral(fu().fm().m_powers2.m1(sz), sz);
}

void fpa2bv_converter::mk_bot_exp(unsigned sz, expr_ref & result) {
    result = m_bv_util.mk_numeral(0, sz);
}

void fpa2bv_converter::mk_min_exp(unsigned ebits, expr_ref & result) {
    SASSERT(ebits > 0);
    const mpz & z = m_mpf_manager.m_powers2.m1(ebits-1, true);
    result = m_bv_util.mk_numeral(z + mpz(1), ebits);
}

void fpa2bv_converter::mk_max_exp(unsigned ebits, expr_ref & result) {
    SASSERT(ebits > 0);		
    result = m_bv_util.mk_numeral(m_mpf_manager.m_powers2.m1(ebits-1, false), ebits);
}

void fpa2bv_converter::mk_leading_zeros(expr * e, unsigned max_bits, expr_ref & result) { 
    SASSERT(m_bv_util.is_bv(e));
    unsigned bv_sz = m_bv_util.get_bv_size(e);

    if (bv_sz == 0)
        result = m_bv_util.mk_numeral(0, max_bits);
    else if (bv_sz == 1) {
        expr_ref eq(m);
        m_simp.mk_eq(e, m_bv_util.mk_numeral(0, 1), eq);
        m_simp.mk_ite(eq, m_bv_util.mk_numeral(1, max_bits), m_bv_util.mk_numeral(0, max_bits), result);
    }
    else {
        expr_ref H(m), L(m);
        H = m_bv_util.mk_extract(bv_sz-1, bv_sz/2, e);
        L = m_bv_util.mk_extract(bv_sz/2-1, 0, e);

        unsigned H_size = m_bv_util.get_bv_size(H);
        // unsigned L_size = m_bv_util.get_bv_size(L);

        expr_ref lzH(m), lzL(m);
        mk_leading_zeros(H, max_bits, lzH); /* recursive! */
        mk_leading_zeros(L, max_bits, lzL);

        expr_ref H_is_zero(m);
        m_simp.mk_eq(H, m_bv_util.mk_numeral(0, H_size), H_is_zero);        

        expr_ref sum(m);
        sum = m_bv_util.mk_bv_add(m_bv_util.mk_numeral(H_size, max_bits), lzL);
        m_simp.mk_ite(H_is_zero, sum, lzH, result);        
    }

    SASSERT(is_well_sorted(m, result));
}

void fpa2bv_converter::mk_bias(expr * e, expr_ref & result) {    
    unsigned ebits = m_bv_util.get_bv_size(e);
    SASSERT(ebits >= 2);

    expr_ref mask(m);
    mask = m_bv_util.mk_numeral(fu().fm().m_powers2.m1(ebits-1), ebits);
    result = m_bv_util.mk_bv_add(e, mask);
}

void fpa2bv_converter::mk_unbias(expr * e, expr_ref & result) {
    unsigned ebits = m_bv_util.get_bv_size(e);
    SASSERT(ebits >= 2);

    expr_ref e_plus_one(m);
    e_plus_one = m_bv_util.mk_bv_add(e, m_bv_util.mk_numeral(1, ebits));
    
    expr_ref leading(m), n_leading(m), rest(m);
    leading = m_bv_util.mk_extract(ebits-1, ebits-1, e_plus_one);
    n_leading = m_bv_util.mk_bv_not(leading);
    rest = m_bv_util.mk_extract(ebits-2, 0, e_plus_one);

    result = m_bv_util.mk_concat(n_leading, rest);
}

void fpa2bv_converter::unpack(expr * e, expr_ref & sgn, expr_ref & sig, expr_ref & exp, bool normalize) {
    SASSERT(is_app_of(e, m_plugin->get_family_id(), OP_TO_FLOAT));
    SASSERT(to_app(e)->get_num_args() == 3);

    sort * srt = to_app(e)->get_decl()->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);

    sgn = to_app(e)->get_arg(0);
    sig = to_app(e)->get_arg(1);
    exp = to_app(e)->get_arg(2);

    expr_ref is_normal(m);
    mk_is_normal(e, is_normal);

    expr_ref normal_sig(m), normal_exp(m);
    normal_sig = m_bv_util.mk_concat(m_bv_util.mk_numeral(1, 1), sig);
    mk_unbias(exp, normal_exp);

    expr_ref denormal_sig(m), denormal_exp(m);
    denormal_sig = m_bv_util.mk_concat(m_bv_util.mk_numeral(0, 1), sig);    
    denormal_exp = m_bv_util.mk_numeral(1, ebits);
    mk_unbias(denormal_exp, denormal_exp);

    if (normalize) {
        SASSERT(ebits <= sbits);
        expr_ref is_sig_zero(m), shift(m), lz(m);
        m_simp.mk_eq(m_bv_util.mk_numeral(0, sbits-1), sig, is_sig_zero);
        mk_leading_zeros(sig, ebits, lz);
        m_simp.mk_ite(is_sig_zero, m_bv_util.mk_numeral(0, ebits), lz, shift);
        SASSERT(is_well_sorted(m, is_sig_zero));
        SASSERT(is_well_sorted(m, lz));
        SASSERT(is_well_sorted(m, shift));
        denormal_sig = m_bv_util.mk_bv_shl(denormal_sig, m_bv_util.mk_zero_extend(sbits-ebits, shift));
        // CMW: The book says we don't need this, but it feels wrong not to do that.
        //denormal_exp = m_bv_util.mk_bv_sub(denormal_exp, shift);
    }

    SASSERT(is_well_sorted(m, normal_sig));
    SASSERT(is_well_sorted(m, denormal_sig));

    m_simp.mk_ite(is_normal, normal_sig, denormal_sig, sig);
    m_simp.mk_ite(is_normal, normal_exp, denormal_exp, exp);

    SASSERT(is_well_sorted(m, sgn));
    SASSERT(is_well_sorted(m, sig));
    SASSERT(is_well_sorted(m, exp));

    SASSERT(m_bv_util.get_bv_size(sgn) == 1);
    SASSERT(m_bv_util.get_bv_size(sig) == sbits);
    SASSERT(m_bv_util.get_bv_size(exp) == ebits);

    TRACE("fpa2bv_unpack", tout << "UNPACK SGN = " << mk_ismt2_pp(sgn, m) << std::endl; );
    TRACE("fpa2bv_unpack", tout << "UNPACK SIG = " << mk_ismt2_pp(sig, m) << std::endl; );
    TRACE("fpa2bv_unpack", tout << "UNPACK EXP = " << mk_ismt2_pp(exp, m) << std::endl; );
}

void fpa2bv_converter::mk_rounding_mode(func_decl * f, expr_ref & result)
{
	switch(f->get_decl_kind())
	{	
	case OP_RM_NEAREST_TIES_TO_AWAY: result = m_bv_util.mk_numeral(BV_RM_TIES_TO_AWAY, 3); break;
    case OP_RM_NEAREST_TIES_TO_EVEN: result = m_bv_util.mk_numeral(BV_RM_TIES_TO_EVEN, 3); break;
    case OP_RM_TOWARD_NEGATIVE: result = m_bv_util.mk_numeral(BV_RM_TO_NEGATIVE, 3); break;
    case OP_RM_TOWARD_POSITIVE: result = m_bv_util.mk_numeral(BV_RM_TO_POSITIVE, 3); break;
	case OP_RM_TOWARD_ZERO: result = m_bv_util.mk_numeral(BV_RM_TO_ZERO, 3); break;	
	default: UNREACHABLE();
	}
}

void fpa2bv_converter::dbg_decouple(const char * prefix, expr_ref & e) {
    #ifdef _DEBUG
    expr_ref new_e(m);
    new_e = m.mk_fresh_const(prefix, m.get_sort(e));
    extra_assertions.push_back(m.mk_eq(new_e, e));    
    e = new_e;
    #endif
}

void fpa2bv_converter::round(sort * s, expr_ref & rm, expr_ref & sgn, expr_ref & sig, expr_ref & exp, expr_ref & result) {
    unsigned ebits = m_util.get_ebits(s);
    unsigned sbits = m_util.get_sbits(s);

    dbg_decouple("fpa2bv_rnd_rm", rm);
    dbg_decouple("fpa2bv_rnd_sgn", sgn);
    dbg_decouple("fpa2bv_rnd_sig", sig);
    dbg_decouple("fpa2bv_rnd_exp", exp);    

	SASSERT(is_well_sorted(m, rm));
	SASSERT(is_well_sorted(m, sgn));
	SASSERT(is_well_sorted(m, sig));
	SASSERT(is_well_sorted(m, exp));	

	TRACE("fpa2bv_dbg", tout << "RND: " << std::endl <<
								"ebits = " << ebits << std::endl <<
								"sbits = " << sbits << std::endl <<
		                        "sgn = " << mk_ismt2_pp(sgn, m) << std::endl <<
								"sig = " << mk_ismt2_pp(sig, m) << std::endl <<
								"exp = " << mk_ismt2_pp(exp, m) << std::endl; );

	// Assumptions: sig is of the form f[-1:0] . f[1:sbits-1] [guard,round,sticky], 
    // i.e., it has 2 + (sbits-1) + 3 = sbits + 4 bits, where the first one is in sgn.
	// Furthermore, note that sig is an unsigned bit-vector, while exp is signed.
    
	SASSERT(ebits <= sbits);
	SASSERT(m_bv_util.is_bv(rm) && m_bv_util.get_bv_size(rm) == 3);
	SASSERT(m_bv_util.is_bv(sgn) && m_bv_util.get_bv_size(sgn) == 1);
	SASSERT(m_bv_util.is_bv(sig) && m_bv_util.get_bv_size(sig) >= 5);
	SASSERT(m_bv_util.is_bv(exp) && m_bv_util.get_bv_size(exp) >= 4);

    SASSERT(m_bv_util.get_bv_size(sig) == sbits+4);
    SASSERT(m_bv_util.get_bv_size(exp) == ebits+2);

	// bool UNFen = false;
    // bool OVFen = false;

	expr_ref e_min(m), e_max(m);
	mk_min_exp(ebits, e_min);
	mk_max_exp(ebits, e_max);

	TRACE("fpa2bv_dbg", tout << "e_min = " << mk_ismt2_pp(e_min, m) << std::endl <<
                                "e_max = " << mk_ismt2_pp(e_max, m) << std::endl;);	

	expr_ref OVF1(m), e_top_three(m), sigm1(m), e_eq_emax_and_sigm1(m), e_eq_emax(m);
    expr_ref e3(m), ne3(m), e2(m), e1(m), e21(m);    
    m_simp.mk_eq(m_bv_util.mk_extract(ebits+1, ebits+1, exp), m_bv_util.mk_numeral(1, 1), e3);
    m_simp.mk_eq(m_bv_util.mk_extract(ebits, ebits, exp), m_bv_util.mk_numeral(1, 1), e2);
    m_simp.mk_eq(m_bv_util.mk_extract(ebits-1, ebits-1, exp), m_bv_util.mk_numeral(1, 1), e1);
    m_simp.mk_or(e2, e1, e21);
    m_simp.mk_not(e3, ne3);
    m_simp.mk_and(ne3, e21, e_top_three);
    m_simp.mk_eq(m_bv_util.mk_zero_extend(2, e_max), exp, e_eq_emax);
    m_simp.mk_eq(m_bv_util.mk_extract(sbits+3, sbits+3, sig), m_bv_util.mk_numeral(1, 1), sigm1);
    m_simp.mk_and(e_eq_emax, sigm1, e_eq_emax_and_sigm1);
    m_simp.mk_or(e_top_three, e_eq_emax_and_sigm1, OVF1);
    
    dbg_decouple("fpa2bv_rnd_OVF1", OVF1);

    TRACE("fpa2bv_dbg", tout << "OVF1 = " << mk_ismt2_pp(OVF1, m) << std::endl;);	
	SASSERT(is_well_sorted(m, OVF1));

	expr_ref lz(m);
	mk_leading_zeros(sig, ebits+2, lz); // CMW: is this always large enough?

    dbg_decouple("fpa2bv_rnd_lz", lz);

	TRACE("fpa2bv_dbg", tout << "LZ = " << mk_ismt2_pp(lz, m) << std::endl;);

	expr_ref t(m);
	t = m_bv_util.mk_bv_add(exp, m_bv_util.mk_numeral(1, ebits+2));
    t = m_bv_util.mk_bv_sub(t, lz); 
	t = m_bv_util.mk_bv_sub(t, m_bv_util.mk_sign_extend(2, e_min));
    expr_ref TINY(m);
	TINY = m_bv_util.mk_sle(t, m_bv_util.mk_numeral(-1, ebits+2));
    
	TRACE("fpa2bv_dbg", tout << "TINY = " << mk_ismt2_pp(TINY, m) << std::endl;);
	SASSERT(is_well_sorted(m, TINY));

    dbg_decouple("fpa2bv_rnd_TINY", TINY);

    expr_ref beta(m);	
    beta = m_bv_util.mk_bv_add(m_bv_util.mk_bv_sub(exp, lz), m_bv_util.mk_numeral(1, ebits+2));

    TRACE("fpa2bv_dbg", tout << "beta = " << mk_ismt2_pp(beta, m)<< std::endl; );	
	SASSERT(is_well_sorted(m, beta));

    dbg_decouple("fpa2bv_rnd_beta", beta);

	expr_ref sigma(m), sigma_add(m);
    sigma_add = m_bv_util.mk_bv_add(exp, m_bv_util.mk_numeral(fu().fm().m_powers2.m1(ebits-1), ebits+2));
	m_simp.mk_ite(TINY, sigma_add, lz, sigma);

    dbg_decouple("fpa2bv_rnd_sigma", sigma);

	TRACE("fpa2bv_dbg", tout << "Shift distance: " << mk_ismt2_pp(sigma, m) << std::endl;);
    SASSERT(is_well_sorted(m, sigma));

	// Normalization shift
    dbg_decouple("fpa2bv_rnd_sig_before_shift", sig);

	unsigned sig_size = m_bv_util.get_bv_size(sig);
    SASSERT(sig_size == sbits+4);
	unsigned sigma_size = m_bv_util.get_bv_size(sigma);

	expr_ref sigma_neg(m), sigma_cap(m), sigma_neg_capped(m), sigma_lt_zero(m), sig_ext(m), rs_sig(m), ls_sig(m), big_sh_sig(m);
	sigma_neg = m_bv_util.mk_bv_neg(sigma);
    sigma_cap = m_bv_util.mk_numeral(sbits+2, sigma_size);
    m_simp.mk_ite(m_bv_util.mk_sle(sigma_neg, sigma_cap), sigma_neg, sigma_cap, sigma_neg_capped);
    dbg_decouple("fpa2bv_rnd_sigma_neg", sigma_neg);
    dbg_decouple("fpa2bv_rnd_sigma_neg_capped", sigma_neg_capped);
	sigma_lt_zero = m_bv_util.mk_sle(sigma, m_bv_util.mk_numeral(-1, sigma_size));
    dbg_decouple("fpa2bv_rnd_sigma_lt_zero", sigma_lt_zero);

	sig_ext = m_bv_util.mk_concat(sig, m_bv_util.mk_numeral(0, sig_size)); 
	rs_sig = m_bv_util.mk_bv_lshr(sig_ext, m_bv_util.mk_zero_extend(2*sig_size - sigma_size, sigma_neg_capped));
	ls_sig = m_bv_util.mk_bv_shl(sig_ext, m_bv_util.mk_zero_extend(2*sig_size - sigma_size, sigma));
	m_simp.mk_ite(sigma_lt_zero, rs_sig, ls_sig, big_sh_sig);
    SASSERT(m_bv_util.get_bv_size(big_sh_sig) == 2*sig_size);

    dbg_decouple("fpa2bv_rnd_big_sh_sig", big_sh_sig);

    unsigned sig_extract_low_bit = (2*sig_size-1)-(sbits+2)+1;
	sig = m_bv_util.mk_extract(2*sig_size-1, sig_extract_low_bit, big_sh_sig);
    SASSERT(m_bv_util.get_bv_size(sig) == sbits+2);

    dbg_decouple("fpa2bv_rnd_shifted_sig", sig);

	expr_ref sticky(m);
	sticky = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, m_bv_util.mk_extract(sig_extract_low_bit-1, 0, big_sh_sig));
	SASSERT(is_well_sorted(m, sticky));
	SASSERT(is_well_sorted(m, sig));

	// put the sticky bit into the significand.
	expr * tmp[] = { sig, m_bv_util.mk_zero_extend(sbits+1, sticky) };
	sig = m_bv_util.mk_bv_or(2, tmp);
    SASSERT(is_well_sorted(m, sig));
    SASSERT(m_bv_util.get_bv_size(sig) == sbits+2);	
	
	// CMW: The (OVF1 && OVFen) and (TINY && UNFen) cases are never taken.
	m_simp.mk_ite(TINY, m_bv_util.mk_zero_extend(2, e_min), beta, exp);
	SASSERT(is_well_sorted(m, exp));

	// Significand rounding
    expr_ref round(m), last(m);
	sticky = m_bv_util.mk_extract(0, 0, sig); // new sticky bit!    
	round = m_bv_util.mk_extract(1, 1, sig);
    last = m_bv_util.mk_extract(2, 2, sig);

    TRACE("fpa2bv_dbg", tout << "sticky = " << mk_ismt2_pp(sticky, m) << std::endl;);

    dbg_decouple("fpa2bv_rnd_sticky", sticky);
    dbg_decouple("fpa2bv_rnd_round", round);
    dbg_decouple("fpa2bv_rnd_last", last);

	sig = m_bv_util.mk_extract(sbits+1, 2, sig);

	expr * last_sticky[2] = { last, sticky };
	expr * round_sticky[2] = { round, sticky };	    
	expr * last_or_sticky = m_bv_util.mk_bv_or(2, last_sticky);
	expr * round_or_sticky = m_bv_util.mk_bv_or(2, round_sticky); 
	expr * round_lors[2] = { m_bv_util.mk_bv_not(round), m_bv_util.mk_bv_not(last_or_sticky) };	
	expr * pos_args[2] = { sgn, m_bv_util.mk_bv_not(round_or_sticky) };
	expr * neg_args[2] = { m_bv_util.mk_bv_not(sgn), m_bv_util.mk_bv_not(round_or_sticky) };

    expr_ref inc_teven(m), inc_taway(m), inc_pos(m), inc_neg(m);
	inc_teven = m_bv_util.mk_bv_not(m_bv_util.mk_bv_or(2, round_lors));
	inc_taway = round;
	inc_pos = m_bv_util.mk_bv_not(m_bv_util.mk_bv_or(2, pos_args));
	inc_neg = m_bv_util.mk_bv_not(m_bv_util.mk_bv_or(2, neg_args));

    expr_ref inc(m), inc_c2(m), inc_c3(m), inc_c4(m);
    expr_ref rm_is_to_neg(m), rm_is_to_pos(m), rm_is_away(m), rm_is_even(m);
    mk_is_rm(rm, BV_RM_TO_NEGATIVE, rm_is_to_neg);
    mk_is_rm(rm, BV_RM_TO_POSITIVE, rm_is_to_pos);
    mk_is_rm(rm, BV_RM_TIES_TO_AWAY, rm_is_away);
    mk_is_rm(rm, BV_RM_TIES_TO_EVEN, rm_is_even);
    m_simp.mk_ite(rm_is_to_neg, inc_neg, m_bv_util.mk_numeral(0, 1), inc_c4);
    m_simp.mk_ite(rm_is_to_pos, inc_pos, inc_c4, inc_c3);
    m_simp.mk_ite(rm_is_away, inc_taway, inc_c3, inc_c2);
	m_simp.mk_ite(rm_is_even, inc_teven, inc_c2, inc);
    
	SASSERT(m_bv_util.get_bv_size(inc) == 1 && is_well_sorted(m, inc));
    dbg_decouple("fpa2bv_rnd_inc", inc);

	sig = m_bv_util.mk_bv_add(m_bv_util.mk_zero_extend(1, sig), 
						      m_bv_util.mk_zero_extend(sbits, inc));
	SASSERT(is_well_sorted(m, sig));
    dbg_decouple("fpa2bv_rnd_sig_plus_inc", sig);

	// Post normalization	
	SASSERT(m_bv_util.get_bv_size(sig) == sbits + 1);
    expr_ref SIGovf(m);
    m_simp.mk_eq(m_bv_util.mk_extract(sbits, sbits, sig), m_bv_util.mk_numeral(1, 1), SIGovf);
    SASSERT(is_well_sorted(m, SIGovf));    
    dbg_decouple("fpa2bv_rnd_SIGovf", SIGovf);

	m_simp.mk_ite(SIGovf,
				  m_bv_util.mk_extract(sbits, 1, sig),
				  m_bv_util.mk_extract(sbits-1, 0, sig), 
                  sig);

	SASSERT(m_bv_util.get_bv_size(exp) == ebits + 2);

	m_simp.mk_ite(SIGovf, 
				  m_bv_util.mk_bv_add(exp, m_bv_util.mk_numeral(1, ebits+2)),
				  exp,
                  exp);

	SASSERT(is_well_sorted(m, sig));
	SASSERT(is_well_sorted(m, exp));
    dbg_decouple("fpa2bv_rnd_sig_postnormalized", sig);
    dbg_decouple("fpa2bv_rnd_exp_postnormalized", exp);
	
	SASSERT(m_bv_util.get_bv_size(sig) == sbits);
	SASSERT(m_bv_util.get_bv_size(exp) == ebits + 2);
	SASSERT(m_bv_util.get_bv_size(e_max) == ebits);

	// Exponent adjustment and rounding        
    expr_ref biased_exp(m);
    mk_bias(m_bv_util.mk_extract(ebits-1, 0, exp), biased_exp);
    dbg_decouple("fpa2bv_rnd_unbiased_exp", exp);
    dbg_decouple("fpa2bv_rnd_biased_exp", biased_exp);

    // AdjustExp
    SASSERT(is_well_sorted(m, OVF1));
    SASSERT(m.is_bool(OVF1));

    expr_ref preOVF2(m), OVF2(m), OVF(m);
    m_simp.mk_eq(m.mk_app(m_bv_util.get_fid(), OP_BREDAND, biased_exp.get()), m_bv_util.mk_numeral(1, 1), preOVF2);
    m_simp.mk_and(SIGovf, preOVF2, OVF2);
    m_simp.mk_ite(OVF2, m_bv_util.mk_numeral(fu().fm().m_powers2.m1(ebits-2), ebits),
                        biased_exp,
                        biased_exp);
    m_simp.mk_or(OVF1, OVF2, OVF);
    
    SASSERT(is_well_sorted(m, OVF2));
    SASSERT(is_well_sorted(m, OVF));
    
    SASSERT(m.is_bool(OVF2));
    SASSERT(m.is_bool(OVF));
    dbg_decouple("fpa2bv_rnd_OVF2", OVF2);
    dbg_decouple("fpa2bv_rnd_OVF", OVF);

    // ExpRnd
    expr_ref top_exp(m), bot_exp(m);
    mk_top_exp(ebits, top_exp);
    mk_bot_exp(ebits, bot_exp);    

    expr_ref rm_is_to_zero(m), rm_zero_or_neg(m), rm_zero_or_pos(m);
    mk_is_rm(rm, BV_RM_TO_ZERO, rm_is_to_zero);
    m_simp.mk_or(rm_is_to_zero, rm_is_to_neg, rm_zero_or_neg);
    m_simp.mk_or(rm_is_to_zero, rm_is_to_pos, rm_zero_or_pos);

    expr_ref sgn_is_zero(m);
    m_simp.mk_eq(sgn, m_bv_util.mk_numeral(0, 1), sgn_is_zero);

    expr_ref max_sig(m), max_exp(m), inf_sig(m), inf_exp(m);
	max_sig = m_bv_util.mk_numeral(fu().fm().m_powers2.m1(sbits-1, false), sbits-1);
	max_exp = m_bv_util.mk_concat(m_bv_util.mk_numeral(fu().fm().m_powers2.m1(ebits-1, false), ebits-1),
                                  m_bv_util.mk_numeral(0, 1));
	inf_sig = m_bv_util.mk_numeral(0, sbits-1);
	inf_exp = top_exp;

    dbg_decouple("fpa2bv_rnd_max_exp", max_exp);

    expr_ref ovfl_exp(m), max_inf_exp_neg(m), max_inf_exp_pos(m), n_d_check(m), n_d_exp(m);
    m_simp.mk_ite(rm_zero_or_neg, max_exp, inf_exp, max_inf_exp_neg);
    m_simp.mk_ite(rm_zero_or_pos, max_exp, inf_exp, max_inf_exp_pos);
    m_simp.mk_ite(sgn_is_zero, max_inf_exp_neg, max_inf_exp_pos, ovfl_exp);
    m_simp.mk_eq(m_bv_util.mk_extract(sbits-1, sbits-1, sig), m_bv_util.mk_numeral(0, 1), n_d_check);
    m_simp.mk_ite(n_d_check, bot_exp /* denormal */, biased_exp, n_d_exp);
    m_simp.mk_ite(OVF, ovfl_exp, n_d_exp, exp);

    expr_ref max_inf_sig_neg(m), max_inf_sig_pos(m), ovfl_sig(m);
    m_simp.mk_ite(rm_zero_or_neg, max_sig, inf_sig, max_inf_sig_neg);
    m_simp.mk_ite(rm_zero_or_pos, max_sig, inf_sig, max_inf_sig_pos);
    m_simp.mk_ite(sgn_is_zero, max_inf_sig_neg, max_inf_sig_pos, ovfl_sig);
    m_simp.mk_ite(OVF, ovfl_sig, m_bv_util.mk_extract(sbits-2, 0, sig), sig);

    dbg_decouple("fpa2bv_rnd_sgn_final", sgn);
    dbg_decouple("fpa2bv_rnd_sig_final", sig);
    dbg_decouple("fpa2bv_rnd_exp_final", exp);

    expr_ref res_sgn(m), res_sig(m), res_exp(m);
    res_sgn = sgn;
	res_sig = sig;
	res_exp = exp;
	
	SASSERT(m_bv_util.get_bv_size(res_sgn) == 1);
	SASSERT(is_well_sorted(m, res_sgn));
    SASSERT(m_bv_util.get_bv_size(res_sig) == sbits-1);
	SASSERT(is_well_sorted(m, res_sig));
    SASSERT(m_bv_util.get_bv_size(res_exp) == ebits);
	SASSERT(is_well_sorted(m, res_exp));

	mk_triple(res_sgn, res_sig, res_exp, result);

    TRACE("fpa2bv_round", tout << "ROUND = " << mk_ismt2_pp(result, m) << std::endl; );
}


fpa2bv_model_converter * fpa2bv_converter::mk_model_converter() {
    return alloc(fpa2bv_model_converter, m, m_const2bv, m_rm_const2bv);
}

void fpa2bv_model_converter::display(std::ostream & out) {
    out << "(fpa2bv-model-converter";
    for (obj_map<func_decl, expr*>::iterator it = m_const2bv.begin();
         it != m_const2bv.end();
         it++) {
             const symbol & n = it->m_key->get_name();
             out << "\n  (" << n << " ";
             unsigned indent = n.size() + 4;
             out << mk_ismt2_pp(it->m_value, m, indent) << ")";
    }
	for (obj_map<func_decl, expr*>::iterator it = m_rm_const2bv.begin();
         it != m_rm_const2bv.end();
         it++) {
             const symbol & n = it->m_key->get_name();
             out << "\n  (" << n << " ";
             unsigned indent = n.size() + 4;
             out << mk_ismt2_pp(it->m_value, m, indent) << ")";
    }
    out << ")" << std::endl;
}

model_converter * fpa2bv_model_converter::translate(ast_translation & translator) {
    fpa2bv_model_converter * res = alloc(fpa2bv_model_converter, translator.to());
    for (obj_map<func_decl, expr*>::iterator it = m_const2bv.begin();
         it != m_const2bv.end();
         it++)
        res->m_const2bv.insert(translator(it->m_key), translator(it->m_value));    
	for (obj_map<func_decl, expr*>::iterator it = m_rm_const2bv.begin();
         it != m_rm_const2bv.end();
         it++)
        res->m_rm_const2bv.insert(translator(it->m_key), translator(it->m_value));    
    return res;
}

void fpa2bv_model_converter::convert(model * bv_mdl, model * float_mdl) {
    float_util fu(m);
    bv_util bu(m);
    mpf fp_val;
    unsynch_mpz_manager & mpzm = fu.fm().mpz_manager();
    unsynch_mpq_manager & mpqm = fu.fm().mpq_manager();

    TRACE("fpa2bv_mc", tout << "BV Model: " << std::endl;
        for (unsigned i = 0 ; i < bv_mdl->get_num_constants(); i++)
            tout << bv_mdl->get_constant(i)->get_name() << " --> " << 
                mk_ismt2_pp(bv_mdl->get_const_interp(bv_mdl->get_constant(i)), m) << std::endl;
        );


    for (obj_map<func_decl, expr*>::iterator it = m_const2bv.begin();
         it != m_const2bv.end();
         it++) 
    {
        func_decl * var = it->m_key;
        app * a = to_app(it->m_value);
        SASSERT(fu.is_float(var->get_range()));
        SASSERT(var->get_range()->get_num_parameters() == 2);
        
        unsigned ebits = fu.get_ebits(var->get_range());
        unsigned sbits = fu.get_sbits(var->get_range());

        expr * sgn = bv_mdl->get_const_interp(to_app(a->get_arg(0))->get_decl());
        expr * sig = bv_mdl->get_const_interp(to_app(a->get_arg(1))->get_decl());
        expr * exp = bv_mdl->get_const_interp(to_app(a->get_arg(2))->get_decl());

        if (!sgn && !sig && !exp)
            continue;
        
        unsigned sgn_sz = bu.get_bv_size(m.get_sort(a->get_arg(0)));
        unsigned sig_sz = bu.get_bv_size(m.get_sort(a->get_arg(1))) - 1;
        unsigned exp_sz = bu.get_bv_size(m.get_sort(a->get_arg(2)));

        rational sgn_q(0), sig_q(0), exp_q(0);

        if (sgn) bu.is_numeral(sgn, sgn_q, sgn_sz);
        if (sig) bu.is_numeral(sig, sig_q, sig_sz);
        if (exp) bu.is_numeral(exp, exp_q, exp_sz);        

        // un-bias exponent
        rational exp_unbiased_q;
        exp_unbiased_q = exp_q - fu.fm().m_powers2.m1(ebits-1);
        
        mpz sig_z; mpf_exp_t exp_z;
        mpzm.set(sig_z, sig_q.to_mpq().numerator());
        exp_z = mpzm.get_int64(exp_unbiased_q.to_mpq().numerator());

        TRACE("fpa2bv_mc", tout << var->get_name() << " == [" << sgn_q.to_string() << " " << 
            mpzm.to_string(sig_z) << " " << exp_z << "(" << exp_q.to_string() << ")]" << std::endl; );
        
        fu.fm().set(fp_val, ebits, sbits, !mpqm.is_zero(sgn_q.to_mpq()), sig_z, exp_z);

        float_mdl->register_decl(var, fu.mk_value(fp_val));

        mpzm.del(sig_z);
    }

	for (obj_map<func_decl, expr*>::iterator it = m_rm_const2bv.begin();
         it != m_rm_const2bv.end();
         it++) 
    {
		func_decl * var = it->m_key;
        app * a = to_app(it->m_value);
        SASSERT(fu.is_rm(var->get_range()));        
		rational val(0);
		unsigned sz = 0;
		if (a && bu.is_numeral(a, val, sz)) {
			TRACE("fpa2bv_mc", tout << var->get_name() << " == " << val.to_string() << std::endl; );
			SASSERT(val.is_uint64());
			switch (val.get_uint64())
			{
			case BV_RM_TIES_TO_AWAY: float_mdl->register_decl(var, fu.mk_round_nearest_ties_to_away()); break;
			case BV_RM_TIES_TO_EVEN: float_mdl->register_decl(var, fu.mk_round_nearest_ties_to_even()); break;
			case BV_RM_TO_NEGATIVE: float_mdl->register_decl(var, fu.mk_round_toward_negative()); break;
			case BV_RM_TO_POSITIVE: float_mdl->register_decl(var, fu.mk_round_toward_positive()); break;
			case BV_RM_TO_ZERO: 
			default: float_mdl->register_decl(var, fu.mk_round_toward_zero());
			}				
		}		
	}

    fu.fm().del(fp_val);
}
