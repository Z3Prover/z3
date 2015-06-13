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
#include<math.h>

#include"ast_smt2_pp.h"
#include"well_sorted.h"
#include"th_rewriter.h"

#include"fpa2bv_converter.h"

#define BVULT(X,Y,R) { expr_ref bvult_eq(m), bvult_not(m); m_simp.mk_eq(X, Y, bvult_eq); m_simp.mk_not(bvult_eq, bvult_not); expr_ref t(m); t = m_bv_util.mk_ule(X,Y); m_simp.mk_and(t, bvult_not, R); }
#define BVSLT(X,Y,R) { expr_ref bvslt_eq(m), bvslt_not(m); m_simp.mk_eq(X, Y, bvslt_eq); m_simp.mk_not(bvslt_eq, bvslt_not); expr_ref t(m); t = m_bv_util.mk_sle(X,Y); m_simp.mk_and(t, bvslt_not, R); }

fpa2bv_converter::fpa2bv_converter(ast_manager & m) : 
    m(m),
    m_simp(m),
    m_util(m),
    m_bv_util(m),
    m_arith_util(m),
    m_mpf_manager(m_util.fm()),
    m_mpz_manager(m_mpf_manager.mpz_manager()),    
    m_hi_fp_unspecified(true),
    m_extra_assertions(m) {
    m_plugin = static_cast<fpa_decl_plugin*>(m.get_plugin(m.mk_family_id("fpa")));
}

fpa2bv_converter::~fpa2bv_converter() {
    reset();
}

void fpa2bv_converter::mk_eq(expr * a, expr * b, expr_ref & result) {
    SASSERT(is_app_of(a, m_plugin->get_family_id(), OP_FPA_FP));
    SASSERT(is_app_of(b, m_plugin->get_family_id(), OP_FPA_FP));

    TRACE("fpa2bv", tout << "mk_eq a=" << mk_ismt2_pp(a, m) << std::endl;
                    tout << "mk_eq b=" << mk_ismt2_pp(b, m) << std::endl;);

    expr_ref eq_sgn(m), eq_exp(m), eq_sig(m);
    m_simp.mk_eq(to_app(a)->get_arg(0), to_app(b)->get_arg(0), eq_sgn);
    m_simp.mk_eq(to_app(a)->get_arg(1), to_app(b)->get_arg(1), eq_exp);
    m_simp.mk_eq(to_app(a)->get_arg(2), to_app(b)->get_arg(2), eq_sig);

    dbg_decouple("fpa2bv_eq_sgn", eq_sgn);
    dbg_decouple("fpa2bv_eq_exp", eq_exp);
    dbg_decouple("fpa2bv_eq_sig", eq_sig);

    expr_ref both_the_same(m);
    m_simp.mk_and(eq_sgn, eq_exp, eq_sig, both_the_same);
    dbg_decouple("fpa2bv_eq_both_the_same", both_the_same);

    // The SMT FPA theory asks for _one_ NaN value, but the bit-blasting
    // has many, like IEEE754. This encoding of equality makes it look like
    // a single NaN again. 
    expr_ref a_is_nan(m), b_is_nan(m), both_are_nan(m);    
    mk_is_nan(a, a_is_nan);
    mk_is_nan(b, b_is_nan);
    m_simp.mk_and(a_is_nan, b_is_nan, both_are_nan);
    dbg_decouple("fpa2bv_eq_both_are_nan", both_are_nan);

    m_simp.mk_or(both_are_nan, both_the_same, result);
}

void fpa2bv_converter::mk_ite(expr * c, expr * t, expr * f, expr_ref & result) {
    SASSERT(is_app_of(t, m_plugin->get_family_id(), OP_FPA_FP));
    SASSERT(is_app_of(f, m_plugin->get_family_id(), OP_FPA_FP));

    expr *t_sgn, *t_sig, *t_exp;
    expr *f_sgn, *f_sig, *f_exp;
    split_fp(t, t_sgn, t_exp, t_sig);
    split_fp(f, f_sgn, f_exp, f_sig);

    expr_ref sgn(m), s(m), e(m);
    m_simp.mk_ite(c, t_sgn, f_sgn, sgn);
    m_simp.mk_ite(c, t_sig, f_sig, s);
    m_simp.mk_ite(c, t_exp, f_exp, e);

    mk_fp(sgn, e, s, result);
}

void fpa2bv_converter::mk_distinct(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    // Note: in SMT there is only one NaN, so multiple of them are considered 
    // equal, thus (distinct NaN NaN) is false, even if the two NaNs have 
    // different bitwise representations (see also mk_eq).
    result = m.mk_true();
    for (unsigned i = 0; i < num; i++) {
        for (unsigned j = i+1; j < num; j++) {
            expr_ref eq(m);
            mk_eq(args[i], args[j], eq);
            m_simp.mk_and(result, m.mk_not(eq), result);
        }
    }    
}

void fpa2bv_converter::mk_numeral(func_decl * f, unsigned num, expr * const * args, expr_ref & result) { 
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
            mk_ninf(f, result);
        else
            mk_pinf(f, result);
    }
    else {
        expr_ref bv_sgn(m), bv_sig(m), e(m), biased_exp(m);
        bv_sgn = m_bv_util.mk_numeral( (sign) ? 1 : 0, 1);
        bv_sig = m_bv_util.mk_numeral(rational(sig), sbits-1);
        e = m_bv_util.mk_numeral(exp, ebits);

        mk_bias(e, biased_exp);

        mk_fp(bv_sgn, biased_exp, bv_sig, result);
        TRACE("fpa2bv_dbg", tout << "value of [" << sign << " " << m_mpz_manager.to_string(sig) << " " << exp << "] is " 
              << mk_ismt2_pp(result, m) << std::endl;);
                        
    }
}

app * fpa2bv_converter::mk_fresh_const(char const * prefix, unsigned sz) {
    return m.mk_fresh_const(prefix, m_bv_util.mk_sort(sz));
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

        app_ref sgn(m), s(m), e(m);

#ifdef Z3DEBUG
        std::string p("fpa2bv");
        std::string name = f->get_name().str();

        sgn = mk_fresh_const((p + "_sgn_" + name).c_str(), 1);
        s = mk_fresh_const((p + "_sig_" + name).c_str(), sbits - 1);
        e = mk_fresh_const((p + "_exp_" + name).c_str(), ebits);        
#else
        app_ref bv(m);
        unsigned bv_sz = 1 + ebits + (sbits - 1);
        bv = mk_fresh_const(0, bv_sz);

        sgn = m_bv_util.mk_extract(bv_sz - 1, bv_sz - 1, bv);
        e = m_bv_util.mk_extract(bv_sz - 2, sbits - 1, bv);
        s = m_bv_util.mk_extract(sbits - 2, 0, bv);

        SASSERT(m_bv_util.get_bv_size(sgn) == 1);
        SASSERT(m_bv_util.get_bv_size(s) == sbits-1);
        SASSERT(m_bv_util.get_bv_size(e) == ebits);
#endif
        
        mk_fp(sgn, e, s, result);

        m_const2bv.insert(f, result);
        m.inc_ref(f);
        m.inc_ref(result);        
    }
}

void fpa2bv_converter::mk_var(unsigned base_inx, sort * srt, expr_ref & result) {
    SASSERT(is_float(srt));
    unsigned ebits = m_util.get_ebits(srt);
    unsigned sbits = m_util.get_sbits(srt);
        
    expr_ref sgn(m), s(m), e(m);    

    sgn = m.mk_var(base_inx, m_bv_util.mk_sort(1));
    s   = m.mk_var(base_inx + 1, m_bv_util.mk_sort(sbits-1));
    e   = m.mk_var(base_inx + 2, m_bv_util.mk_sort(ebits));

    mk_fp(sgn, e, s, result);
}

void fpa2bv_converter::mk_uninterpreted_function(func_decl * f, unsigned num, expr * const * args, expr_ref & result)
{
    TRACE("fpa2bv_dbg", tout << "UF: " << mk_ismt2_pp(f, m) << std::endl; );
    SASSERT(f->get_arity() == num);

    expr_ref_buffer new_args(m);

    for (unsigned i = 0; i < num ; i ++)
    if (is_float(args[i]))
    {
        expr * sgn, * sig, * exp;
        split_fp(args[i], sgn, exp, sig);
        new_args.push_back(sgn);
        new_args.push_back(sig);
        new_args.push_back(exp);
    }
    else
        new_args.push_back(args[i]);

    func_decl * fd;    
    func_decl_triple fd3;
    if (m_uf2bvuf.find(f, fd)) {
        result = m.mk_app(fd, new_args.size(), new_args.c_ptr());
    }
    else if (m_uf23bvuf.find(f, fd3))
    {
        expr_ref a_sgn(m), a_sig(m), a_exp(m);
        a_sgn = m.mk_app(fd3.f_sgn, new_args.size(), new_args.c_ptr());
        a_sig = m.mk_app(fd3.f_sig, new_args.size(), new_args.c_ptr());
        a_exp = m.mk_app(fd3.f_exp, new_args.size(), new_args.c_ptr());            
        mk_fp(a_sgn, a_exp, a_sig, result);
    }
    else {
        sort_ref_buffer new_domain(m);
    
        for (unsigned i = 0; i < f->get_arity() ; i ++)
            if (is_float(f->get_domain()[i]))
            {
                new_domain.push_back(m_bv_util.mk_sort(1));            
                new_domain.push_back(m_bv_util.mk_sort(m_util.get_sbits(f->get_domain()[i])-1));
                new_domain.push_back(m_bv_util.mk_sort(m_util.get_ebits(f->get_domain()[i])));                                
            }
            else
                new_domain.push_back(f->get_domain()[i]);

        if (!is_float(f->get_range()))
        {
            func_decl * fbv = m.mk_func_decl(f->get_name(), new_domain.size(), new_domain.c_ptr(), f->get_range(), *f->get_info());
            TRACE("fpa2bv_dbg", tout << "New UF func_decl : " << mk_ismt2_pp(fbv, m) << std::endl; );
            m_uf2bvuf.insert(f, fbv);
            m.inc_ref(f);
            m.inc_ref(fbv);
            result = m.mk_app(fbv, new_args.size(), new_args.c_ptr());
        }
        else
        {
            string_buffer<> name_buffer;
            name_buffer.reset(); name_buffer << f->get_name() << ".sgn";        
            func_decl * f_sgn = m.mk_func_decl(symbol(name_buffer.c_str()), new_domain.size(), new_domain.c_ptr(), m_bv_util.mk_sort(1));
            name_buffer.reset(); name_buffer << f->get_name() << ".sig";
            func_decl * f_sig = m.mk_func_decl(symbol(name_buffer.c_str()), new_domain.size(), new_domain.c_ptr(), m_bv_util.mk_sort(m_util.get_sbits(f->get_range())-1));
            name_buffer.reset(); name_buffer << f->get_name() << ".exp";
            func_decl * f_exp = m.mk_func_decl(symbol(name_buffer.c_str()), new_domain.size(), new_domain.c_ptr(), m_bv_util.mk_sort(m_util.get_ebits(f->get_range())));
            expr_ref a_sgn(m), a_sig(m), a_exp(m);
            a_sgn = m.mk_app(f_sgn, new_args.size(), new_args.c_ptr());
            a_sig = m.mk_app(f_sig, new_args.size(), new_args.c_ptr());
            a_exp = m.mk_app(f_exp, new_args.size(), new_args.c_ptr());            
            TRACE("fpa2bv_dbg", tout << "New UF func_decls : " << std::endl;
                                tout << mk_ismt2_pp(f_sgn, m) << std::endl;
                                tout << mk_ismt2_pp(f_sig, m) << std::endl;
                                tout << mk_ismt2_pp(f_exp, m) << std::endl; );
            m_uf23bvuf.insert(f, func_decl_triple(f_sgn, f_sig, f_exp));
            m.inc_ref(f);
            m.inc_ref(f_sgn);
            m.inc_ref(f_sig);
            m.inc_ref(f_exp);
            mk_fp(a_sgn, a_exp, a_sig, result);
        }               
    }    

    TRACE("fpa2bv_dbg", tout << "UF result: " << mk_ismt2_pp(result, m) << std::endl; );

    SASSERT(is_well_sorted(m, result));
}

void fpa2bv_converter::mk_rm_const(func_decl * f, expr_ref & result) {
    SASSERT(f->get_family_id() == null_family_id);
    SASSERT(f->get_arity() == 0);
    expr * r;
    if (m_rm_const2bv.find(f, r)) {
        result = r;
    }
    else {
        SASSERT(is_rm(f->get_range()));

        result = m.mk_fresh_const(
            #ifdef Z3DEBUG
            "fpa2bv_rm"
            #else
            0
            #endif
            , m_bv_util.mk_sort(3));

        m_rm_const2bv.insert(f, result);
        m.inc_ref(f);
        m.inc_ref(result);

        expr_ref rcc(m);
        rcc = bu().mk_ule(result, bu().mk_numeral(4, 3));
        m_extra_assertions.push_back(rcc);
    }
}

void fpa2bv_converter::mk_pinf(func_decl * f, expr_ref & result) {
    sort * srt = f->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);
    expr_ref top_exp(m);
    mk_top_exp(ebits, top_exp);
    mk_fp(m_bv_util.mk_numeral(0, 1),
          top_exp,
          m_bv_util.mk_numeral(0, sbits-1),
          result);
}

void fpa2bv_converter::mk_ninf(func_decl * f, expr_ref & result) {
    sort * srt = f->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);
    expr_ref top_exp(m);
    mk_top_exp(ebits, top_exp);
    mk_fp(m_bv_util.mk_numeral(1, 1),
          top_exp,
          m_bv_util.mk_numeral(0, sbits-1),
          result);
}

void fpa2bv_converter::mk_nan(func_decl * f, expr_ref & result) {
    sort * srt = f->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);
    expr_ref top_exp(m);
    mk_top_exp(ebits, top_exp);
    mk_fp(m_bv_util.mk_numeral(0, 1),
          top_exp,
          m_bv_util.mk_numeral(1, sbits-1),          
          result);
}

void fpa2bv_converter::mk_nzero(func_decl *f, expr_ref & result) {
    sort * srt = f->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);
    expr_ref bot_exp(m);
    mk_bot_exp(ebits, bot_exp);
    mk_fp(m_bv_util.mk_numeral(1, 1),
          bot_exp,
          m_bv_util.mk_numeral(0, sbits - 1),
          result);
}

void fpa2bv_converter::mk_pzero(func_decl *f, expr_ref & result) {
    sort * srt = f->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);
    expr_ref bot_exp(m);
    mk_bot_exp(ebits, bot_exp);
    mk_fp(m_bv_util.mk_numeral(0, 1),
          bot_exp,
          m_bv_util.mk_numeral(0, sbits-1),
          result);
}

void fpa2bv_converter::mk_one(func_decl *f, expr_ref sign, expr_ref & result) {
    sort * srt = f->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);
    mk_fp(sign,
          m_bv_util.mk_numeral(fu().fm().m_powers2.m1(ebits-1), ebits),
          m_bv_util.mk_numeral(0, sbits-1),
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
    expr_ref cap(m), cap_le_delta(m);
    cap = m_bv_util.mk_numeral(sbits+2, ebits);
    cap_le_delta = m_bv_util.mk_ule(cap, exp_delta);
    m_simp.mk_ite(cap_le_delta, cap, exp_delta, exp_delta);

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
    expr_ref sticky_eq(m), nil_sbit3(m), one_sbit3(m); 
    nil_sbit3 = m_bv_util.mk_numeral(0, sbits+3);
    one_sbit3 = m_bv_util.mk_numeral(1, sbits+3);
    m_simp.mk_eq(sticky_raw, nil_sbit3, sticky_eq);
    m_simp.mk_ite(sticky_eq, nil_sbit3, one_sbit3, sticky);
    SASSERT(is_well_sorted(m, sticky));
    
    expr * or_args[2] = { shifted_d_sig, sticky };
    shifted_d_sig = m_bv_util.mk_bv_or(2, or_args);
    SASSERT(is_well_sorted(m, shifted_d_sig));

    expr_ref eq_sgn(m);
    m_simp.mk_eq(c_sgn, d_sgn, eq_sgn);

    // dbg_decouple("fpa2bv_add_eq_sgn", eq_sgn);
    TRACE("fpa2bv_add_core", tout << "EQ_SGN = " << mk_ismt2_pp(eq_sgn, m) << std::endl; );    
    
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
    expr_ref not_c_sgn(m), not_d_sgn(m), not_sign_bv(m);
    not_c_sgn = m_bv_util.mk_bv_not(c_sgn);
    not_d_sgn = m_bv_util.mk_bv_not(d_sgn);
    not_sign_bv = m_bv_util.mk_bv_not(sign_bv);
    res_sgn_c1 = m.mk_app(bvfid, OP_BAND, not_c_sgn, d_sgn, sign_bv);
    res_sgn_c2 = m.mk_app(bvfid, OP_BAND, c_sgn, not_d_sgn, not_sign_bv);
    res_sgn_c3 = m.mk_app(bvfid, OP_BAND, c_sgn, d_sgn);
    expr * res_sgn_or_args[3] = { res_sgn_c1, res_sgn_c2, res_sgn_c3 };   
    res_sgn = m_bv_util.mk_bv_or(3, res_sgn_or_args);

    expr_ref res_sig_eq(m), sig_abs(m), one_1(m);
    one_1 = m_bv_util.mk_numeral(1, 1);
    m_simp.mk_eq(sign_bv, one_1, res_sig_eq);
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
    
    expr_ref rm_is_to_neg(m), signs_and(m), signs_xor(m), v4_and(m), rm_and_xor(m), neg_cond(m);
    m_simp.mk_and(x_is_zero, y_is_zero, c4);
    m_simp.mk_and(x_is_neg, y_is_neg, signs_and);
    m_simp.mk_xor(x_is_neg, y_is_neg, signs_xor);
    mk_is_rm(rm, BV_RM_TO_NEGATIVE, rm_is_to_neg);
    m_simp.mk_and(rm_is_to_neg, signs_xor, rm_and_xor);
    m_simp.mk_or(signs_and, rm_and_xor, neg_cond);
    mk_ite(neg_cond, nzero, pzero, v4);
    m_simp.mk_and(x_is_neg, y_is_neg, v4_and);
    mk_ite(v4_and, x, v4, v4);

    c5 = x_is_zero;
    v5 = y;

    c6 = y_is_zero;
    v6 = x;

    // Actual addition.
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());    

    expr_ref a_sgn(m), a_sig(m), a_exp(m), a_lz(m), b_sgn(m), b_sig(m), b_exp(m), b_lz(m);
    unpack(x, a_sgn, a_sig, a_exp, a_lz, false);
    unpack(y, b_sgn, b_sig, b_exp, b_lz, false);

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

    expr_ref is_zero_sig(m), nil_sbit4(m);
    nil_sbit4 = m_bv_util.mk_numeral(0, sbits+4);
    m_simp.mk_eq(res_sig, nil_sbit4, is_zero_sig);

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
    mk_neg(f, 1, &args[2], t);
    expr * nargs[3] = { args[0], args[1], t };
    mk_add(f, 3, nargs, result);
}

void fpa2bv_converter::mk_neg(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    expr * sgn, * s, * e;
    split_fp(args[0], sgn, e, s);
    expr_ref c(m), nsgn(m);
    mk_is_nan(args[0], c);    
    nsgn = m_bv_util.mk_bv_not(sgn);    
    expr_ref r_sgn(m);
    m_simp.mk_ite(c, sgn, nsgn, r_sgn);
    mk_fp(r_sgn, e, s, result);
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
    mk_ninf(f, ninf);
    mk_pinf(f, pinf);

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
    unsigned sbits = m_util.get_sbits(f->get_range());    

    expr_ref a_sgn(m), a_sig(m), a_exp(m), a_lz(m), b_sgn(m), b_sig(m), b_exp(m), b_lz(m);
    unpack(x, a_sgn, a_sig, a_exp, a_lz, true);
    unpack(y, b_sgn, b_sig, b_exp, b_lz, true);

    dbg_decouple("fpa2bv_mul_a_sig", a_sig);
    dbg_decouple("fpa2bv_mul_a_exp", a_exp);
    dbg_decouple("fpa2bv_mul_b_sig", b_sig);
    dbg_decouple("fpa2bv_mul_b_exp", b_exp);

    expr_ref a_lz_ext(m), b_lz_ext(m);
    a_lz_ext = m_bv_util.mk_zero_extend(2, a_lz);
    b_lz_ext = m_bv_util.mk_zero_extend(2, b_lz);

    dbg_decouple("fpa2bv_mul_lz_a", a_lz);
    dbg_decouple("fpa2bv_mul_lz_b", b_lz);    

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

    res_exp = m_bv_util.mk_bv_add(
                m_bv_util.mk_bv_sub(a_exp_ext, a_lz_ext),
                m_bv_util.mk_bv_sub(b_exp_ext, b_lz_ext));

    expr_ref product(m);
    product = m_bv_util.mk_bv_mul(a_sig_ext, b_sig_ext);

    dbg_decouple("fpa2bv_mul_product", product);

    SASSERT(m_bv_util.get_bv_size(product) == 2*sbits);

    expr_ref h_p(m), l_p(m), rbits(m);
    h_p = m_bv_util.mk_extract(2*sbits-1, sbits, product);
    l_p = m_bv_util.mk_extract(sbits-1, 0, product);
    
    if (sbits >= 4) {
        expr_ref sticky(m);
        sticky = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, m_bv_util.mk_extract(sbits-4, 0, product));            
        rbits = m_bv_util.mk_concat(m_bv_util.mk_extract(sbits-1, sbits-3, product), sticky);
    }
    else
        rbits = m_bv_util.mk_concat(l_p, m_bv_util.mk_numeral(0, 4 - sbits));
    
    SASSERT(m_bv_util.get_bv_size(rbits) == 4);
    res_sig = m_bv_util.mk_concat(h_p, rbits);

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
    mk_ninf(f, ninf);
    mk_pinf(f, pinf);        

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

    expr_ref c1(m), c2(m), c3(m), c4(m), c5(m), c6(m), c7(m);
    expr_ref v1(m), v2(m), v3(m), v4(m), v5(m), v6(m), v7(m), v8(m);

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

    // (y is 0) -> if (x is 0) then NaN else inf with xor sign. 
    c6 = y_is_zero;    
    expr_ref sgn_inf(m);
    mk_ite(signs_xor, ninf, pinf, sgn_inf);
    mk_ite(x_is_zero, nan, sgn_inf, v6);

    // (x is 0) -> result is zero with sgn = x.sgn^y.sgn
    // This is a special case to avoid problems with the unpacking of zero.
    c7 = x_is_zero;    
    mk_ite(signs_xor, nzero, pzero, v7);

    // else comes the actual division.
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());
    SASSERT(ebits <= sbits);

    expr_ref a_sgn(m), a_sig(m), a_exp(m), a_lz(m), b_sgn(m), b_sig(m), b_exp(m), b_lz(m);
    unpack(x, a_sgn, a_sig, a_exp, a_lz, true);
    unpack(y, b_sgn, b_sig, b_exp, b_lz, true);
    
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

    expr_ref a_lz_ext(m), b_lz_ext(m);
    a_lz_ext = m_bv_util.mk_zero_extend(2, a_lz);
    b_lz_ext = m_bv_util.mk_zero_extend(2, b_lz);

    res_exp = m_bv_util.mk_bv_sub(
            m_bv_util.mk_bv_sub(a_exp_ext, a_lz_ext),
            m_bv_util.mk_bv_sub(b_exp_ext, b_lz_ext));

    expr_ref quotient(m);
    quotient = m.mk_app(m_bv_util.get_fid(), OP_BUDIV, a_sig_ext, b_sig_ext);

    dbg_decouple("fpa2bv_div_quotient", quotient);

    SASSERT(m_bv_util.get_bv_size(quotient) == (sbits + sbits + extra_bits));    

    expr_ref sticky(m);
    sticky = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, m_bv_util.mk_extract(extra_bits-2, 0, quotient));
    res_sig = m_bv_util.mk_concat(m_bv_util.mk_extract(extra_bits+sbits+1, extra_bits-1, quotient), sticky);

    SASSERT(m_bv_util.get_bv_size(res_sig) == (sbits + 4));

    expr_ref res_sig_lz(m);
    mk_leading_zeros(res_sig, sbits + 4, res_sig_lz);
    dbg_decouple("fpa2bv_div_res_sig_lz", res_sig_lz);    
    expr_ref res_sig_shift_amount(m);
    res_sig_shift_amount = m_bv_util.mk_bv_sub(res_sig_lz, m_bv_util.mk_numeral(1, sbits + 4));
    dbg_decouple("fpa2bv_div_res_sig_shift_amount", res_sig_shift_amount);
    expr_ref shift_cond(m);
    shift_cond = m_bv_util.mk_ule(res_sig_lz, m_bv_util.mk_numeral(1, sbits + 4));
    m_simp.mk_ite(shift_cond, res_sig, m_bv_util.mk_bv_shl(res_sig, res_sig_shift_amount), res_sig);
    m_simp.mk_ite(shift_cond, res_exp, m_bv_util.mk_bv_sub(res_exp, m_bv_util.mk_extract(ebits+1, 0, res_sig_shift_amount)), res_exp);
    
    round(f->get_range(), rm, res_sgn, res_sig, res_exp, v8);

    // And finally, we tie them together.    
    mk_ite(c7, v7, v8, result);
    mk_ite(c6, v6, result, result);
    mk_ite(c5, v5, result, result);
    mk_ite(c4, v4, result, result);
    mk_ite(c3, v3, result, result);
    mk_ite(c2, v2, result, result);
    mk_ite(c1, v1, result, result);

    SASSERT(is_well_sorted(m, result));

    TRACE("fpa2bv_div", tout << "DIV = " << mk_ismt2_pp(result, m) << std::endl; );
}

void fpa2bv_converter::mk_rem(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
    
    // Remainder is always exact, so there is no rounding mode.
    expr_ref x(m), y(m);
    x = args[0];
    y = args[1];

    expr_ref nan(m), nzero(m), pzero(m), ninf(m), pinf(m);
    mk_nan(f, nan);
    mk_nzero(f, nzero); 
    mk_pzero(f, pzero);
    mk_ninf(f, ninf);
    mk_pinf(f, pinf);        

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

    // (y is 0) -> NaN.
    c4 = y_is_zero;
    v4 = nan;

    // (x is 0) -> x
    c5 = x_is_zero;
    v5 = pzero;
        
    // else the actual remainder.
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());    

    expr_ref a_sgn(m), a_sig(m), a_exp(m), a_lz(m);
    expr_ref b_sgn(m), b_sig(m), b_exp(m), b_lz(m);
    unpack(x, a_sgn, a_sig, a_exp, a_lz, true);
    unpack(y, b_sgn, b_sig, b_exp, b_lz, true);
    
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
    
    // CMW: Actual rounding is not necessary here, this is 
    // just convenience to get rid of the extra bits.
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

    expr_ref result_is_zero(m), zeros(m);
    mk_is_zero(result, result_is_zero);
    mk_ite(x_is_pos, pzero, nzero, zeros);
    mk_ite(result_is_zero, zeros, result, result);

    SASSERT(is_well_sorted(m, result));

    TRACE("fpa2bv_rem", tout << "REM = " << mk_ismt2_pp(result, m) << std::endl; );
}

void fpa2bv_converter::mk_abs(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    expr * sgn, * s, * e;
    split_fp(args[0], sgn, e, s);
    mk_fp(m_bv_util.mk_numeral(0, 1), e, s, result);
}

void fpa2bv_converter::mk_min(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
    
    expr * x = args[0], * y = args[1];

    expr * x_sgn, * x_sig, * x_exp;
    expr * y_sgn, * y_sig, * y_exp;
    split_fp(x, x_sgn, x_exp, x_sig);
    split_fp(y, y_sgn, y_exp, y_sig);

    expr_ref x_is_nan(m), y_is_nan(m), x_is_zero(m), y_is_zero(m), both_zero(m), pzero(m);
    mk_is_zero(x, x_is_zero);
    mk_is_zero(y, y_is_zero);
    m_simp.mk_and(x_is_zero, y_is_zero, both_zero);
    mk_is_nan(x, x_is_nan);    
    mk_is_nan(y, y_is_nan);
    mk_pzero(f, pzero);

    expr_ref sgn_diff(m);
    sgn_diff = m.mk_not(m.mk_eq(x_sgn, y_sgn));

    expr_ref lt(m);
    mk_float_lt(f, num, args, lt);
    
    result = y;
    mk_ite(lt, x, result, result);
    mk_ite(both_zero, y, result, result);
    mk_ite(m.mk_and(both_zero, sgn_diff), pzero, result, result); // min(-0.0, +0.0) = min(+0.0, -0.0) = +0.0
    mk_ite(y_is_nan, x, result, result);
    mk_ite(x_is_nan, y, result, result);

    SASSERT(is_well_sorted(m, result));
}

void fpa2bv_converter::mk_max(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);

    expr * x = args[0], *y = args[1];

    expr * x_sgn, *x_sig, *x_exp;
    expr * y_sgn, *y_sig, *y_exp;
    split_fp(x, x_sgn, x_exp, x_sig);
    split_fp(y, y_sgn, y_exp, y_sig);

    expr_ref x_is_nan(m), y_is_nan(m), x_is_zero(m), y_is_zero(m), both_zero(m), pzero(m);    
    mk_is_zero(x, x_is_zero);
    mk_is_zero(y, y_is_zero);
    m_simp.mk_and(x_is_zero, y_is_zero, both_zero);
    mk_is_nan(x, x_is_nan);
    mk_is_nan(y, y_is_nan);
    mk_pzero(f, pzero);

    expr_ref sgn_diff(m);
    sgn_diff = m.mk_not(m.mk_eq(x_sgn, y_sgn));

    expr_ref gt(m);
    mk_float_gt(f, num, args, gt);

    result = y;
    mk_ite(gt, x, result, result);
    mk_ite(both_zero, y, result, result);    
    mk_ite(m.mk_and(both_zero, sgn_diff), pzero, result, result); // max(-0.0, +0.0) = max(+0.0, -0.0) = +0.0
    mk_ite(y_is_nan, x, result, result);
    mk_ite(x_is_nan, y, result, result);

    SASSERT(is_well_sorted(m, result));
}

void fpa2bv_converter::mk_fma(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
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
    mk_ninf(f, ninf);
    mk_pinf(f, pinf);

    expr_ref x_is_nan(m), x_is_zero(m), x_is_pos(m), x_is_neg(m), x_is_inf(m);
    expr_ref y_is_nan(m), y_is_zero(m), y_is_pos(m), y_is_neg(m), y_is_inf(m);
    expr_ref z_is_nan(m), z_is_zero(m), z_is_pos(m), z_is_neg(m), z_is_inf(m);
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
    mk_is_nan(z, z_is_nan);
    mk_is_zero(z, z_is_zero);
    mk_is_pos(z, z_is_pos);
    mk_is_neg(z, z_is_neg);
    mk_is_inf(z, z_is_inf);

    expr_ref rm_is_to_neg(m);
    mk_is_rm(rm, BV_RM_TO_NEGATIVE, rm_is_to_neg);

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

    expr_ref c1(m), c2(m), c3(m), c4(m), c5(m), c6(m), c7(m);
    expr_ref v1(m), v2(m), v3(m), v4(m), v5(m), v6(m), v7(m), v8(m);

    expr_ref inf_xor(m), inf_cond(m);
    m_simp.mk_xor(x_is_neg, y_is_neg, inf_xor);
    m_simp.mk_xor(inf_xor, z_is_neg, inf_xor);
    m_simp.mk_and(z_is_inf, inf_xor, inf_cond);

    // (x is NaN) || (y is NaN) || (z is Nan) -> NaN
    m_simp.mk_or(x_is_nan, y_is_nan, z_is_nan, c1);
    v1 = nan;
    
    // (x is +oo) -> if (y is 0) then NaN else inf with y's sign.
    mk_is_pinf(x, c2);
    expr_ref y_sgn_inf(m), inf_or(m);
    mk_ite(y_is_pos, pinf, ninf, y_sgn_inf);
    m_simp.mk_or(y_is_zero, inf_cond, inf_or);
    mk_ite(inf_or, nan, y_sgn_inf, v2);
                
    // (y is +oo) -> if (x is 0) then NaN else inf with x's sign.
    mk_is_pinf(y, c3);
    expr_ref x_sgn_inf(m);
    mk_ite(x_is_pos, pinf, ninf, x_sgn_inf);
    m_simp.mk_or(x_is_zero, inf_cond, inf_or);
    mk_ite(inf_or, nan, x_sgn_inf, v3);
    
    // (x is -oo) -> if (y is 0) then NaN else inf with -y's sign.    
    mk_is_ninf(x, c4);
    expr_ref neg_y_sgn_inf(m);
    mk_ite(y_is_pos, ninf, pinf, neg_y_sgn_inf);
    m_simp.mk_or(y_is_zero, inf_cond, inf_or);
    mk_ite(inf_or, nan, neg_y_sgn_inf, v4);

    // (y is -oo) -> if (x is 0) then NaN else inf with -x's sign.    
    mk_is_ninf(y, c5);
    expr_ref neg_x_sgn_inf(m);
    mk_ite(x_is_pos, ninf, pinf, neg_x_sgn_inf);
    m_simp.mk_or(x_is_zero, inf_cond, inf_or);
    mk_ite(inf_or, nan, neg_x_sgn_inf, v5);

    // z is +-INF -> z.
    mk_is_inf(z, c6);
    v6 = z;

    // (x is 0) || (y is 0) -> z
    m_simp.mk_or(x_is_zero, y_is_zero, c7);
    expr_ref ite_c(m);
    m_simp.mk_and(z_is_zero, m.mk_not(rm_is_to_neg), ite_c);
    mk_ite(ite_c, pzero, z, v7);
    
    // else comes the fused multiplication.
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());

    expr_ref a_sgn(m), a_sig(m), a_exp(m), a_lz(m);
    expr_ref b_sgn(m), b_sig(m), b_exp(m), b_lz(m);
    expr_ref c_sgn(m), c_sig(m), c_exp(m), c_lz(m);
    unpack(x, a_sgn, a_sig, a_exp, a_lz, true);
    unpack(y, b_sgn, b_sig, b_exp, b_lz, true);
    unpack(z, c_sgn, c_sig, c_exp, c_lz, true);    

    expr_ref a_lz_ext(m), b_lz_ext(m), c_lz_ext(m);
    a_lz_ext = m_bv_util.mk_zero_extend(2, a_lz);
    b_lz_ext = m_bv_util.mk_zero_extend(2, b_lz);
    c_lz_ext = m_bv_util.mk_zero_extend(2, c_lz);

    expr_ref a_sig_ext(m), b_sig_ext(m);
    a_sig_ext = m_bv_util.mk_zero_extend(sbits, a_sig);
    b_sig_ext = m_bv_util.mk_zero_extend(sbits, b_sig);    

    expr_ref a_exp_ext(m), b_exp_ext(m), c_exp_ext(m);
    a_exp_ext = m_bv_util.mk_sign_extend(2, a_exp);
    b_exp_ext = m_bv_util.mk_sign_extend(2, b_exp);
    c_exp_ext = m_bv_util.mk_sign_extend(2, c_exp);    

    dbg_decouple("fpa2bv_fma_a_sig", a_sig_ext);
    dbg_decouple("fpa2bv_fma_b_sig", b_sig_ext);
    dbg_decouple("fpa2bv_fma_c_sig", c_sig);
    dbg_decouple("fpa2bv_fma_a_exp", a_exp_ext);
    dbg_decouple("fpa2bv_fma_b_exp", b_exp_ext);
    dbg_decouple("fpa2bv_fma_c_exp", c_exp_ext);
    dbg_decouple("fpa2bv_fma_a_lz", a_lz_ext);
    dbg_decouple("fpa2bv_fma_b_lz", b_lz_ext);
    dbg_decouple("fpa2bv_fma_c_lz", c_lz_ext);

    expr_ref mul_sgn(m), mul_sig(m), mul_exp(m);
    expr * signs[2] = { a_sgn, b_sgn };

    mul_sgn = m_bv_util.mk_bv_xor(2, signs);
    dbg_decouple("fpa2bv_fma_mul_sgn", mul_sgn);

    mul_exp = m_bv_util.mk_bv_add(m_bv_util.mk_bv_sub(a_exp_ext, a_lz_ext),
                                  m_bv_util.mk_bv_sub(b_exp_ext, b_lz_ext));
    dbg_decouple("fpa2bv_fma_mul_exp", mul_exp);
    
    mul_sig = m_bv_util.mk_bv_mul(a_sig_ext, b_sig_ext);
    dbg_decouple("fpa2bv_fma_mul_sig", mul_sig);

    SASSERT(m_bv_util.get_bv_size(mul_sig) == 2*sbits);
    SASSERT(m_bv_util.get_bv_size(mul_exp) == ebits + 2);

    // The product has the form [-1][0].[2*sbits - 2].
    
    // Extend c
    c_sig = m_bv_util.mk_zero_extend(1, m_bv_util.mk_concat(c_sig, m_bv_util.mk_numeral(0, sbits-1)));
    c_exp_ext = m_bv_util.mk_bv_sub(c_exp_ext, c_lz_ext);

    SASSERT(m_bv_util.get_bv_size(mul_sig) == 2 * sbits);
    SASSERT(m_bv_util.get_bv_size(c_sig) == 2 * sbits);

    expr_ref swap_cond(m);
    swap_cond = m_bv_util.mk_sle(mul_exp, c_exp_ext);
    SASSERT(is_well_sorted(m, swap_cond));
    dbg_decouple("fpa2bv_fma_swap_cond", swap_cond);

    expr_ref e_sgn(m), e_sig(m), e_exp(m), f_sgn(m), f_sig(m), f_exp(m);
    m_simp.mk_ite(swap_cond, c_sgn, mul_sgn, e_sgn);
    m_simp.mk_ite(swap_cond, c_sig, mul_sig, e_sig); // has 2 * sbits
    m_simp.mk_ite(swap_cond, c_exp_ext, mul_exp, e_exp); // has ebits + 2
    m_simp.mk_ite(swap_cond, mul_sgn, c_sgn, f_sgn);
    m_simp.mk_ite(swap_cond, mul_sig, c_sig, f_sig); // has 2 * sbits
    m_simp.mk_ite(swap_cond, mul_exp, c_exp_ext, f_exp); // has ebits + 2        

    SASSERT(is_well_sorted(m, e_sgn));
    SASSERT(is_well_sorted(m, e_sig));
    SASSERT(is_well_sorted(m, e_exp));
    SASSERT(is_well_sorted(m, f_sgn));
    SASSERT(is_well_sorted(m, f_sig));
    SASSERT(is_well_sorted(m, f_exp));

    SASSERT(m_bv_util.get_bv_size(e_sig) == 2 * sbits);
    SASSERT(m_bv_util.get_bv_size(f_sig) == 2 * sbits);
    SASSERT(m_bv_util.get_bv_size(e_exp) == ebits + 2);
    SASSERT(m_bv_util.get_bv_size(f_exp) == ebits + 2);

    expr_ref res_sgn(m), res_sig(m), res_exp(m);
    
    expr_ref exp_delta(m);
    exp_delta = m_bv_util.mk_bv_sub(e_exp, f_exp);
    dbg_decouple("fpa2bv_fma_add_exp_delta", exp_delta);

    // cap the delta    
    expr_ref cap(m), cap_le_delta(m);
    cap = m_bv_util.mk_numeral(2*sbits, ebits+2);
    cap_le_delta = m_bv_util.mk_ule(cap, exp_delta);
    m_simp.mk_ite(cap_le_delta, cap, exp_delta, exp_delta);
    SASSERT(m_bv_util.get_bv_size(exp_delta) == ebits+2);
    SASSERT(is_well_sorted(m, exp_delta));
    dbg_decouple("fpa2bv_fma_add_exp_delta_capped", exp_delta);
    
    // Alignment shift with sticky bit computation.
    expr_ref shifted_big(m), shifted_f_sig(m), sticky_raw(m);
    shifted_big = m_bv_util.mk_bv_lshr(
                    m_bv_util.mk_concat(f_sig, m_bv_util.mk_numeral(0, sbits)), 
                    m_bv_util.mk_zero_extend((3*sbits)-(ebits+2), exp_delta));
    shifted_f_sig = m_bv_util.mk_extract(3*sbits-1, sbits, shifted_big);
    sticky_raw = m_bv_util.mk_extract(sbits-1, 0, shifted_big); 
    SASSERT(m_bv_util.get_bv_size(shifted_f_sig) == 2 * sbits);
    SASSERT(is_well_sorted(m, shifted_f_sig));    
       
    expr_ref sticky(m); 
    sticky = m_bv_util.mk_zero_extend(2*sbits-1, m.mk_app(m_bv_util.get_fid(), OP_BREDOR, sticky_raw.get()));
    SASSERT(is_well_sorted(m, sticky));
    dbg_decouple("fpa2bv_fma_f_sig_sticky_raw", sticky_raw);
    dbg_decouple("fpa2bv_fma_f_sig_sticky", sticky);
    
    expr * or_args[2] = { shifted_f_sig, sticky };
    shifted_f_sig = m_bv_util.mk_bv_or(2, or_args);
    SASSERT(is_well_sorted(m, shifted_f_sig));

    // Significant addition.
    // Two extra bits for catching the overflow.
    e_sig = m_bv_util.mk_zero_extend(2, e_sig);
    shifted_f_sig = m_bv_util.mk_zero_extend(2, shifted_f_sig);

    expr_ref eq_sgn(m);
    m_simp.mk_eq(e_sgn, f_sgn, eq_sgn);

    SASSERT(m_bv_util.get_bv_size(e_sig) == 2*sbits + 2);
    SASSERT(m_bv_util.get_bv_size(shifted_f_sig) == 2*sbits + 2);

    dbg_decouple("fpa2bv_fma_add_e_sig", e_sig);
    dbg_decouple("fpa2bv_fma_add_shifted_f_sig", shifted_f_sig);

    expr_ref sum(m);
    m_simp.mk_ite(eq_sgn, 
                  m_bv_util.mk_bv_add(e_sig, shifted_f_sig),
                  m_bv_util.mk_bv_sub(e_sig, shifted_f_sig),                  
                  sum);

    SASSERT(is_well_sorted(m, sum));

    dbg_decouple("fpa2bv_fma_add_sum", sum);

    expr_ref sign_bv(m), n_sum(m);
    sign_bv = m_bv_util.mk_extract(2*sbits+1, 2*sbits+1, sum);        
    n_sum = m_bv_util.mk_bv_neg(sum);

    expr_ref res_sig_eq(m), sig_abs(m), one_1(m);
    one_1 = m_bv_util.mk_numeral(1, 1);
    m_simp.mk_eq(sign_bv, one_1, res_sig_eq);
    m_simp.mk_ite(res_sig_eq, n_sum, sum, sig_abs);
    dbg_decouple("fpa2bv_fma_add_sign_bv", sign_bv);    
    dbg_decouple("fpa2bv_fma_add_n_sum", n_sum);         
    dbg_decouple("fpa2bv_fma_add_sig_abs", sig_abs);

    res_exp = e_exp;
    
    // Result could overflow into 4.xxx ...

    family_id bvfid = m_bv_util.get_fid();
    expr_ref res_sgn_c1(m), res_sgn_c2(m), res_sgn_c3(m);
    expr_ref not_e_sgn(m), not_f_sgn(m), not_sign_bv(m);
    not_e_sgn = m_bv_util.mk_bv_not(e_sgn);
    not_f_sgn = m_bv_util.mk_bv_not(f_sgn);
    not_sign_bv = m_bv_util.mk_bv_not(sign_bv);
    res_sgn_c1 = m.mk_app(bvfid, OP_BAND, not_e_sgn, f_sgn, sign_bv);
    res_sgn_c2 = m.mk_app(bvfid, OP_BAND, e_sgn, not_f_sgn, not_sign_bv);
    res_sgn_c3 = m.mk_app(bvfid, OP_BAND, e_sgn, f_sgn);
    expr * res_sgn_or_args[3] = { res_sgn_c1, res_sgn_c2, res_sgn_c3 };   
    res_sgn = m_bv_util.mk_bv_or(3, res_sgn_or_args);

    if (sbits > 5) {
        sticky_raw = m_bv_util.mk_extract(sbits - 5, 0, sig_abs);
        sticky = m_bv_util.mk_zero_extend(sbits + 3, m.mk_app(bvfid, OP_BREDOR, sticky_raw.get()));
        expr * res_or_args[2] = { m_bv_util.mk_extract(2 * sbits - 1, sbits - 4, sig_abs), sticky };
        res_sig = m_bv_util.mk_bv_or(2, res_or_args);
    }
    else {
        unsigned too_short = 6 - sbits;
        sig_abs = m_bv_util.mk_concat(sig_abs, m_bv_util.mk_numeral(0, too_short));
        res_sig = m_bv_util.mk_extract(sbits + 3, 0, sig_abs);
    }
    dbg_decouple("fpa2bv_fma_add_sum_sticky", sticky);
    SASSERT(m_bv_util.get_bv_size(res_sig) == sbits + 4);

    expr_ref is_zero_sig(m), nil_sbits4(m);
    nil_sbits4 = m_bv_util.mk_numeral(0, sbits+4);
    m_simp.mk_eq(res_sig, nil_sbits4, is_zero_sig);
    SASSERT(is_well_sorted(m, is_zero_sig));

    dbg_decouple("fpa2bv_fma_is_zero_sig", is_zero_sig);
    
    expr_ref zero_case(m);
    mk_ite(rm_is_to_neg, nzero, pzero, zero_case);

    expr_ref rounded(m);
    round(f->get_range(), rm, res_sgn, res_sig, res_exp, rounded);

    mk_ite(is_zero_sig, zero_case, rounded, v8);

    // And finally, we tie them together.
    mk_ite(c7, v7, v8, result);
    mk_ite(c6, v6, result, result);
    mk_ite(c5, v5, result, result);
    mk_ite(c4, v4, result, result);
    mk_ite(c3, v3, result, result);
    mk_ite(c2, v2, result, result);
    mk_ite(c1, v1, result, result);

    SASSERT(is_well_sorted(m, result));

    TRACE("fpa2bv_fma_", tout << "FMA = " << mk_ismt2_pp(result, m) << std::endl; );
}

void fpa2bv_converter::mk_sqrt(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
    
    expr_ref rm(m), x(m);
    rm = args[0];
    x = args[1];    

    expr_ref nan(m), nzero(m), pzero(m), ninf(m), pinf(m);
    mk_nan(f, nan);
    mk_nzero(f, nzero); 
    mk_pzero(f, pzero);
    mk_ninf(f, ninf);
    mk_pinf(f, pinf);

    expr_ref x_is_nan(m), x_is_zero(m), x_is_pos(m), x_is_inf(m);    
    mk_is_nan(x, x_is_nan);
    mk_is_zero(x, x_is_zero);
    mk_is_pos(x, x_is_pos);
    mk_is_inf(x, x_is_inf);
    
    expr_ref zero1(m), one1(m);
    zero1 = m_bv_util.mk_numeral(0, 1);
    one1 = m_bv_util.mk_numeral(1, 1);
    
    expr_ref c1(m), c2(m), c3(m), c4(m), c5(m), c6(m);
    expr_ref v1(m), v2(m), v3(m), v4(m), v5(m), v6(m), v7(m);

    // (x is NaN) -> NaN
    c1 = x_is_nan;
    v1 = x;
    
    // (x is +oo) -> +oo
    mk_is_pinf(x, c2);
    v2 = x;
                
    // (x is +-0) -> +-0
    mk_is_zero(x, c3);
    v3 = x;
    
    // (x < 0) -> NaN
    mk_is_neg(x, c4);
    v4 = nan;

    // else comes the actual square root.
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());

    expr_ref a_sgn(m), a_sig(m), a_exp(m), a_lz(m);
    unpack(x, a_sgn, a_sig, a_exp, a_lz, true);

    dbg_decouple("fpa2bv_sqrt_sig", a_sig);
    dbg_decouple("fpa2bv_sqrt_exp", a_exp);

    SASSERT(m_bv_util.get_bv_size(a_sig) == sbits);
    SASSERT(m_bv_util.get_bv_size(a_exp) == ebits);

    expr_ref res_sgn(m), res_sig(m), res_exp(m);

    res_sgn = zero1;

    expr_ref real_exp(m);
    real_exp = m_bv_util.mk_bv_sub(m_bv_util.mk_sign_extend(1, a_exp), m_bv_util.mk_zero_extend(1, a_lz));
    res_exp = m_bv_util.mk_sign_extend(2, m_bv_util.mk_extract(ebits, 1, real_exp));

    expr_ref e_is_odd(m);
    e_is_odd = m.mk_eq(m_bv_util.mk_extract(0, 0, real_exp), one1);

    dbg_decouple("fpa2bv_sqrt_e_is_odd", e_is_odd);
    dbg_decouple("fpa2bv_sqrt_real_exp", real_exp);

    expr_ref sig_prime(m);    
    m_simp.mk_ite(e_is_odd, m_bv_util.mk_concat(a_sig, zero1),
                            m_bv_util.mk_concat(zero1, a_sig), 
                            sig_prime);
    SASSERT(m_bv_util.get_bv_size(sig_prime) == sbits+1);        
    dbg_decouple("fpa2bv_sqrt_sig_prime", sig_prime);

    // This is algorithm 10.2 in the Handbook of Floating-Point Arithmetic
    expr_ref Q(m), R(m), S(m), T(m);

    const mpz & p2 = fu().fm().m_powers2(sbits+3);
    Q = m_bv_util.mk_numeral(p2, sbits+5);
    R = m_bv_util.mk_bv_sub(m_bv_util.mk_concat(sig_prime, m_bv_util.mk_numeral(0, 4)), Q);
    S = Q;

    for (unsigned i = 0; i < sbits + 3; i++) {
        dbg_decouple("fpa2bv_sqrt_Q", Q);
        dbg_decouple("fpa2bv_sqrt_R", R);

        S = m_bv_util.mk_concat(zero1, m_bv_util.mk_extract(sbits+4, 1, S));
        
        expr_ref twoQ_plus_S(m);
        twoQ_plus_S = m_bv_util.mk_bv_add(m_bv_util.mk_concat(Q, zero1), m_bv_util.mk_concat(zero1, S));
        T = m_bv_util.mk_bv_sub(m_bv_util.mk_concat(R, zero1), twoQ_plus_S);

        dbg_decouple("fpa2bv_sqrt_T", T);

        SASSERT(m_bv_util.get_bv_size(Q) == sbits + 5);
        SASSERT(m_bv_util.get_bv_size(R) == sbits + 5);
        SASSERT(m_bv_util.get_bv_size(S) == sbits + 5);
        SASSERT(m_bv_util.get_bv_size(T) == sbits + 6);

        expr_ref t_lt_0(m);
        m_simp.mk_eq(m_bv_util.mk_extract(sbits+5, sbits+5, T), one1, t_lt_0);        
        
        expr * or_args[2] = { Q, S };

        m_simp.mk_ite(t_lt_0, Q,
                              m_bv_util.mk_bv_or(2, or_args),
                              Q);
        m_simp.mk_ite(t_lt_0, m_bv_util.mk_concat(m_bv_util.mk_extract(sbits+3, 0, R), zero1), 
                              m_bv_util.mk_extract(sbits+4, 0, T), 
                              R);
    }

    expr_ref is_exact(m);
    m_simp.mk_eq(R, m_bv_util.mk_numeral(0, sbits+5), is_exact);
    dbg_decouple("fpa2bv_sqrt_is_exact", is_exact);    

    expr_ref rest(m), last(m), q_is_odd(m), rest_ext(m);
    last = m_bv_util.mk_extract(0, 0, Q);
    rest = m_bv_util.mk_extract(sbits+3, 1, Q);
    dbg_decouple("fpa2bv_sqrt_last", last);
    dbg_decouple("fpa2bv_sqrt_rest", rest);
    rest_ext = m_bv_util.mk_zero_extend(1, rest);
    expr_ref sticky(m);
    m_simp.mk_ite(is_exact, m_bv_util.mk_zero_extend(sbits+3, last),
                            m_bv_util.mk_numeral(1, sbits+4),
                            sticky);
    expr * or_args[2] = { rest_ext, sticky };
    res_sig = m_bv_util.mk_bv_or(2, or_args);

    SASSERT(m_bv_util.get_bv_size(res_sig) == sbits + 4);

    expr_ref rounded(m);
    round(f->get_range(), rm, res_sgn, res_sig, res_exp, rounded);    
    v5 = rounded;

    // And finally, we tie them together.
    mk_ite(c4, v4, v5, result);
    mk_ite(c3, v3, result, result);
    mk_ite(c2, v2, result, result);
    mk_ite(c1, v1, result, result);

    SASSERT(is_well_sorted(m, result));
}

void fpa2bv_converter::mk_round_to_integral(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);
    
    expr_ref rm(m), x(m);
    rm = args[0];
    x = args[1];

    expr_ref rm_is_rta(m), rm_is_rte(m), rm_is_rtp(m), rm_is_rtn(m), rm_is_rtz(m);
    mk_is_rm(rm, BV_RM_TIES_TO_AWAY, rm_is_rta);
    mk_is_rm(rm, BV_RM_TIES_TO_EVEN, rm_is_rte);
    mk_is_rm(rm, BV_RM_TO_POSITIVE, rm_is_rtp);
    mk_is_rm(rm, BV_RM_TO_NEGATIVE, rm_is_rtn);
    mk_is_rm(rm, BV_RM_TO_ZERO, rm_is_rtz);

    expr_ref nan(m), nzero(m), pzero(m), ninf(m), pinf(m);
    mk_nan(f, nan);
    mk_nzero(f, nzero); 
    mk_pzero(f, pzero);

    expr_ref x_is_zero(m), x_is_pos(m), x_is_neg(m);
    mk_is_zero(x, x_is_zero);
    mk_is_pos(x, x_is_pos);
    mk_is_neg(x, x_is_neg);
    
    dbg_decouple("fpa2bv_r2i_x_is_zero", x_is_zero);
    dbg_decouple("fpa2bv_r2i_x_is_pos", x_is_pos);    

    expr_ref c1(m), c2(m), c3(m), c4(m), c5(m);
    expr_ref v1(m), v2(m), v3(m), v4(m), v5(m), v6(m);

    // (x is NaN) -> NaN
    mk_is_nan(x, c1);
    v1 = nan;

    // (x is +-oo) -> x
    mk_is_inf(x, c2);
    v2 = x;

    // (x is +-0) -> x ; -0.0 -> -0.0, says IEEE754, Sec 5.9.
    mk_is_zero(x, c3);
    v3 = x;
    

    expr_ref one_1(m), zero_1(m);
    one_1 = m_bv_util.mk_numeral(1, 1);
    zero_1 = m_bv_util.mk_numeral(0, 1);
    
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());    

    expr_ref a_sgn(m), a_sig(m), a_exp(m), a_lz(m);
    unpack(x, a_sgn, a_sig, a_exp, a_lz, true);
    
    dbg_decouple("fpa2bv_r2i_unpacked_sig", a_sig);
    dbg_decouple("fpa2bv_r2i_unpacked_exp", a_exp);

    expr_ref xzero(m);
    mk_ite(m.mk_eq(a_sgn, one_1), nzero, pzero, xzero);

    // exponent < 0 -> 0/1
    expr_ref exp_lt_zero(m), exp_h(m);
    exp_h = m_bv_util.mk_extract(ebits-1, ebits-1, a_exp);    
    m_simp.mk_eq(exp_h, one_1, exp_lt_zero);
    dbg_decouple("fpa2bv_r2i_exp_lt_zero", exp_lt_zero);
    c4 = exp_lt_zero;

    expr_ref pone(m), none(m), xone(m), c421(m), c422(m), c423(m), t1(m), t2(m), tie(m), v42(m), exp_lt_m1(m);
    mk_one(f, zero_1, pone);
    mk_one(f, one_1, none);
    mk_ite(m.mk_eq(a_sgn, one_1), none, pone, xone);
    
    m_simp.mk_eq(a_sig, m_bv_util.mk_numeral(fu().fm().m_powers2(sbits-1), sbits), t1);
    m_simp.mk_eq(a_exp, m_bv_util.mk_numeral(-1, ebits), t2);
    m_simp.mk_and(t1, t2, tie);    
    dbg_decouple("fpa2bv_r2i_c42_tie", tie);

    m_simp.mk_and(tie, rm_is_rte, c421);
    m_simp.mk_and(tie, rm_is_rta, c422);
    c423 = m_bv_util.mk_sle(a_exp, m_bv_util.mk_numeral(-2, ebits));

    dbg_decouple("fpa2bv_r2i_c421", c421);
    dbg_decouple("fpa2bv_r2i_c422", c422);
    dbg_decouple("fpa2bv_r2i_c423", c423);

    v42 = xone;
    mk_ite(c423, xzero, v42, v42);
    mk_ite(c422, xone, v42, v42);
    mk_ite(c421, xzero, v42, v42);
    
    expr_ref v4_rtn(m), v4_rtp(m);
    mk_ite(x_is_neg, nzero, pone, v4_rtp);
    mk_ite(x_is_neg, none, pzero, v4_rtn);

    mk_ite(rm_is_rtp, v4_rtp, v42, v4);
    mk_ite(rm_is_rtn, v4_rtn, v4, v4);
    mk_ite(rm_is_rtz, xzero, v4, v4);

    SASSERT(is_well_sorted(m, v4));
    
    // exponent >= sbits-1
    expr_ref exp_is_large(m);
    exp_is_large = m_bv_util.mk_sle(m_bv_util.mk_numeral(sbits-1, ebits), a_exp);
    dbg_decouple("fpa2bv_r2i_exp_is_large", exp_is_large);
    c5 = exp_is_large;
    v5 = x;

    // Actual conversion with rounding.    
    // x.exponent >= 0 && x.exponent < x.sbits - 1

    expr_ref res_sgn(m), res_sig(m), res_exp(m);
    res_sgn = a_sgn;
    res_exp = a_exp;

    expr_ref shift(m), rshift(m), div(m), rem(m);
    shift = m_bv_util.mk_bv_sub(m_bv_util.mk_numeral(sbits - 1, sbits + 1),
                                m_bv_util.mk_sign_extend(sbits - ebits + 1, a_exp));
    rshift = m_bv_util.mk_bv_sub(m_bv_util.mk_numeral(sbits, sbits + 1), shift);
    div = m_bv_util.mk_bv_lshr(m_bv_util.mk_zero_extend(1, a_sig), shift);
    rem = m_bv_util.mk_bv_lshr(m_bv_util.mk_bv_shl(m_bv_util.mk_zero_extend(1, a_sig), rshift), rshift);

    SASSERT(is_well_sorted(m, div));
    SASSERT(is_well_sorted(m, rem));
    SASSERT(m_bv_util.get_bv_size(div) == sbits + 1);
    SASSERT(m_bv_util.get_bv_size(rem) == sbits + 1);

    dbg_decouple("fpa2bv_r2i_shift", shift);
    dbg_decouple("fpa2bv_r2i_rshift", rshift);
    dbg_decouple("fpa2bv_r2i_div", div);
    dbg_decouple("fpa2bv_r2i_rem", rem);

    expr_ref div_p1(m);
    div_p1 = m_bv_util.mk_bv_add(div, m_bv_util.mk_numeral(1, sbits+1));

    expr_ref tie2(m), tie2_c(m), div_last(m), v51(m), rem_shl(m);
    rem_shl = m_bv_util.mk_concat(m_bv_util.mk_extract(sbits - 1, 0, rem), zero_1);
    m_simp.mk_eq(rem_shl,
                 m_bv_util.mk_bv_shl(m_bv_util.mk_numeral(1, sbits+1), shift),
                 tie2);    
    div_last = m_bv_util.mk_extract(0, 0, div);
    tie2_c = m.mk_or(m.mk_and(tie2,
                              m.mk_or(m.mk_and(rm_is_rte, m.mk_eq(div_last, one_1)),
                                      m.mk_and(rm_is_rta, m.mk_eq(div_last, zero_1)))),
                     m.mk_xor(m.mk_eq(a_sgn, one_1),
                              m_bv_util.mk_sle(m_bv_util.mk_bv_shl(m_bv_util.mk_numeral(1, sbits + 1), shift),
                                               rem_shl)));
    m_simp.mk_ite(tie2_c, div_p1, div, v51);

    dbg_decouple("fpa2bv_r2i_v51", v51);
    dbg_decouple("fpa2bv_r2i_tie2", tie2);

    SASSERT(is_well_sorted(m, tie2));
    SASSERT(is_well_sorted(m, tie2_c));
    SASSERT(is_well_sorted(m, v51));

    expr_ref c521(m), v52(m);
    m_simp.mk_not(m.mk_eq(rem, m_bv_util.mk_numeral(0, sbits+1)), c521);
    m_simp.mk_and(c521, m.mk_eq(res_sgn, zero_1), c521);
    m_simp.mk_ite(c521, div_p1, div, v52);

    expr_ref c531(m), v53(m);
    m_simp.mk_not(m.mk_eq(rem, m_bv_util.mk_numeral(0, sbits+1)), c531);
    m_simp.mk_and(c531, m.mk_eq(res_sgn, one_1), c531);
    m_simp.mk_ite(c531, div_p1, div, v53);

    expr_ref c51(m), c52(m), c53(m);
    c51 = m.mk_or(rm_is_rte, rm_is_rta);
    c52 = rm_is_rtp;
    c53 = rm_is_rtn;
    
    res_sig = div;
    m_simp.mk_ite(c53, v53, res_sig, res_sig);
    m_simp.mk_ite(c52, v52, res_sig, res_sig);
    m_simp.mk_ite(c51, v51, res_sig, res_sig);
    res_sig = m_bv_util.mk_concat(res_sig, m_bv_util.mk_numeral(0, 3)); // rounding bits are all 0.
    
    SASSERT(m_bv_util.get_bv_size(res_exp) == ebits);
    SASSERT(m_bv_util.get_bv_size(shift) == sbits + 1);

    expr_ref e_shift(m);
    e_shift = (ebits + 2 <= sbits + 1) ? m_bv_util.mk_extract(ebits + 1, 0, shift) :
                                         m_bv_util.mk_sign_extend((ebits + 2) - (sbits + 1), shift);
    SASSERT(m_bv_util.get_bv_size(e_shift) == ebits + 2);
    res_exp = m_bv_util.mk_bv_add(m_bv_util.mk_zero_extend(2, res_exp), e_shift);

    SASSERT(m_bv_util.get_bv_size(res_sgn) == 1);
    SASSERT(m_bv_util.get_bv_size(res_sig) == sbits + 4);
    SASSERT(m_bv_util.get_bv_size(res_exp) == ebits + 2);

    // CMW: We use the rounder for normalization.
    round(f->get_range(), rm, res_sgn, res_sig, res_exp, v6); 

    // And finally, we tie them together.
    mk_ite(c5, v5, v6, result);
    mk_ite(c4, v4, result, result);
    mk_ite(c3, v3, result, result);
    mk_ite(c2, v2, result, result);
    mk_ite(c1, v1, result, result);

    SASSERT(is_well_sorted(m, result));

    TRACE("fpa2bv_round_to_integral", tout << "ROUND2INTEGRAL = " << mk_ismt2_pp(result, m) << std::endl; );
}

void fpa2bv_converter::mk_float_eq(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 2);

    expr * x = args[0], * y = args[1];

    TRACE("fpa2bv_float_eq", tout << "X = " << mk_ismt2_pp(x, m) << std::endl; 
                             tout << "Y = " << mk_ismt2_pp(y, m) << std::endl;);

    expr_ref c1(m), c2(m), x_is_nan(m), y_is_nan(m), x_is_zero(m), y_is_zero(m);
    mk_is_nan(x, x_is_nan);
    mk_is_nan(y, y_is_nan);
    m_simp.mk_or(x_is_nan, y_is_nan, c1);
    mk_is_zero(x, x_is_zero);
    mk_is_zero(y, y_is_zero);
    m_simp.mk_and(x_is_zero, y_is_zero, c2);

    expr * x_sgn, * x_sig, * x_exp;
    expr * y_sgn, * y_sig, * y_exp;
    split_fp(x, x_sgn, x_exp, x_sig);
    split_fp(y, y_sgn, y_exp, y_sig);
    
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

    TRACE("fpa2bv_float_eq", tout << "FLOAT_EQ = " << mk_ismt2_pp(result, m) << std::endl; );
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
    split_fp(x, x_sgn, x_exp, x_sig);
    split_fp(y, y_sgn, y_exp, y_sig);

    expr_ref c3(m), t3(m), t4(m), one_1(m), nil_1(m);
    one_1 = m_bv_util.mk_numeral(1, 1);
    nil_1 = m_bv_util.mk_numeral(0, 1);
    m_simp.mk_eq(x_sgn, one_1, c3);

    expr_ref y_sgn_eq_0(m), y_lt_x_exp(m), y_lt_x_sig(m), y_eq_x_exp(m), y_le_x_sig_exp(m), t3_or(m);
    m_simp.mk_eq(y_sgn, nil_1, y_sgn_eq_0);
    BVULT(y_exp, x_exp, y_lt_x_exp);
    BVULT(y_sig, x_sig, y_lt_x_sig);
    m_simp.mk_eq(y_exp, x_exp, y_eq_x_exp);
    m_simp.mk_and(y_eq_x_exp, y_lt_x_sig, y_le_x_sig_exp);
    m_simp.mk_or(y_lt_x_exp, y_le_x_sig_exp, t3_or);
    m_simp.mk_ite(y_sgn_eq_0, m.mk_true(), t3_or, t3);

    expr_ref y_sgn_eq_1(m), x_lt_y_exp(m), x_eq_y_exp(m), x_lt_y_sig(m), x_le_y_sig_exp(m), t4_or(m);
    m_simp.mk_eq(y_sgn, one_1, y_sgn_eq_1);
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

void fpa2bv_converter::mk_is_nan(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    mk_is_nan(args[0], result);
}

void fpa2bv_converter::mk_is_inf(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    mk_is_inf(args[0], result);
}

void fpa2bv_converter::mk_is_normal(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    mk_is_normal(args[0], result);
}

void fpa2bv_converter::mk_is_subnormal(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    mk_is_denormal(args[0], result);
}

void fpa2bv_converter::mk_is_negative(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    expr_ref t1(m), t2(m);
    mk_is_nan(args[0], t1);
    mk_is_neg(args[0], t2);
    result = m.mk_and(m.mk_not(t1), t2);
    TRACE("fpa2bv_is_negative", tout << "result = " << mk_ismt2_pp(result, m) << std::endl;);
}

void fpa2bv_converter::mk_is_positive(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    expr_ref t1(m), t2(m);
    mk_is_nan(args[0], t1);
    mk_is_pos(args[0], t2);
    result = m.mk_and(m.mk_not(t1), t2);    
}

void fpa2bv_converter::mk_to_fp(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    TRACE("fpa2bv_to_fp", for (unsigned i=0; i < num; i++)
                            tout << "arg" << i << " = " << mk_ismt2_pp(args[i], m) << std::endl; );

    if (num == 1 && 
        m_bv_util.is_bv(args[0])) {
        sort * s = f->get_range();
        unsigned to_sbits = m_util.get_sbits(s);
        unsigned to_ebits = m_util.get_ebits(s);

        expr * bv = args[0];
        int sz = m_bv_util.get_bv_size(bv);
        SASSERT((unsigned)sz == to_sbits + to_ebits);

        mk_fp(m_bv_util.mk_extract(sz - 1, sz - 1, bv),
              m_bv_util.mk_extract(sz - 2, sz - to_ebits - 1, bv),
              m_bv_util.mk_extract(sz - to_ebits - 2, 0, bv),
              result);
    }
    else if (num == 2 &&
             m_bv_util.is_bv(args[0]) &&
             m_bv_util.get_bv_size(args[0]) == 3 &&
             m_util.is_float(m.get_sort(args[1]))) {
        // rm + float -> float
        mk_to_fp_float(f, f->get_range(), args[0], args[1], result);
    }
    else if (num == 2 &&
             m_bv_util.is_bv(args[0]) &&
             m_bv_util.get_bv_size(args[0]) == 3 &&
             (m_arith_util.is_int(args[1]) || 
              m_arith_util.is_real(args[1]))) {
        // rm + real -> float
        mk_to_fp_real(f, f->get_range(), args[0], args[1], result);
    }
    else if (num == 2 &&
             m_bv_util.is_bv(args[0]) &&
             m_bv_util.get_bv_size(args[0]) == 3 &&
             m_bv_util.is_bv(args[1])) {
        // rm + signed bv -> float
        mk_to_fp_signed(f, num, args, result);
    }
    else if (num == 3 && 
             m_bv_util.is_bv(args[0]) && 
             m_bv_util.is_bv(args[1]) && 
             m_bv_util.is_bv(args[2])) { 
        // 3 BV -> float
        SASSERT(m_bv_util.get_bv_size(args[0]) == 1);
        SASSERT(m_util.get_ebits(f->get_range()) == m_bv_util.get_bv_size(args[1]));
        SASSERT(m_util.get_sbits(f->get_range()) == m_bv_util.get_bv_size(args[2])+1);        
        mk_fp(args[0], args[1], args[2], result);
    }
    else if (num == 3 &&
             m_bv_util.is_bv(args[0]) &&
             m_bv_util.get_bv_size(args[0]) == 3 &&
             m_arith_util.is_numeral(args[1]) &&
             m_arith_util.is_numeral(args[2]))
    {
        // rm + real + int -> float
        mk_to_fp_real_int(f, num, args, result);
    }    
    else
        UNREACHABLE();

    SASSERT(is_well_sorted(m, result)); 
}

void fpa2bv_converter::mk_to_fp_float(func_decl * f, sort * s, expr * rm, expr * x, expr_ref & result) {
    unsigned from_sbits = m_util.get_sbits(m.get_sort(x));
    unsigned from_ebits = m_util.get_ebits(m.get_sort(x));
    unsigned to_sbits = m_util.get_sbits(s);
    unsigned to_ebits = m_util.get_ebits(s);

    if (from_sbits == to_sbits && from_ebits == to_ebits)
        result = x;
    else {
        expr_ref c1(m), c2(m), c3(m), c4(m), c5(m);
        expr_ref v1(m), v2(m), v3(m), v4(m), v5(m), v6(m);
        expr_ref one1(m);

        one1 = m_bv_util.mk_numeral(1, 1);
        expr_ref ninf(m), pinf(m);
        mk_pinf(f, pinf);
        mk_ninf(f, ninf);

        // NaN -> NaN
        mk_is_nan(x, c1);
        mk_nan(f, v1);

        // +0 -> +0
        mk_is_pzero(x, c2);
        mk_pzero(f, v2);

        // -0 -> -0
        mk_is_nzero(x, c3);
        mk_nzero(f, v3);

        // +oo -> +oo
        mk_is_pinf(x, c4);
        v4 = pinf;

        // -oo -> -oo
        mk_is_ninf(x, c5);
        v5 = ninf;

        // otherwise: the actual conversion with rounding.            
        expr_ref sgn(m), sig(m), exp(m), lz(m);
        unpack(x, sgn, sig, exp, lz, true);

        dbg_decouple("fpa2bv_to_float_x_sgn", sgn);
        dbg_decouple("fpa2bv_to_float_x_sig", sig);
        dbg_decouple("fpa2bv_to_float_x_exp", exp);
        dbg_decouple("fpa2bv_to_float_lz", lz);

        expr_ref res_sgn(m), res_sig(m), res_exp(m);

        res_sgn = sgn;

        SASSERT(m_bv_util.get_bv_size(sgn) == 1);
        SASSERT(m_bv_util.get_bv_size(sig) == from_sbits);
        SASSERT(m_bv_util.get_bv_size(exp) == from_ebits);
        SASSERT(m_bv_util.get_bv_size(lz) == from_ebits);

        if (from_sbits < (to_sbits + 3)) {
            // make sure that sig has at least to_sbits + 3
            res_sig = m_bv_util.mk_concat(sig, m_bv_util.mk_numeral(0, to_sbits + 3 - from_sbits));
        }
        else if (from_sbits > (to_sbits + 3)) {
            // collapse the extra bits into a sticky bit.
            expr_ref sticky(m), low(m), high(m);
            high = m_bv_util.mk_extract(from_sbits - 1, from_sbits - to_sbits - 2, sig);
            SASSERT(m_bv_util.get_bv_size(high) == to_sbits + 2);
            low = m_bv_util.mk_extract(from_sbits - to_sbits - 3, 0, sig);            
            sticky = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, low.get());
            SASSERT(m_bv_util.get_bv_size(sticky) == 1);
            dbg_decouple("fpa2bv_to_float_sticky", sticky);
            res_sig = m_bv_util.mk_concat(high, sticky);            
            SASSERT(m_bv_util.get_bv_size(res_sig) == to_sbits + 3);
        }
        else
            res_sig = sig;

        res_sig = m_bv_util.mk_zero_extend(1, res_sig); // extra zero in the front for the rounder.
        unsigned sig_sz = m_bv_util.get_bv_size(res_sig);
        SASSERT(sig_sz == to_sbits + 4);

        expr_ref exponent_overflow(m), exponent_underflow(m);
        exponent_overflow = m.mk_false();
        exponent_underflow = m.mk_false();

        if (from_ebits < (to_ebits + 2)) {
            res_exp = m_bv_util.mk_sign_extend(to_ebits - from_ebits + 2, exp);

            // subtract lz for subnormal numbers.
            expr_ref lz_ext(m);
            lz_ext = m_bv_util.mk_zero_extend(to_ebits - from_ebits + 2, lz);
            res_exp = m_bv_util.mk_bv_sub(res_exp, lz_ext);
        }
        else if (from_ebits > (to_ebits + 2)) {            
            expr_ref lz_rest(m), lz_redor(m), lz_redor_bool(m);            
            lz_rest = m_bv_util.mk_extract(from_ebits - 1, to_ebits + 2, lz);
            lz_redor = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, lz_rest.get());
            m_simp.mk_eq(lz_redor, one1, lz_redor_bool);
            dbg_decouple("fpa2bv_to_float_exp_lz_redor", lz_redor);

            // subtract lz for subnormal numbers.
            expr_ref exp_sub_lz(m);
            exp_sub_lz = m_bv_util.mk_bv_sub(exp, lz);
            dbg_decouple("fpa2bv_to_float_exp_sub_lz", exp_sub_lz);

            expr_ref high(m), low(m), low_msb(m);
            expr_ref no_ovf(m), zero1(m);
            high = m_bv_util.mk_extract(from_ebits - 1, to_ebits + 2, exp_sub_lz);
            low = m_bv_util.mk_extract(to_ebits + 1, 0, exp_sub_lz);
            low_msb = m_bv_util.mk_extract(to_ebits + 1, to_ebits + 1, low);
            dbg_decouple("fpa2bv_to_float_exp_high", high);
            dbg_decouple("fpa2bv_to_float_exp_low", low);
            dbg_decouple("fpa2bv_to_float_exp_low_msb", low_msb);
            
            res_exp = low;

            expr_ref high_red_or(m), high_red_and(m);
            high_red_or = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, high.get());
            high_red_and = m.mk_app(m_bv_util.get_fid(), OP_BREDAND, high.get());

            expr_ref h_or_eq_0(m), h_and_eq_1(m), low_msb_is_one(m), low_msb_is_zero(m);
            zero1 = m_bv_util.mk_numeral(0, 1);
            m_simp.mk_eq(high_red_and, one1, h_and_eq_1);
            m_simp.mk_eq(high_red_or, zero1, h_or_eq_0);
            m_simp.mk_eq(low_msb, zero1, low_msb_is_zero);
            m_simp.mk_eq(low_msb, one1, low_msb_is_one);
            dbg_decouple("fpa2bv_to_float_exp_h_and_eq_1", h_and_eq_1);
            dbg_decouple("fpa2bv_to_float_exp_h_or_eq_0", h_or_eq_0);
            dbg_decouple("fpa2bv_to_float_exp_s_is_zero", low_msb_is_zero);
            dbg_decouple("fpa2bv_to_float_exp_s_is_one", low_msb_is_one);
            
            m_simp.mk_and(h_or_eq_0, low_msb_is_one, exponent_underflow);
            m_simp.mk_and(h_and_eq_1, low_msb_is_zero, exponent_overflow);
            m_simp.mk_or(exponent_overflow, lz_redor_bool, exponent_overflow);
            dbg_decouple("fpa2bv_to_float_exp_ovf", exponent_overflow);
            dbg_decouple("fpa2bv_to_float_exp_udf", exponent_underflow);

            // exponent underflow means that the result is the smallest 
            // representable float, rounded according to rm.            
            m_simp.mk_ite(exponent_underflow, 
                                m_bv_util.mk_concat(m_bv_util.mk_numeral(1, 1),
                                                    m_bv_util.mk_numeral(1, to_ebits+1)), 
                                res_exp, 
                                res_exp);
            m_simp.mk_ite(exponent_underflow, m_bv_util.mk_numeral(1, to_sbits+4), res_sig, res_sig);
        }
        else // from_ebits == (to_ebits + 2)
            res_exp = m_bv_util.mk_bv_sub(exp, lz);

        SASSERT(m_bv_util.get_bv_size(res_exp) == to_ebits + 2);
        SASSERT(is_well_sorted(m, res_exp));

        dbg_decouple("fpa2bv_to_float_res_sig", res_sig);
        dbg_decouple("fpa2bv_to_float_res_exp", res_exp);

        expr_ref rounded(m);
        expr_ref rm_e(rm, m);
        round(s, rm_e, res_sgn, res_sig, res_exp, rounded);

        expr_ref is_neg(m), sig_inf(m);
        m_simp.mk_eq(sgn, one1, is_neg);
        mk_ite(is_neg, ninf, pinf, sig_inf);

        mk_ite(exponent_overflow, sig_inf, rounded, v6);        

        // And finally, we tie them together.
        mk_ite(c5, v5, v6, result);
        mk_ite(c4, v4, result, result);
        mk_ite(c3, v3, result, result);
        mk_ite(c2, v2, result, result);
        mk_ite(c1, v1, result, result);
    }

    SASSERT(is_well_sorted(m, result));
}

void fpa2bv_converter::mk_to_fp_real(func_decl * f, sort * s, expr * rm, expr * x, expr_ref & result) {
    TRACE("fpa2bv_to_fp_real", tout << "rm: " << mk_ismt2_pp(rm, m) << std::endl << 
                                    "x: " << mk_ismt2_pp(x, m) << std::endl;);
    SASSERT(m_util.is_float(s));
    SASSERT(au().is_real(x) || au().is_int(x));

    unsigned ebits = m_util.get_ebits(s);
    unsigned sbits = m_util.get_sbits(s);

    if (m_bv_util.is_numeral(rm) && m_util.au().is_numeral(x)) {
        rational tmp_rat; unsigned sz;
        m_bv_util.is_numeral(to_expr(rm), tmp_rat, sz);
        SASSERT(tmp_rat.is_int32());
        SASSERT(sz == 3);
        BV_RM_VAL bv_rm = (BV_RM_VAL)tmp_rat.get_unsigned();

        mpf_rounding_mode mrm;
        switch (bv_rm) {
        case BV_RM_TIES_TO_AWAY: mrm = MPF_ROUND_NEAREST_TAWAY; break;
        case BV_RM_TIES_TO_EVEN: mrm = MPF_ROUND_NEAREST_TEVEN; break;
        case BV_RM_TO_NEGATIVE: mrm = MPF_ROUND_TOWARD_NEGATIVE; break;
        case BV_RM_TO_POSITIVE: mrm = MPF_ROUND_TOWARD_POSITIVE; break;
        case BV_RM_TO_ZERO: mrm = MPF_ROUND_TOWARD_ZERO; break;
        default: UNREACHABLE();
        }

        rational q;
        bool is_int;
        m_util.au().is_numeral(x, q, is_int);

        if (q.is_zero())
            return mk_pzero(f, result);
        else {
            scoped_mpf v(m_mpf_manager);
            m_util.fm().set(v, ebits, sbits, mrm, q.to_mpq());

            expr_ref sgn(m), sig(m), exp(m), unbiased_exp(m);
            sgn = m_bv_util.mk_numeral((m_util.fm().sgn(v)) ? 1 : 0, 1);
            sig = m_bv_util.mk_numeral(m_util.fm().sig(v), sbits - 1);
            unbiased_exp = m_bv_util.mk_numeral(m_util.fm().exp(v), ebits);
            mk_bias(unbiased_exp, exp);

            mk_fp(sgn, exp, sig, result);
        }
    }
    else if (m_util.au().is_numeral(x)) {
        rational q;
        bool is_int;
        m_util.au().is_numeral(x, q, is_int);

        if (m_util.au().is_zero(x))
            mk_pzero(f, result);
        else {
            expr_ref rm_nta(m), rm_nte(m), rm_tp(m), rm_tn(m), rm_tz(m);
            mk_is_rm(rm, BV_RM_TIES_TO_AWAY, rm_nta);
            mk_is_rm(rm, BV_RM_TIES_TO_EVEN, rm_nte);
            mk_is_rm(rm, BV_RM_TO_POSITIVE, rm_tp);
            mk_is_rm(rm, BV_RM_TO_NEGATIVE, rm_tn);
            mk_is_rm(rm, BV_RM_TO_ZERO, rm_tz);

            scoped_mpf v_nta(m_mpf_manager), v_nte(m_mpf_manager), v_tp(m_mpf_manager);
            scoped_mpf v_tn(m_mpf_manager), v_tz(m_mpf_manager);
            m_util.fm().set(v_nta, ebits, sbits, MPF_ROUND_NEAREST_TAWAY, q.to_mpq());
            m_util.fm().set(v_nte, ebits, sbits, MPF_ROUND_NEAREST_TEVEN, q.to_mpq());
            m_util.fm().set(v_tp, ebits, sbits, MPF_ROUND_TOWARD_POSITIVE, q.to_mpq());
            m_util.fm().set(v_tn, ebits, sbits, MPF_ROUND_TOWARD_NEGATIVE, q.to_mpq());
            m_util.fm().set(v_tz, ebits, sbits, MPF_ROUND_TOWARD_ZERO, q.to_mpq());

            expr_ref v1(m), v2(m), v3(m), v4(m);

            expr_ref sgn(m), sig(m), exp(m), unbiased_exp(m);
            sgn = m_bv_util.mk_numeral((m_util.fm().sgn(v_nta)) ? 1 : 0, 1);
            sig = m_bv_util.mk_numeral(m_util.fm().sig(v_nta), sbits - 1);
            unbiased_exp = m_bv_util.mk_numeral(m_util.fm().exp(v_nta), ebits);
            mk_bias(unbiased_exp, exp);
            mk_fp(sgn, exp, sig, v1);

            sgn = m_bv_util.mk_numeral((m_util.fm().sgn(v_nte)) ? 1 : 0, 1);
            sig = m_bv_util.mk_numeral(m_util.fm().sig(v_nte), sbits - 1);
            unbiased_exp = m_bv_util.mk_numeral(m_util.fm().exp(v_nte), ebits);
            mk_bias(unbiased_exp, exp);
            mk_fp(sgn, exp, sig, v2);

            sgn = m_bv_util.mk_numeral((m_util.fm().sgn(v_tp)) ? 1 : 0, 1);
            sig = m_bv_util.mk_numeral(m_util.fm().sig(v_tp), sbits - 1);
            unbiased_exp = m_bv_util.mk_numeral(m_util.fm().exp(v_tp), ebits);
            mk_bias(unbiased_exp, exp);
            mk_fp(sgn, exp, sig, v3);

            sgn = m_bv_util.mk_numeral((m_util.fm().sgn(v_tn)) ? 1 : 0, 1);
            sig = m_bv_util.mk_numeral(m_util.fm().sig(v_tn), sbits - 1);
            unbiased_exp = m_bv_util.mk_numeral(m_util.fm().exp(v_tn), ebits);
            mk_bias(unbiased_exp, exp);
            mk_fp(sgn, exp, sig, v4);

            sgn = m_bv_util.mk_numeral((m_util.fm().sgn(v_tp)) ? 1 : 0, 1);
            sig = m_bv_util.mk_numeral(m_util.fm().sig(v_tp), sbits - 1);
            unbiased_exp = m_bv_util.mk_numeral(m_util.fm().exp(v_tp), ebits);
            mk_bias(unbiased_exp, exp);

            mk_fp(sgn, exp, sig, result);
            mk_ite(rm_tn, v4, result, result);
            mk_ite(rm_tp, v3, result, result);
            mk_ite(rm_nte, v2, result, result);
            mk_ite(rm_nta, v1, result, result);
        }
    }
    else {
        SASSERT(!m_arith_util.is_numeral(x));
        bv_util & bu = m_bv_util;
        arith_util & au = m_arith_util;

        expr_ref bv0(m), bv1(m), zero(m), two(m);
        bv0 = bu.mk_numeral(0, 1);
        bv1 = bu.mk_numeral(1, 1);
        zero = au.mk_numeral(rational(0), false);
        two = au.mk_numeral(rational(2), false);

        expr_ref sgn(m), sig(m), exp(m);
        sgn = mk_fresh_const("fpa2bv_to_fp_real_sgn", 1);         
        sig = mk_fresh_const("fpa2bv_to_fp_real_sig", sbits + 4);
        exp = mk_fresh_const("fpa2bv_to_fp_real_exp", ebits + 2);

        expr_ref rme(rm, m);
        round(s, rme, sgn, sig, exp, result);
        
        expr * e = m.mk_eq(m_util.mk_to_real(result), x);
        m_extra_assertions.push_back(e);
    }

    SASSERT(is_well_sorted(m, result));
}

void fpa2bv_converter::mk_to_fp_real_int(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    // rm + real + int -> float
    SASSERT(m_util.is_float(f->get_range()));
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());

    expr * rm = args[0];

    rational q;
    if (!m_arith_util.is_numeral(args[1], q))
        UNREACHABLE();

    rational e;
    if (!m_arith_util.is_numeral(args[2], e))
        UNREACHABLE();

    SASSERT(e.is_int64());
    SASSERT(m_mpz_manager.eq(e.to_mpq().denominator(), 1));

    if (q.is_zero())
        return mk_pzero(f, result);
    else {
        scoped_mpf nte(m_mpf_manager), nta(m_mpf_manager), tp(m_mpf_manager), tn(m_mpf_manager), tz(m_mpf_manager);
        m_mpf_manager.set(nte, ebits, sbits, MPF_ROUND_NEAREST_TEVEN, q.to_mpq(), e.to_mpq().numerator());
        m_mpf_manager.set(nta, ebits, sbits, MPF_ROUND_NEAREST_TAWAY, q.to_mpq(), e.to_mpq().numerator());
        m_mpf_manager.set(tp, ebits, sbits, MPF_ROUND_TOWARD_POSITIVE, q.to_mpq(), e.to_mpq().numerator());
        m_mpf_manager.set(tn, ebits, sbits, MPF_ROUND_TOWARD_NEGATIVE, q.to_mpq(), e.to_mpq().numerator());
        m_mpf_manager.set(tz, ebits, sbits, MPF_ROUND_TOWARD_ZERO, q.to_mpq(), e.to_mpq().numerator());

        app_ref a_nte(m), a_nta(m), a_tp(m), a_tn(m), a_tz(m);
        a_nte = m_plugin->mk_numeral(nte);
        a_nta = m_plugin->mk_numeral(nta);
        a_tp = m_plugin->mk_numeral(tp);
        a_tn = m_plugin->mk_numeral(tn);
        a_tz = m_plugin->mk_numeral(tz);

        expr_ref bv_nte(m), bv_nta(m), bv_tp(m), bv_tn(m), bv_tz(m);
        mk_numeral(a_nte->get_decl(), 0, 0, bv_nte);
        mk_numeral(a_nta->get_decl(), 0, 0, bv_nta);
        mk_numeral(a_tp->get_decl(), 0, 0, bv_tp);
        mk_numeral(a_tn->get_decl(), 0, 0, bv_tn);
        mk_numeral(a_tz->get_decl(), 0, 0, bv_tz);

        expr_ref c1(m), c2(m), c3(m), c4(m);
        c1 = m.mk_eq(rm, m_bv_util.mk_numeral(BV_RM_TO_POSITIVE, 3));
        c2 = m.mk_eq(rm, m_bv_util.mk_numeral(BV_RM_TO_POSITIVE, 3));
        c3 = m.mk_eq(rm, m_bv_util.mk_numeral(BV_RM_TIES_TO_AWAY, 3));
        c4 = m.mk_eq(rm, m_bv_util.mk_numeral(BV_RM_TIES_TO_EVEN, 3));

        mk_ite(c1, bv_tn, bv_tz, result);
        mk_ite(c2, bv_tp, result, result);
        mk_ite(c3, bv_nta, result, result);
        mk_ite(c4, bv_nte, result, result);
    }
}

void fpa2bv_converter::mk_to_real(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    TRACE("fpa2bv_to_real", for (unsigned i = 0; i < num; i++)
          tout << "arg" << i << " = " << mk_ismt2_pp(args[i], m) << std::endl;);
    SASSERT(num == 1);
    SASSERT(f->get_num_parameters() == 0);
    SASSERT(is_app_of(args[0], m_plugin->get_family_id(), OP_FPA_FP));

    expr * x = args[0];
    sort * s = m.get_sort(x);
    unsigned ebits = m_util.get_ebits(s);
    unsigned sbits = m_util.get_sbits(s);

    sort * rs = m_arith_util.mk_real();
    expr_ref x_is_nan(m), x_is_inf(m), x_is_zero(m);
    mk_is_nan(x, x_is_nan);
    mk_is_inf(x, x_is_inf);
    mk_is_zero(x, x_is_zero);

    expr_ref sgn(m), sig(m), exp(m), lz(m);
    unpack(x, sgn, sig, exp, lz, true);
    // sig is of the form [1].[sigbits]

    SASSERT(m_bv_util.get_bv_size(sgn) == 1);
    SASSERT(m_bv_util.get_bv_size(sig) == sbits);
    SASSERT(m_bv_util.get_bv_size(exp) == ebits);

    expr_ref rsig(m), bit(m), zero(m), one(m), two(m), bv0(m), bv1(m);
    zero = m_arith_util.mk_numeral(rational(0), rs);
    one = m_arith_util.mk_numeral(rational(1), rs);
    two = m_arith_util.mk_numeral(rational(2), rs);
    bv0 = m_bv_util.mk_numeral(0, 1);
    bv1 = m_bv_util.mk_numeral(1, 1);
    rsig = one;
    for (unsigned i = sbits - 2; i != (unsigned)-1; i--) {
        bit = m_bv_util.mk_extract(i, i, sig);
        rsig = m_arith_util.mk_add(m_arith_util.mk_mul(rsig, two),
                                   m.mk_ite(m.mk_eq(bit, bv1), one, zero));
    }

    const mpz & p2 = fu().fm().m_powers2(sbits - 1);
    expr_ref ep2(m);
    ep2 = m_arith_util.mk_numeral(rational(p2), false);
    rsig = m_arith_util.mk_div(rsig, ep2);
    dbg_decouple("fpa2bv_to_real_ep2", ep2);
    dbg_decouple("fpa2bv_to_real_rsig", rsig);

    expr_ref exp_n(m), exp_p(m), exp_is_neg(m), exp_abs(m);
    exp_is_neg = m.mk_eq(m_bv_util.mk_extract(ebits - 1, ebits - 1, exp), bv1);
    dbg_decouple("fpa2bv_to_real_exp_is_neg", exp_is_neg);
    exp_p = m_bv_util.mk_sign_extend(1, exp);
    exp_n = m_bv_util.mk_bv_neg(exp_p);
    exp_abs = m.mk_ite(exp_is_neg, exp_n, exp_p);
    dbg_decouple("fpa2bv_to_real_exp_abs", exp);
    SASSERT(m_bv_util.get_bv_size(exp_abs) == ebits + 1);

    expr_ref exp2(m), prev_bit(m);
    exp2 = zero;
    for (unsigned i = ebits; i != (unsigned)-1; i--) {
        bit = m_bv_util.mk_extract(i, i, exp_abs);
        exp2 = m_arith_util.mk_add(m_arith_util.mk_mul(exp2, two),
                                   m.mk_ite(m.mk_eq(bit, bv1), one, zero));
        prev_bit = bit;
    }

    exp2 = m.mk_ite(exp_is_neg, m_arith_util.mk_div(one, exp2), exp2);
    dbg_decouple("fpa2bv_to_real_exp2", exp2);

    expr_ref res(m), two_exp2(m);
    two_exp2 = m_arith_util.mk_power(two, exp2);
    res = m_arith_util.mk_mul(rsig, two_exp2);
    res = m.mk_ite(m.mk_eq(sgn, bv1), m_arith_util.mk_uminus(res), res);
    dbg_decouple("fpa2bv_to_real_sig_times_exp2", res);

    TRACE("fpa2bv_to_real", tout << "rsig = " << mk_ismt2_pp(rsig, m) << std::endl;
    tout << "exp2 = " << mk_ismt2_pp(exp2, m) << std::endl;);

    result = m.mk_ite(x_is_zero, zero, res);
    result = m.mk_ite(x_is_inf, mk_to_real_unspecified(), result);
    result = m.mk_ite(x_is_nan, mk_to_real_unspecified(), result);

    SASSERT(is_well_sorted(m, result));
}

void fpa2bv_converter::mk_to_fp_signed(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    TRACE("fpa2bv_to_fp_signed", for (unsigned i = 0; i < num; i++)
          tout << "arg" << i << " = " << mk_ismt2_pp(args[i], m) << std::endl;);

    // This is a conversion from signed bitvector to float:
    // ; from signed machine integer, represented as a 2's complement bit vector
    // ((_ to_fp eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
    // Semantics:    
    //    Let b in[[(_ BitVec m)]] and let n be the signed integer represented by b (in 2's complement format).
    //    [[(_ to_fp eb sb)]](r, b) = +/ -infinity if n is too large / too small to be represented as a finite 
    //    number of [[(_ FloatingPoint eb sb)]]; [[(_ to_fp eb sb)]](r, x) = y otherwise, where y is the finite 
    //    number such that [[fp.to_real]](y) is closest to n according to rounding mode r.        

    SASSERT(num == 2);
    SASSERT(m_util.is_float(f->get_range()));
    SASSERT(m_bv_util.is_bv(args[0]));
    SASSERT(m_bv_util.is_bv(args[1]));

    expr_ref rm(m), x(m);
    rm = args[0];
    x = args[1];

    dbg_decouple("fpa2bv_to_fp_signed_x", x);

    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());
    unsigned bv_sz = m_bv_util.get_bv_size(x);
    SASSERT(m_bv_util.get_bv_size(rm) == 3);

    expr_ref bv0_1(m), bv1_1(m), bv0_sz(m), bv1_sz(m);
    bv0_1 = m_bv_util.mk_numeral(0, 1);
    bv1_1 = m_bv_util.mk_numeral(1, 1);
    bv0_sz = m_bv_util.mk_numeral(0, bv_sz);
    bv1_sz = m_bv_util.mk_numeral(1, bv_sz);

    expr_ref is_zero(m), nzero(m), pzero(m), ninf(m), pinf(m);
    is_zero = m.mk_eq(x, bv0_sz);
    mk_nzero(f, nzero);
    mk_pzero(f, pzero);
    mk_ninf(f, ninf);
    mk_pinf(f, pinf);

    // Special case: x == 0 -> p/n zero
    expr_ref c1(m), v1(m);
    c1 = is_zero;    
    v1 = pzero;

    // Special case: x != 0
    expr_ref is_neg_bit(m), exp_too_large(m), sig_4(m), exp_2(m);
    expr_ref is_neg(m), x_abs(m);
    is_neg_bit = m_bv_util.mk_extract(bv_sz - 1, bv_sz - 1, x);
    is_neg = m.mk_eq(is_neg_bit, bv1_1);
    x_abs = m.mk_ite(is_neg, m_bv_util.mk_bv_neg(x), x);
    dbg_decouple("fpa2bv_to_fp_signed_is_neg", is_neg);
    // x_abs has an extra bit in the front.
    // x_abs is [bv_sz-1, bv_sz-2] . [bv_sz-3 ... 0] * 2^(bv_sz-2)
    // bv_sz-2 is the "1.0" bit for the rounder.

    expr_ref lz(m), e_bv_sz(m), e_rest_sz(m);
    mk_leading_zeros(x_abs, bv_sz, lz);
    e_bv_sz = m_bv_util.mk_numeral(bv_sz, bv_sz);
    e_rest_sz = m_bv_util.mk_bv_sub(e_bv_sz, lz);
    SASSERT(m_bv_util.get_bv_size(lz) == m_bv_util.get_bv_size(e_bv_sz));
    dbg_decouple("fpa2bv_to_fp_signed_lz", lz);
    expr_ref shifted_sig(m);
    shifted_sig = m_bv_util.mk_bv_shl(x_abs, lz);

    expr_ref sticky(m);
    // shifted_sig is [bv_sz-1, bv_sz-2] . [bv_sz-3 ... 0] * 2^(bv_sz-2) * 2^(-lz)
    unsigned sig_sz = sbits + 4; // we want extra rounding bits.
    if (sig_sz <= bv_sz) {
        expr_ref sig_rest(m);
        sig_4 = m_bv_util.mk_extract(bv_sz - 1, bv_sz - sig_sz + 1, shifted_sig); // one short
        sig_rest = m_bv_util.mk_extract(bv_sz - sig_sz, 0, shifted_sig);
        sticky = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, sig_rest.get());
        sig_4 = m_bv_util.mk_concat(sig_4, sticky);
    }
    else {
        unsigned extra_bits = sig_sz - bv_sz;
        expr_ref extra_zeros(m);
        extra_zeros = m_bv_util.mk_numeral(0, extra_bits);
        sig_4 = m_bv_util.mk_concat(shifted_sig, extra_zeros);
        lz = m_bv_util.mk_bv_add(m_bv_util.mk_concat(extra_zeros, lz), 
                                 m_bv_util.mk_numeral(extra_bits, sig_sz));
        bv_sz = bv_sz + extra_bits;
        SASSERT(is_well_sorted(m, lz));
    }
    SASSERT(m_bv_util.get_bv_size(sig_4) == sig_sz);
        
    expr_ref s_exp(m), exp_rest(m);
    s_exp = m_bv_util.mk_bv_sub(m_bv_util.mk_numeral(bv_sz - 2, bv_sz), lz);
    // s_exp = (bv_sz-2) + (-lz) signed
    SASSERT(m_bv_util.get_bv_size(s_exp) == bv_sz);

    unsigned exp_sz = ebits + 2; // (+2 for rounder)
    exp_2 = m_bv_util.mk_extract(exp_sz - 1, 0, s_exp);
    // the remaining bits are 0 if ebits is large enough.    
    exp_too_large = m.mk_false();

    // The exponent is at most bv_sz, i.e., we need ld(bv_sz)+1 ebits.
    // exp < bv_sz (+sign bit which is [0])    
    unsigned exp_worst_case_sz = (unsigned)((log((double)bv_sz) / log((double)2)) + 1.0);
    
    TRACE("fpa2bv_to_fp_signed", tout << "exp worst case sz: " << exp_worst_case_sz << std::endl;);

    if (exp_sz < exp_worst_case_sz) {
        // exp_sz < exp_worst_case_sz and exp >= 0.
        // Take the maximum legal exponent; this
        // allows us to keep the most precision.
        expr_ref max_exp(m), max_exp_bvsz(m);
        mk_max_exp(exp_sz, max_exp);
        max_exp_bvsz = m_bv_util.mk_zero_extend(bv_sz - exp_sz, max_exp);

        exp_too_large = m_bv_util.mk_ule(m_bv_util.mk_bv_add(
                                            max_exp_bvsz, 
                                            m_bv_util.mk_numeral(1, bv_sz)), 
                                         s_exp);
        sig_4 = m.mk_ite(exp_too_large, m_bv_util.mk_numeral(0, sig_sz), sig_4);
        exp_2 = m.mk_ite(exp_too_large, max_exp, exp_2);
    }
    dbg_decouple("fpa2bv_to_fp_signed_exp_too_large", exp_too_large);    

    expr_ref sgn(m), sig(m), exp(m);
    sgn = is_neg_bit;
    sig = sig_4;
    exp = exp_2;

    dbg_decouple("fpa2bv_to_fp_signed_sgn", sgn);
    dbg_decouple("fpa2bv_to_fp_signed_sig", sig);
    dbg_decouple("fpa2bv_to_fp_signed_exp", exp);

    SASSERT(m_bv_util.get_bv_size(sig) == sbits + 4);
    SASSERT(m_bv_util.get_bv_size(exp) == ebits + 2);
    
    expr_ref v2(m);
    round(f->get_range(), rm, sgn, sig, exp, v2);
    
    mk_ite(c1, v1, v2, result);
}

void fpa2bv_converter::mk_to_fp_unsigned(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    TRACE("fpa2bv_to_fp_unsigned", for (unsigned i = 0; i < num; i++)
          tout << "arg" << i << " = " << mk_ismt2_pp(args[i], m) << std::endl;);

    // This is a conversion from unsigned bitvector to float:
    // ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
    // Semantics:
    //    Let b in[[(_ BitVec m)]] and let n be the unsigned integer represented by b.
    //    [[(_ to_fp_unsigned eb sb)]](r, x) = +infinity if n is too large to be
    //    represented as a finite number of[[(_ FloatingPoint eb sb)]];
    //    [[(_ to_fp_unsigned eb sb)]](r, x) = y otherwise, where y is the finite number
    //    such that[[fp.to_real]](y) is closest to n according to rounding mode r.

    SASSERT(num == 2);
    SASSERT(m_util.is_float(f->get_range()));
    SASSERT(m_bv_util.is_bv(args[0]));
    SASSERT(m_bv_util.is_bv(args[1]));

    expr_ref rm(m), x(m);
    rm = args[0];
    x = args[1];

    dbg_decouple("fpa2bv_to_fp_unsigned_x", x);

    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());
    unsigned bv_sz = m_bv_util.get_bv_size(x);
    SASSERT(m_bv_util.get_bv_size(rm) == 3);    

    expr_ref bv0_1(m), bv1_1(m), bv0_sz(m), bv1_sz(m);
    bv0_1 = m_bv_util.mk_numeral(0, 1);
    bv1_1 = m_bv_util.mk_numeral(1, 1);
    bv0_sz = m_bv_util.mk_numeral(0, bv_sz);
    bv1_sz = m_bv_util.mk_numeral(1, bv_sz);

    expr_ref is_zero(m), nzero(m), pzero(m), ninf(m), pinf(m);
    is_zero = m.mk_eq(x, bv0_sz);
    mk_nzero(f, nzero);
    mk_pzero(f, pzero);
    mk_ninf(f, ninf);
    mk_pinf(f, pinf);

    // Special case: x == 0 -> p/n zero
    expr_ref c1(m), v1(m);
    c1 = is_zero;
    v1 = pzero;

    // Special case: x != 0
    expr_ref exp_too_large(m), sig_4(m), exp_2(m);        
    // x is [bv_sz-1] . [bv_sz-2 ... 0] * 2^(bv_sz-1)
    // bv_sz-1 is the "1.0" bit for the rounder.

    expr_ref lz(m), e_bv_sz(m), e_rest_sz(m);
    mk_leading_zeros(x, bv_sz, lz);
    e_bv_sz = m_bv_util.mk_numeral(bv_sz, bv_sz);
    e_rest_sz = m_bv_util.mk_bv_sub(e_bv_sz, lz);
    SASSERT(m_bv_util.get_bv_size(lz) == m_bv_util.get_bv_size(e_bv_sz));
    dbg_decouple("fpa2bv_to_fp_unsigned_lz", lz);
    expr_ref shifted_sig(m);
    shifted_sig = m_bv_util.mk_bv_shl(x, lz);

    expr_ref sticky(m);
    // shifted_sig is [bv_sz-1] . [bv_sz-2 ... 0] * 2^(bv_sz-1) * 2^(-lz)
    unsigned sig_sz = sbits + 4; // we want extra rounding bits.
    if (sig_sz <= bv_sz) {
        expr_ref sig_rest(m);
        sig_4 = m_bv_util.mk_extract(bv_sz - 1, bv_sz - sig_sz + 1, shifted_sig); // one short
        sig_rest = m_bv_util.mk_extract(bv_sz - sig_sz, 0, shifted_sig);
        sticky = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, sig_rest.get());
        sig_4 = m_bv_util.mk_concat(sig_4, sticky);
    }
    else {
        unsigned extra_bits = sig_sz - bv_sz;
        expr_ref extra_zeros(m);
        extra_zeros = m_bv_util.mk_numeral(0, extra_bits);
        sig_4 = m_bv_util.mk_concat(shifted_sig, extra_zeros);
        lz = m_bv_util.mk_bv_add(m_bv_util.mk_concat(extra_zeros, lz),
                                 m_bv_util.mk_numeral(extra_bits, sig_sz));
        bv_sz = bv_sz + extra_bits;
        SASSERT(is_well_sorted(m, lz));
    }
    SASSERT(m_bv_util.get_bv_size(sig_4) == sig_sz);

    expr_ref s_exp(m), exp_rest(m);
    s_exp = m_bv_util.mk_bv_sub(m_bv_util.mk_numeral(bv_sz - 2, bv_sz), lz);
    // s_exp = (bv_sz-2) + (-lz) signed
    SASSERT(m_bv_util.get_bv_size(s_exp) == bv_sz);

    unsigned exp_sz = ebits + 2; // (+2 for rounder)
    exp_2 = m_bv_util.mk_extract(exp_sz - 1, 0, s_exp);
    // the remaining bits are 0 if ebits is large enough.    
    exp_too_large = m.mk_false(); // This is always in range.        

    // The exponent is at most bv_sz, i.e., we need ld(bv_sz)+1 ebits.
    // exp < bv_sz (+sign bit which is [0])    
    unsigned exp_worst_case_sz = (unsigned)((log((double)bv_sz) / log((double)2)) + 1.0);    

    if (exp_sz < exp_worst_case_sz) {
        // exp_sz < exp_worst_case_sz and exp >= 0.
        // Take the maximum legal exponent; this
        // allows us to keep the most precision.
        expr_ref max_exp(m), max_exp_bvsz(m);
        mk_max_exp(exp_sz, max_exp);
        max_exp_bvsz = m_bv_util.mk_zero_extend(bv_sz - exp_sz, max_exp);

        exp_too_large = m_bv_util.mk_ule(m_bv_util.mk_bv_add(
            max_exp_bvsz,
            m_bv_util.mk_numeral(1, bv_sz)),
            s_exp);
        sig_4 = m.mk_ite(exp_too_large, m_bv_util.mk_numeral(0, sig_sz), sig_4);
        exp_2 = m.mk_ite(exp_too_large, max_exp, exp_2);
    }
    dbg_decouple("fpa2bv_to_fp_unsigned_exp_too_large", exp_too_large);

    expr_ref sgn(m), sig(m), exp(m);
    sgn = bv0_1;
    sig = sig_4;
    exp = exp_2;

    dbg_decouple("fpa2bv_to_fp_unsigned_sgn", sgn);
    dbg_decouple("fpa2bv_to_fp_unsigned_sig", sig);
    dbg_decouple("fpa2bv_to_fp_unsigned_exp", exp);

    SASSERT(m_bv_util.get_bv_size(sig) == sbits + 4);
    SASSERT(m_bv_util.get_bv_size(exp) == ebits + 2);

    expr_ref v2(m);
    round(f->get_range(), rm, sgn, sig, exp, v2);

    mk_ite(c1, v1, v2, result);
}

void fpa2bv_converter::mk_to_ieee_bv(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 1);
    expr * sgn, * s, * e;
    split_fp(args[0], sgn, e, s);
    result = m_bv_util.mk_concat(m_bv_util.mk_concat(sgn, e), s);
}

void fpa2bv_converter::mk_to_ubv(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    TRACE("fpa2bv_to_ubv", for (unsigned i = 0; i < num; i++)
          tout << "arg" << i << " = " << mk_ismt2_pp(args[i], m) << std::endl;);
    
    SASSERT(f->get_num_parameters() == 1);
    SASSERT(f->get_parameter(0).is_int());
    SASSERT(num == 2);
    SASSERT(m_bv_util.get_bv_size(args[0]) == 3);
    SASSERT(m_util.is_float(args[1]));

    expr * rm = args[0];
    expr * x = args[1];
    sort * xs = m.get_sort(x);
    sort * bv_srt = f->get_range();

    unsigned ebits = m_util.get_ebits(xs);
    unsigned sbits = m_util.get_sbits(xs);
    unsigned bv_sz = (unsigned)f->get_parameter(0).get_int();
    
    expr_ref bv0(m), bv1(m);
    bv0 = m_bv_util.mk_numeral(0, 1);
    bv1 = m_bv_util.mk_numeral(1, 1);

    expr_ref x_is_nan(m), x_is_inf(m), x_is_zero(m), x_is_neg(m), x_is_nzero(m);
    mk_is_nan(x, x_is_nan);
    mk_is_inf(x, x_is_inf);
    mk_is_zero(x, x_is_zero);
    mk_is_neg(x, x_is_neg);
    mk_is_nzero(x, x_is_nzero);

    // NaN, Inf, or negative (except -0) -> unspecified
    expr_ref c1(m), v1(m);
    c1 = m.mk_or(x_is_nan, x_is_inf, m.mk_and(x_is_neg, m.mk_not(x_is_nzero)));
    v1 = mk_to_ubv_unspecified(bv_sz);

    // +-Zero  -> 0
    expr_ref c2(m), v2(m);
    c2 = x_is_zero;
    v2 = m_bv_util.mk_numeral(rational(0), bv_srt);
    dbg_decouple("fpa2bv_to_ubv_c2", c2);

    // Otherwise...
    expr_ref sgn(m), sig(m), exp(m), lz(m);
    unpack(x, sgn, sig, exp, lz, true);

    // sig is of the form +- [1].[sig] * 2^(exp-lz)
    SASSERT(m_bv_util.get_bv_size(sgn) == 1);
    SASSERT(m_bv_util.get_bv_size(sig) == sbits);
    SASSERT(m_bv_util.get_bv_size(exp) == ebits);
    SASSERT(m_bv_util.get_bv_size(lz) == ebits);
    dbg_decouple("fpa2bv_to_ubv_sig", sig);
    unsigned sig_sz = m_bv_util.get_bv_size(sig);
    SASSERT(sig_sz == sbits);
    if (sig_sz < (bv_sz + 3))
        sig = m_bv_util.mk_concat(sig, m_bv_util.mk_numeral(0, bv_sz - sig_sz + 3));
    sig_sz = m_bv_util.get_bv_size(sig);
    SASSERT(sig_sz >= (bv_sz + 3));

    expr_ref exp_m_lz(m), shift(m), shift_neg(m), bv0_e2(m), shift_abs(m);
    exp_m_lz = m_bv_util.mk_bv_sub(m_bv_util.mk_sign_extend(2, exp), 
                                   m_bv_util.mk_zero_extend(2, lz));
    shift = m_bv_util.mk_bv_sub(exp_m_lz,
                                m_bv_util.mk_numeral(bv_sz - 1, ebits + 2));
    shift_neg = m_bv_util.mk_bv_neg(shift);
    bv0_e2 = m_bv_util.mk_numeral(0, ebits + 2);
    shift_abs = m.mk_ite(m_bv_util.mk_sle(shift, bv0_e2), shift_neg, shift);
    SASSERT(m_bv_util.get_bv_size(shift) == ebits + 2);
    SASSERT(m_bv_util.get_bv_size(shift_neg) == ebits + 2);
    SASSERT(m_bv_util.get_bv_size(shift_abs) == ebits + 2);
    dbg_decouple("fpa2bv_to_ubv_shift", shift);
    dbg_decouple("fpa2bv_to_ubv_shift_abs", shift_abs);

    // x is of the form +- [1].[sig][r][g][s] ... and at least bv_sz + 3 long    
    //           [1][ ... sig ... ][r][g][ ... s ...]
    // [    ... ubv ...    ][r][g][  ... s ...      ]
    expr_ref max_shift(m);
    max_shift = m_bv_util.mk_numeral(sig_sz, sig_sz);
    shift_abs = m_bv_util.mk_zero_extend(sig_sz - ebits - 2, shift_abs);
    SASSERT(m_bv_util.get_bv_size(shift_abs) == sig_sz);

    expr_ref c_in_limits(m);
    c_in_limits = m_bv_util.mk_sle(shift, m_bv_util.mk_numeral(0, ebits + 2));
    dbg_decouple("fpa2bv_to_ubv_in_limits", c_in_limits);

    expr_ref shifted_sig(m);    
    shifted_sig = m_bv_util.mk_bv_lshr(sig, shift_abs);
    dbg_decouple("fpa2bv_to_ubv_shifted_sig", shifted_sig);

    expr_ref last(m), round(m), sticky(m);
    last   = m_bv_util.mk_extract(sig_sz - bv_sz - 0, sig_sz - bv_sz - 0, shifted_sig);
    round  = m_bv_util.mk_extract(sig_sz - bv_sz - 1, sig_sz - bv_sz - 1, shifted_sig);
    sticky = m.mk_ite(m.mk_eq(m_bv_util.mk_extract(sig_sz - bv_sz - 2, 0, shifted_sig),
                                  m_bv_util.mk_numeral(0, sig_sz - (bv_sz + 3) + 2)),
                          bv0,
                          bv1);
    dbg_decouple("fpa2bv_to_ubv_last", last);
    dbg_decouple("fpa2bv_to_ubv_round", round);    
    dbg_decouple("fpa2bv_to_ubv_sticky", sticky);
    
    expr_ref rounding_decision(m);
    rounding_decision = mk_rounding_decision(rm, sgn, last, round, sticky);
    SASSERT(m_bv_util.get_bv_size(rounding_decision) == 1);
    dbg_decouple("fpa2bv_to_ubv_rounding_decision", rounding_decision);

    expr_ref unrounded_sig(m), pre_rounded(m), inc(m);
    unrounded_sig = m_bv_util.mk_zero_extend(1, m_bv_util.mk_extract(sig_sz - 1, sig_sz - bv_sz, shifted_sig));
    inc = m_bv_util.mk_zero_extend(1, m_bv_util.mk_zero_extend(bv_sz - 1, rounding_decision));
    pre_rounded = m_bv_util.mk_bv_add(unrounded_sig, inc);

    expr_ref rnd_overflow(m), rnd(m), rnd_has_overflown(m);
    rnd_overflow = m_bv_util.mk_extract(bv_sz, bv_sz, pre_rounded);
    rnd = m_bv_util.mk_extract(bv_sz - 1, 0, pre_rounded);
    rnd_has_overflown = m.mk_eq(rnd_overflow, bv1);
    dbg_decouple("fpa2bv_to_ubv_rnd_has_overflown", rnd_has_overflown);

    result = m.mk_ite(rnd_has_overflown, mk_to_ubv_unspecified(bv_sz), rnd);
    result = m.mk_ite(c_in_limits, result, mk_to_ubv_unspecified(bv_sz));
    result = m.mk_ite(c2, v2, result);
    result = m.mk_ite(c1, v1, result);

    SASSERT(is_well_sorted(m, result));
}

void fpa2bv_converter::mk_to_sbv(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    TRACE("fpa2bv_to_sbv", for (unsigned i = 0; i < num; i++)
          tout << "arg" << i << " = " << mk_ismt2_pp(args[i], m) << std::endl;);

    SASSERT(f->get_num_parameters() == 1);
    SASSERT(f->get_parameter(0).is_int());
    SASSERT(num == 2);
    SASSERT(m_bv_util.get_bv_size(args[0]) == 3);
    SASSERT(m_util.is_float(args[1]));

    expr * rm = args[0];
    expr * x = args[1];
    sort * xs = m.get_sort(x);
    sort * bv_srt = f->get_range();    

    unsigned ebits = m_util.get_ebits(xs);
    unsigned sbits = m_util.get_sbits(xs);
    unsigned bv_sz = (unsigned)f->get_parameter(0).get_int();    

    expr_ref bv0(m), bv1(m), bv0_2(m), bv1_2(m), bv3_2(m);
    bv0 = m_bv_util.mk_numeral(0, 1);
    bv1 = m_bv_util.mk_numeral(1, 1);
    bv0_2 = m_bv_util.mk_numeral(0, 2);
    bv1_2 = m_bv_util.mk_numeral(1, 2);
    bv3_2 = m_bv_util.mk_numeral(3, 2);

    expr_ref x_is_nan(m), x_is_inf(m), x_is_zero(m), x_is_neg(m), x_is_nzero(m);
    mk_is_nan(x, x_is_nan);
    mk_is_inf(x, x_is_inf);
    mk_is_zero(x, x_is_zero);
    mk_is_neg(x, x_is_neg);
    mk_is_nzero(x, x_is_nzero);

    // NaN, Inf -> unspecified
    expr_ref c1(m), v1(m);
    c1 = m.mk_or(x_is_nan, x_is_inf);
    v1 = mk_to_sbv_unspecified(bv_sz);
    dbg_decouple("fpa2bv_to_sbv_c1", c1);

    // +-Zero -> 0
    expr_ref c2(m), v2(m);
    c2 = x_is_zero;
    v2 = m_bv_util.mk_numeral(rational(0), bv_srt);
    dbg_decouple("fpa2bv_to_sbv_c2", c2);

    // Otherwise...
    expr_ref sgn(m), sig(m), exp(m), lz(m);
    unpack(x, sgn, sig, exp, lz, true);

    dbg_decouple("fpa2bv_to_sbv_sgn", sgn);
    dbg_decouple("fpa2bv_to_sbv_sig", sig);
    dbg_decouple("fpa2bv_to_sbv_exp", exp);

    // x is of the form +- [1].[sig] * 2^(exp-lz)
    SASSERT(m_bv_util.get_bv_size(sgn) == 1);
    SASSERT(m_bv_util.get_bv_size(sig) == sbits);
    SASSERT(m_bv_util.get_bv_size(exp) == ebits);
    SASSERT(m_bv_util.get_bv_size(lz) == ebits);
    dbg_decouple("fpa2bv_to_sbv_sig", sig);
    unsigned sig_sz = m_bv_util.get_bv_size(sig);
    SASSERT(sig_sz == sbits);
    if (sig_sz < (bv_sz + 3))
        sig = m_bv_util.mk_concat(sig, m_bv_util.mk_numeral(0, bv_sz - sig_sz + 3));
    sig_sz = m_bv_util.get_bv_size(sig);
    SASSERT(sig_sz >= (bv_sz + 3));

    expr_ref exp_m_lz(m), shift(m), shift_neg(m), bv0_e2(m), shift_abs(m);
    exp_m_lz = m_bv_util.mk_bv_sub(m_bv_util.mk_sign_extend(2, exp),
                                   m_bv_util.mk_zero_extend(2, lz));
    shift = m_bv_util.mk_bv_sub(exp_m_lz,
                                m_bv_util.mk_numeral(bv_sz - 1, ebits + 2));
    shift_neg = m_bv_util.mk_bv_neg(shift);
    bv0_e2 = m_bv_util.mk_numeral(0, ebits + 2);
    shift_abs = m.mk_ite(m_bv_util.mk_sle(shift, bv0_e2), shift_neg, shift);
    SASSERT(m_bv_util.get_bv_size(shift) == ebits + 2);
    SASSERT(m_bv_util.get_bv_size(shift_neg) == ebits + 2);
    SASSERT(m_bv_util.get_bv_size(shift_abs) == ebits + 2);    
    dbg_decouple("fpa2bv_to_sbv_shift", shift);    

    // sig is of the form +- [1].[sig][r][g][s] ... and at least bv_sz + 3 long    
    //           [1][ ... sig ... ][r][g][ ... s ...]
    // [    ... ubv ...    ][r][g][  ... s ...      ]
    expr_ref max_shift(m);
    max_shift = m_bv_util.mk_numeral(sig_sz, sig_sz);
    shift_abs = m_bv_util.mk_zero_extend(sig_sz - ebits - 2, shift_abs);
    SASSERT(m_bv_util.get_bv_size(shift_abs) == sig_sz);
    dbg_decouple("fpa2bv_to_sbv_shift_abs", shift_abs);

    expr_ref c_in_limits(m);
    c_in_limits = m_bv_util.mk_sle(shift, m_bv_util.mk_numeral(0, ebits + 2));
    dbg_decouple("fpa2bv_to_sbv_in_limits", c_in_limits);

    expr_ref huge_sig(m), huge_shift(m), huge_shifted_sig(m);
    huge_sig = m_bv_util.mk_concat(sig, m_bv_util.mk_numeral(0, sig_sz));
    huge_shift = m_bv_util.mk_concat(m_bv_util.mk_numeral(0, sig_sz), shift_abs);
    huge_shifted_sig = m_bv_util.mk_bv_lshr(huge_sig, huge_shift);
    dbg_decouple("fpa2bv_to_sbv_huge_shifted_sig", huge_shifted_sig);
    SASSERT(m_bv_util.get_bv_size(huge_shifted_sig) == 2 * sig_sz);

    expr_ref upper_hss(m), lower_hss(m);
    upper_hss = m_bv_util.mk_extract(2 * sig_sz - 1, sig_sz + 1, huge_shifted_sig);    
    lower_hss = m_bv_util.mk_extract(sig_sz, 0, huge_shifted_sig);
    SASSERT(m_bv_util.get_bv_size(upper_hss) == sig_sz - 1);
    SASSERT(m_bv_util.get_bv_size(lower_hss) == sig_sz + 1);
    dbg_decouple("fpa2bv_to_sbv_upper_hss", upper_hss);
    dbg_decouple("fpa2bv_to_sbv_lower_hss", lower_hss);

    expr_ref last(m), round(m), sticky(m);
    last = m_bv_util.mk_extract(1, 1, upper_hss);
    round = m_bv_util.mk_extract(0, 0, upper_hss);    
    sticky = m.mk_app(m_bv_util.get_fid(), OP_BREDOR, lower_hss.get());
    dbg_decouple("fpa2bv_to_sbv_last", last);
    dbg_decouple("fpa2bv_to_sbv_round", round);
    dbg_decouple("fpa2bv_to_sbv_sticky", sticky);

    expr_ref upper_hss_w_sticky(m);
    upper_hss_w_sticky = m_bv_util.mk_concat(upper_hss, sticky);
    dbg_decouple("fpa2bv_to_sbv_upper_hss_w_sticky", upper_hss_w_sticky);
    SASSERT(m_bv_util.get_bv_size(upper_hss_w_sticky) == sig_sz);

    expr_ref rounding_decision(m);
    rounding_decision = mk_rounding_decision(rm, sgn, last, round, sticky);
    SASSERT(m_bv_util.get_bv_size(rounding_decision) == 1);
    dbg_decouple("fpa2bv_to_sbv_rounding_decision", rounding_decision);

    expr_ref unrounded_sig(m), pre_rounded(m), inc(m);
    unrounded_sig = m_bv_util.mk_extract(sig_sz - 1, sig_sz - bv_sz - 1, upper_hss_w_sticky);
    inc = m_bv_util.mk_zero_extend(bv_sz, rounding_decision);
    pre_rounded = m_bv_util.mk_bv_add(unrounded_sig, inc);
    dbg_decouple("fpa2bv_to_sbv_inc", inc);
    dbg_decouple("fpa2bv_to_sbv_unrounded_sig", unrounded_sig);
    dbg_decouple("fpa2bv_to_sbv_pre_rounded", pre_rounded);

    expr_ref rnd_overflow(m), rnd_abs(m), rnd_signed(m), rnd_has_overflown(m), extra_neg(m);
    rnd_overflow = m_bv_util.mk_extract(bv_sz, bv_sz - 1, pre_rounded);
    rnd_abs = m_bv_util.mk_extract(bv_sz - 1, 0, pre_rounded);
    rnd_signed = m.mk_ite(m.mk_eq(sgn, bv1), m_bv_util.mk_bv_neg(rnd_abs), rnd_abs);
    extra_neg = m_bv_util.mk_numeral(fu().fm().m_powers2(bv_sz-1), bv_sz+1);
    rnd_has_overflown = m.mk_and(m.mk_not(m.mk_eq(rnd_overflow, bv0_2)),
                                 m.mk_not(m.mk_and(m.mk_eq(sgn, bv1), m.mk_eq(pre_rounded, extra_neg))));
    dbg_decouple("fpa2bv_to_sbv_extra_neg", extra_neg);
    dbg_decouple("fpa2bv_to_sbv_rnd_overflow", rnd_overflow);
    dbg_decouple("fpa2bv_to_sbv_rnd_abs", rnd_abs);
    dbg_decouple("fpa2bv_to_sbv_rnd_has_overflown", rnd_has_overflown);

    result = m.mk_ite(rnd_has_overflown, mk_to_sbv_unspecified(bv_sz), rnd_signed);
    result = m.mk_ite(c_in_limits, result, mk_to_sbv_unspecified(bv_sz));
    result = m.mk_ite(c2, v2, result);
    result = m.mk_ite(c1, v1, result);

    SASSERT(is_well_sorted(m, result));
}

expr_ref fpa2bv_converter::mk_to_ubv_unspecified(unsigned width) {
    if (m_hi_fp_unspecified)
        return expr_ref(m_bv_util.mk_numeral(0, width), m);
    else
        return expr_ref(m_util.mk_internal_to_ubv_unspecified(width), m);
}

expr_ref fpa2bv_converter::mk_to_sbv_unspecified(unsigned width) {
    if (m_hi_fp_unspecified)
        return expr_ref(m_bv_util.mk_numeral(0, width), m);
    else
        return expr_ref(m_util.mk_internal_to_sbv_unspecified(width), m);
}

expr_ref fpa2bv_converter::mk_to_real_unspecified() {
    if (m_hi_fp_unspecified)
        return expr_ref(m_arith_util.mk_numeral(rational(0), false), m);
    else
        return expr_ref(m_util.mk_internal_to_real_unspecified(), m);
}

void fpa2bv_converter::mk_fp(expr * sign, expr * exponent, expr * significand, expr_ref & result) {
    SASSERT(m_bv_util.is_bv(sign) && m_bv_util.get_bv_size(sign) == 1);
    SASSERT(m_bv_util.is_bv(significand));
    SASSERT(m_bv_util.is_bv(exponent));
    result = m.mk_app(m_util.get_family_id(), OP_FPA_FP, sign, exponent, significand);
}

void fpa2bv_converter::mk_fp(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 3);
    SASSERT(m_bv_util.get_bv_size(args[0]) == 1);
    SASSERT(m_util.get_sbits(f->get_range()) == m_bv_util.get_bv_size(args[2]) + 1);
    SASSERT(m_util.get_ebits(f->get_range()) == m_bv_util.get_bv_size(args[1]));
    mk_fp(args[0], args[1], args[2], result);
    TRACE("fpa2bv_mk_fp", tout << "mk_fp result = " << mk_ismt2_pp(result, m) << std::endl;);
}

void fpa2bv_converter::split_fp(expr * e, expr * & sgn, expr * & exp, expr * & sig) const {
    SASSERT(is_app_of(e, m_plugin->get_family_id(), OP_FPA_FP));
    SASSERT(to_app(e)->get_num_args() == 3);    
    sgn = to_app(e)->get_arg(0);    
    exp = to_app(e)->get_arg(1);
    sig = to_app(e)->get_arg(2);
}

void fpa2bv_converter::split_fp(expr * e, expr_ref & sgn, expr_ref & exp, expr_ref & sig) const {
    SASSERT(is_app_of(e, m_plugin->get_family_id(), OP_FPA_FP));
    SASSERT(to_app(e)->get_num_args() == 3);
    expr *e_sgn, *e_sig, *e_exp;
    split_fp(e, e_sgn, e_exp, e_sig);
    sgn = e_sgn;
    exp = e_exp;
    sig = e_sig;    
}

void fpa2bv_converter::mk_is_nan(expr * e, expr_ref & result) {
    expr * sgn, * sig, * exp;
    split_fp(e, sgn, exp, sig);
    
    // exp == 1^n , sig != 0
    expr_ref sig_is_zero(m), sig_is_not_zero(m), exp_is_top(m), top_exp(m), zero(m);
    mk_top_exp(m_bv_util.get_bv_size(exp), top_exp);

    zero = m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(sig));
    m_simp.mk_eq(sig, zero, sig_is_zero);
    m_simp.mk_not(sig_is_zero, sig_is_not_zero);
    m_simp.mk_eq(exp, top_exp, exp_is_top);
    m_simp.mk_and(exp_is_top, sig_is_not_zero, result);
}

void fpa2bv_converter::mk_is_inf(expr * e, expr_ref & result) {
    expr * sgn, * sig, * exp;
    split_fp(e, sgn, exp, sig);
    expr_ref eq1(m), eq2(m), top_exp(m), zero(m);
    mk_top_exp(m_bv_util.get_bv_size(exp), top_exp);
    zero = m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(sig));
    m_simp.mk_eq(sig, zero, eq1);
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
    SASSERT(is_app_of(e, m_plugin->get_family_id(), OP_FPA_FP));
    SASSERT(to_app(e)->get_num_args() == 3);
    expr * a0 = to_app(e)->get_arg(0);
    expr_ref zero(m);
    zero = m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(a0));
    m_simp.mk_eq(a0, zero, result);
}

void fpa2bv_converter::mk_is_neg(expr * e, expr_ref & result) {
    SASSERT(is_app_of(e, m_plugin->get_family_id(), OP_FPA_FP));
    SASSERT(to_app(e)->get_num_args() == 3);
    expr * a0 = to_app(e)->get_arg(0);
    expr_ref one(m);
    one = m_bv_util.mk_numeral(1, m_bv_util.get_bv_size(a0));
    m_simp.mk_eq(a0, one, result);
}

void fpa2bv_converter::mk_is_zero(expr * e, expr_ref & result) {
    expr * sgn, * sig, * exp;
    split_fp(e, sgn, exp, sig);
    expr_ref eq1(m), eq2(m), bot_exp(m), zero(m);
    mk_bot_exp(m_bv_util.get_bv_size(exp), bot_exp);
    zero = m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(sig));
    m_simp.mk_eq(sig, zero, eq1);
    m_simp.mk_eq(exp, bot_exp, eq2);
    m_simp.mk_and(eq1, eq2, result);
}

void fpa2bv_converter::mk_is_nzero(expr * e, expr_ref & result) {
    expr * sgn, * sig, * exp;
    split_fp(e, sgn, exp, sig);
    expr_ref e_is_zero(m), eq(m), one_1(m);
    mk_is_zero(e, e_is_zero);
    one_1 = m_bv_util.mk_numeral(1, 1);
    m_simp.mk_eq(sgn, one_1, eq);
    m_simp.mk_and(eq, e_is_zero, result);
}

void fpa2bv_converter::mk_is_pzero(expr * e, expr_ref & result) {
    expr * sgn, * sig, * exp;
    split_fp(e, sgn, exp, sig);
    expr_ref e_is_zero(m), eq(m), nil_1(m);
    mk_is_zero(e, e_is_zero);
    nil_1 = m_bv_util.mk_numeral(0, 1);
    m_simp.mk_eq(sgn, nil_1, eq);
    m_simp.mk_and(eq, e_is_zero, result);
}

void fpa2bv_converter::mk_is_denormal(expr * e, expr_ref & result) {
    expr * sgn, *sig, *exp;
    split_fp(e, sgn, exp, sig);

    expr_ref zero(m), zexp(m), is_zero(m), n_is_zero(m);
    zero = m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(exp));
    m_simp.mk_eq(exp, zero, result);
    m_simp.mk_eq(exp, zero, zexp);
    mk_is_zero(e, is_zero);
    m_simp.mk_not(is_zero, n_is_zero);
    m_simp.mk_and(n_is_zero, zexp, result);
}

void fpa2bv_converter::mk_is_normal(expr * e, expr_ref & result) {    
    expr * sgn, * sig, * exp;
    split_fp(e, sgn, exp, sig);

    expr_ref is_special(m), is_denormal(m), p(m), is_zero(m);
    mk_is_denormal(e, is_denormal);
    mk_is_zero(e, is_zero);
    unsigned ebits = m_bv_util.get_bv_size(exp);
    p = m_bv_util.mk_numeral(fu().fm().m_powers2.m1(ebits), ebits);
    m_simp.mk_eq(exp, p, is_special);

    expr_ref or_ex(m);
    m_simp.mk_or(is_special, is_denormal, or_ex);
    m_simp.mk_or(is_zero, or_ex, or_ex);
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
    case BV_RM_TO_POSITIVE: 
    case BV_RM_TO_ZERO: 
        return m_simp.mk_eq(e, rm_num, result);
    default:
        UNREACHABLE();
    }
}

void fpa2bv_converter::mk_top_exp(unsigned sz, expr_ref & result) {
    result = m_bv_util.mk_numeral(fu().fm().m_powers2.m1(sz), sz);
}

void fpa2bv_converter::mk_bot_exp(unsigned sz, expr_ref & result) {
    result = m_bv_util.mk_numeral(0, sz);
}

void fpa2bv_converter::mk_min_exp(unsigned ebits, expr_ref & result) {
    SASSERT(ebits >= 2);
    const mpz & z = m_mpf_manager.m_powers2.m1(ebits-1, true);
    result = m_bv_util.mk_numeral(z + mpz(1), ebits);
}

void fpa2bv_converter::mk_max_exp(unsigned ebits, expr_ref & result) {
    SASSERT(ebits >= 2);        
    result = m_bv_util.mk_numeral(m_mpf_manager.m_powers2.m1(ebits-1, false), ebits);   
}

void fpa2bv_converter::mk_leading_zeros(expr * e, unsigned max_bits, expr_ref & result) { 
    SASSERT(m_bv_util.is_bv(e));
    unsigned bv_sz = m_bv_util.get_bv_size(e);

    if (bv_sz == 0)
        result = m_bv_util.mk_numeral(0, max_bits);
    else if (bv_sz == 1) {
        expr_ref eq(m), nil_1(m), one_m(m), nil_m(m);
        nil_1 = m_bv_util.mk_numeral(0, 1);
        one_m = m_bv_util.mk_numeral(1, max_bits);
        nil_m = m_bv_util.mk_numeral(0, max_bits);
        m_simp.mk_eq(e, nil_1, eq);
        m_simp.mk_ite(eq, one_m, nil_m, result);
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

        expr_ref H_is_zero(m), nil_h(m);
        nil_h = m_bv_util.mk_numeral(0, H_size);
        m_simp.mk_eq(H, nil_h, H_is_zero);        

        expr_ref sum(m), h_m(m);
        h_m = m_bv_util.mk_numeral(H_size, max_bits);
        sum = m_bv_util.mk_bv_add(h_m, lzL);
        m_simp.mk_ite(H_is_zero, sum, lzH, result);        
    }

    SASSERT(is_well_sorted(m, result));
}

void fpa2bv_converter::mk_bias(expr * e, expr_ref & result) {    
    unsigned ebits = m_bv_util.get_bv_size(e);
    SASSERT(ebits >= 2);

    expr_ref bias(m);
    bias = m_bv_util.mk_numeral(fu().fm().m_powers2.m1(ebits-1), ebits);
    result = m_bv_util.mk_bv_add(e, bias);
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

void fpa2bv_converter::unpack(expr * e, expr_ref & sgn, expr_ref & sig, expr_ref & exp, expr_ref & lz, bool normalize) {
    SASSERT(is_app_of(e, m_plugin->get_family_id(), OP_FPA_FP));
    SASSERT(to_app(e)->get_num_args() == 3);

    sort * srt = to_app(e)->get_decl()->get_range();
    SASSERT(is_float(srt));
    unsigned sbits = m_util.get_sbits(srt);
    unsigned ebits = m_util.get_ebits(srt);

    split_fp(e, sgn, exp, sig);

    SASSERT(m_bv_util.get_bv_size(sgn) == 1);
    SASSERT(m_bv_util.get_bv_size(exp) == ebits);
    SASSERT(m_bv_util.get_bv_size(sig) == sbits-1);

    expr_ref is_normal(m);
    mk_is_normal(e, is_normal);

    expr_ref normal_sig(m), normal_exp(m);
    normal_sig = m_bv_util.mk_concat(m_bv_util.mk_numeral(1, 1), sig);
    mk_unbias(exp, normal_exp);
    dbg_decouple("fpa2bv_unpack_normal_exp", normal_exp);

    expr_ref denormal_sig(m), denormal_exp(m);
    denormal_sig = m_bv_util.mk_zero_extend(1, sig);   
    // SASSERT(ebits >= 3); // Note: when ebits=2 there is no 1-exponent, so mk_unbias will produce a 0.
    denormal_exp = m_bv_util.mk_numeral(1, ebits);
    mk_unbias(denormal_exp, denormal_exp);
    dbg_decouple("fpa2bv_unpack_denormal_exp", denormal_exp);    

    expr_ref zero_e(m);
    zero_e = m_bv_util.mk_numeral(0, ebits);

    if (normalize) {
        expr_ref is_sig_zero(m), zero_s(m);
        zero_s = m_bv_util.mk_numeral(0, sbits);
        m_simp.mk_eq(zero_s, denormal_sig, is_sig_zero);

        expr_ref lz_d(m);
        mk_leading_zeros(denormal_sig, ebits, lz_d);        
        m_simp.mk_ite(m.mk_or(is_normal, is_sig_zero), zero_e, lz_d, lz);
        dbg_decouple("fpa2bv_unpack_lz", lz);

        expr_ref shift(m);
        m_simp.mk_ite(is_sig_zero, zero_e, lz, shift);
        dbg_decouple("fpa2bv_unpack_shift", shift);
        SASSERT(is_well_sorted(m, is_sig_zero));
        SASSERT(is_well_sorted(m, shift));
        SASSERT(m_bv_util.get_bv_size(shift) == ebits);
        if (ebits <= sbits) {        
            expr_ref q(m);
            q = m_bv_util.mk_zero_extend(sbits-ebits, shift);
            denormal_sig = m_bv_util.mk_bv_shl(denormal_sig, q);            
        } 
        else {
            // the maximum shift is `sbits', because after that the mantissa
            // would be zero anyways. So we can safely cut the shift variable down,
            // as long as we check the higher bits.            
            expr_ref sh(m), is_sh_zero(m), sl(m), sbits_s(m), short_shift(m);
            zero_s = m_bv_util.mk_numeral(0, sbits-1);
            sbits_s = m_bv_util.mk_numeral(sbits, sbits);
            sh = m_bv_util.mk_extract(ebits-1, sbits, shift);            
            m_simp.mk_eq(zero_s, sh, is_sh_zero);
            short_shift = m_bv_util.mk_extract(sbits-1, 0, shift);
            m_simp.mk_ite(is_sh_zero, short_shift, sbits_s, sl);
            denormal_sig = m_bv_util.mk_bv_shl(denormal_sig, sl);
        }        
    }
    else
        lz = zero_e;

    SASSERT(is_well_sorted(m, normal_sig));
    SASSERT(is_well_sorted(m, denormal_sig));
    SASSERT(is_well_sorted(m, normal_exp));
    SASSERT(is_well_sorted(m, denormal_exp));

    dbg_decouple("fpa2bv_unpack_is_normal", is_normal);

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
    case OP_FPA_RM_NEAREST_TIES_TO_EVEN: result = m_bv_util.mk_numeral(BV_RM_TIES_TO_EVEN, 3); break;
    case OP_FPA_RM_NEAREST_TIES_TO_AWAY: result = m_bv_util.mk_numeral(BV_RM_TIES_TO_AWAY, 3); break;    
    case OP_FPA_RM_TOWARD_POSITIVE: result = m_bv_util.mk_numeral(BV_RM_TO_POSITIVE, 3); break;
    case OP_FPA_RM_TOWARD_NEGATIVE: result = m_bv_util.mk_numeral(BV_RM_TO_NEGATIVE, 3); break;    
    case OP_FPA_RM_TOWARD_ZERO: result = m_bv_util.mk_numeral(BV_RM_TO_ZERO, 3); break;
    default: UNREACHABLE();
    }
}

void fpa2bv_converter::dbg_decouple(const char * prefix, expr_ref & e) {    
    #ifdef Z3DEBUG
    return;
    // CMW: This works only for quantifier-free formulas.
    expr_ref new_e(m);
    new_e = m.mk_fresh_const(prefix, m.get_sort(e));
    m_extra_assertions.push_back(m.mk_eq(new_e, e));
    e = new_e;
    #endif
}

expr_ref fpa2bv_converter::mk_rounding_decision(expr * rm, expr * sgn, expr * last, expr * round, expr * sticky) {
    expr_ref rmr(rm, m);
    expr_ref sgnr(sgn, m);
    expr_ref lastr(last, m);
    expr_ref roundr(round, m);
    expr_ref stickyr(sticky, m);
    dbg_decouple("fpa2bv_rnd_dec_rm", rmr);
    dbg_decouple("fpa2bv_rnd_dec_sgn", sgnr);
    dbg_decouple("fpa2bv_rnd_dec_last", lastr);
    dbg_decouple("fpa2bv_rnd_dec_round", roundr);
    dbg_decouple("fpa2bv_rnd_dec_sticky", stickyr);

    expr_ref last_or_sticky(m), round_or_sticky(m), not_last(m), not_round(m), not_sticky(m), not_lors(m), not_rors(m), not_sgn(m);
    expr * last_sticky[2] = { last, sticky };
    expr * round_sticky[2] = { round, sticky };
    last_or_sticky = m_bv_util.mk_bv_or(2, last_sticky);
    round_or_sticky = m_bv_util.mk_bv_or(2, round_sticky);
    not_last= m_bv_util.mk_bv_not(last);
    not_round = m_bv_util.mk_bv_not(round);
    not_sticky = m_bv_util.mk_bv_not(sticky);
    not_lors = m_bv_util.mk_bv_not(last_or_sticky);
    not_rors = m_bv_util.mk_bv_not(round_or_sticky);
    not_sgn = m_bv_util.mk_bv_not(sgn);
    expr * nround_lors[2] = { not_round, not_lors };    
    expr * pos_args[2] = { sgn, not_rors };
    expr * neg_args[2] = { not_sgn, not_rors };
    expr * nl_r[2] = { last, not_round };
    expr * nl_nr_sn[3] = { not_last, not_round, not_sticky };

    expr_ref inc_teven(m), inc_taway(m), inc_pos(m), inc_neg(m);
    inc_teven = m_bv_util.mk_bv_not(m_bv_util.mk_bv_or(2, nround_lors));
    expr *taway_args[2] = { m_bv_util.mk_bv_not(m_bv_util.mk_bv_or(2, nl_r)),
                            m_bv_util.mk_bv_not(m_bv_util.mk_bv_or(3, nl_nr_sn)) };
    inc_taway = m_bv_util.mk_bv_or(2, taway_args);
    inc_pos = m_bv_util.mk_bv_not(m_bv_util.mk_bv_or(2, pos_args));
    inc_neg = m_bv_util.mk_bv_not(m_bv_util.mk_bv_or(2, neg_args));

    expr_ref res(m), inc_c2(m), inc_c3(m), inc_c4(m);
    expr_ref rm_is_to_neg(m), rm_is_to_pos(m), rm_is_away(m), rm_is_even(m), nil_1(m);
    nil_1 = m_bv_util.mk_numeral(0, 1);
    mk_is_rm(rm, BV_RM_TO_NEGATIVE, rm_is_to_neg);
    mk_is_rm(rm, BV_RM_TO_POSITIVE, rm_is_to_pos);
    mk_is_rm(rm, BV_RM_TIES_TO_AWAY, rm_is_away);
    mk_is_rm(rm, BV_RM_TIES_TO_EVEN, rm_is_even);
    m_simp.mk_ite(rm_is_to_neg, inc_neg, nil_1, inc_c4);
    m_simp.mk_ite(rm_is_to_pos, inc_pos, inc_c4, inc_c3);
    m_simp.mk_ite(rm_is_away, inc_taway, inc_c3, inc_c2);
    m_simp.mk_ite(rm_is_even, inc_teven, inc_c2, res);
    
    dbg_decouple("fpa2bv_rnd_dec_res", res);
    return res;
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
    expr_ref e3(m), ne3(m), e2(m), e1(m), e21(m), one_1(m), h_exp(m), sh_exp(m), th_exp(m);
    one_1 = m_bv_util.mk_numeral(1, 1);
    h_exp = m_bv_util.mk_extract(ebits+1, ebits+1, exp);
    sh_exp = m_bv_util.mk_extract(ebits, ebits, exp);
    th_exp = m_bv_util.mk_extract(ebits-1, ebits-1, exp);
    m_simp.mk_eq(h_exp, one_1, e3);
    m_simp.mk_eq(sh_exp, one_1, e2);
    m_simp.mk_eq(th_exp, one_1, e1);
    m_simp.mk_or(e2, e1, e21);
    m_simp.mk_not(e3, ne3);
    m_simp.mk_and(ne3, e21, e_top_three);

    expr_ref ext_emax(m), t_sig(m);
    ext_emax = m_bv_util.mk_zero_extend(2, e_max);
    t_sig = m_bv_util.mk_extract(sbits+3, sbits+3, sig);
    m_simp.mk_eq(ext_emax, exp, e_eq_emax);
    m_simp.mk_eq(t_sig, one_1, sigm1);
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
    dbg_decouple("fpa2bv_rnd_t", t);
    expr_ref TINY(m);    
    TINY = m_bv_util.mk_sle(t, m_bv_util.mk_numeral((unsigned)-1, ebits+2));
    dbg_decouple("fpa2bv_rnd_TINY", TINY);
    TRACE("fpa2bv_dbg", tout << "TINY = " << mk_ismt2_pp(TINY, m) << std::endl;);
    SASSERT(is_well_sorted(m, TINY));    

    expr_ref beta(m);    
    beta = m_bv_util.mk_bv_add(m_bv_util.mk_bv_sub(exp, lz), m_bv_util.mk_numeral(1, ebits+2));

    TRACE("fpa2bv_dbg", tout << "beta = " << mk_ismt2_pp(beta, m)<< std::endl; );    
    SASSERT(is_well_sorted(m, beta));

    dbg_decouple("fpa2bv_rnd_beta", beta);
    dbg_decouple("fpa2bv_rnd_e_min", e_min);
    dbg_decouple("fpa2bv_rnd_e_max", e_max);

    expr_ref sigma(m), sigma_add(m);
    sigma_add = m_bv_util.mk_bv_sub(exp, m_bv_util.mk_sign_extend(2, e_min));
    sigma_add = m_bv_util.mk_bv_add(sigma_add, m_bv_util.mk_numeral(1, ebits+2));
    m_simp.mk_ite(TINY, sigma_add, lz, sigma);

    dbg_decouple("fpa2bv_rnd_sigma", sigma);

    TRACE("fpa2bv_dbg", tout << "Shift distance: " << mk_ismt2_pp(sigma, m) << std::endl;);
    SASSERT(is_well_sorted(m, sigma));

    // Normalization shift
    dbg_decouple("fpa2bv_rnd_sig_before_shift", sig);

    unsigned sig_size = m_bv_util.get_bv_size(sig);
    SASSERT(sig_size == sbits+4);
    SASSERT(m_bv_util.get_bv_size(sigma) == ebits+2);
    unsigned sigma_size = ebits+2;

    expr_ref sigma_neg(m), sigma_cap(m), sigma_neg_capped(m), sigma_lt_zero(m), sig_ext(m), 
             rs_sig(m), ls_sig(m), big_sh_sig(m), sigma_le_cap(m);
    sigma_neg = m_bv_util.mk_bv_neg(sigma);
    sigma_cap = m_bv_util.mk_numeral(sbits+2, sigma_size);
    sigma_le_cap = m_bv_util.mk_ule(sigma_neg, sigma_cap);
    m_simp.mk_ite(sigma_le_cap, sigma_neg, sigma_cap, sigma_neg_capped);
    dbg_decouple("fpa2bv_rnd_sigma_neg", sigma_neg);
    dbg_decouple("fpa2bv_rnd_sigma_cap", sigma_cap);
    dbg_decouple("fpa2bv_rnd_sigma_neg_capped", sigma_neg_capped);
    sigma_lt_zero = m_bv_util.mk_sle(sigma, m_bv_util.mk_numeral((unsigned)-1, sigma_size));
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
    expr_ref ext_sticky(m);
    ext_sticky = m_bv_util.mk_zero_extend(sbits+1, sticky);
    expr * tmp[] = { sig, ext_sticky };
    sig = m_bv_util.mk_bv_or(2, tmp);
    SASSERT(is_well_sorted(m, sig));
    SASSERT(m_bv_util.get_bv_size(sig) == sbits+2);    
    
    // CMW: The (OVF1 && OVFen) and (TINY && UNFen) cases are never taken.
    expr_ref ext_emin(m);
    ext_emin = m_bv_util.mk_zero_extend(2, e_min);
    m_simp.mk_ite(TINY, ext_emin, beta, exp);
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

    expr_ref inc(m);
    inc = mk_rounding_decision(rm, sgn, last, round, sticky);
    
    SASSERT(m_bv_util.get_bv_size(inc) == 1 && is_well_sorted(m, inc));
    dbg_decouple("fpa2bv_rnd_inc", inc);

    sig = m_bv_util.mk_bv_add(m_bv_util.mk_zero_extend(1, sig), 
                              m_bv_util.mk_zero_extend(sbits, inc));
    SASSERT(is_well_sorted(m, sig));
    dbg_decouple("fpa2bv_rnd_sig_plus_inc", sig);

    // Post normalization    
    SASSERT(m_bv_util.get_bv_size(sig) == sbits + 1);
    expr_ref SIGovf(m);
    t_sig = m_bv_util.mk_extract(sbits, sbits, sig);
    m_simp.mk_eq(t_sig, one_1, SIGovf);
    SASSERT(is_well_sorted(m, SIGovf));    
    dbg_decouple("fpa2bv_rnd_SIGovf", SIGovf);

    expr_ref hallbut1_sig(m), lallbut1_sig(m);
    hallbut1_sig = m_bv_util.mk_extract(sbits, 1, sig);
    lallbut1_sig = m_bv_util.mk_extract(sbits-1, 0, sig);
    m_simp.mk_ite(SIGovf, hallbut1_sig, lallbut1_sig, sig);

    SASSERT(m_bv_util.get_bv_size(exp) == ebits + 2);

    expr_ref exp_p1(m);
    exp_p1 = m_bv_util.mk_bv_add(exp, m_bv_util.mk_numeral(1, ebits+2));
    m_simp.mk_ite(SIGovf, exp_p1, exp, exp);

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

    expr_ref preOVF2(m), OVF2(m), OVF(m), exp_redand(m), pem2m1(m);
    exp_redand = m.mk_app(m_bv_util.get_fid(), OP_BREDAND, biased_exp.get());
    m_simp.mk_eq(exp_redand, one_1, preOVF2);
    m_simp.mk_and(SIGovf, preOVF2, OVF2);
    pem2m1 = m_bv_util.mk_numeral(fu().fm().m_powers2.m1(ebits-2), ebits);
    m_simp.mk_ite(OVF2, pem2m1, biased_exp, biased_exp);
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

    expr_ref nil_1(m);
    nil_1 = m_bv_util.mk_numeral(0, 1);

    expr_ref rm_is_to_zero(m), rm_is_to_neg(m), rm_is_to_pos(m), rm_zero_or_neg(m), rm_zero_or_pos(m);    
    mk_is_rm(rm, BV_RM_TO_ZERO, rm_is_to_zero);
    mk_is_rm(rm, BV_RM_TO_NEGATIVE, rm_is_to_neg);
    mk_is_rm(rm, BV_RM_TO_POSITIVE, rm_is_to_pos);
    m_simp.mk_or(rm_is_to_zero, rm_is_to_neg, rm_zero_or_neg);
    m_simp.mk_or(rm_is_to_zero, rm_is_to_pos, rm_zero_or_pos);
    dbg_decouple("fpa2bv_rnd_rm_is_to_zero", rm_is_to_zero);
    dbg_decouple("fpa2bv_rnd_rm_is_to_neg", rm_is_to_neg);
    dbg_decouple("fpa2bv_rnd_rm_is_to_pos", rm_is_to_pos);


    expr_ref sgn_is_zero(m);
    m_simp.mk_eq(sgn, m_bv_util.mk_numeral(0, 1), sgn_is_zero);
    dbg_decouple("fpa2bv_rnd_sgn_is_zero", sgn_is_zero);

    expr_ref max_sig(m), max_exp(m), inf_sig(m), inf_exp(m);
    max_sig = m_bv_util.mk_numeral(fu().fm().m_powers2.m1(sbits-1, false), sbits-1);
    max_exp = m_bv_util.mk_concat(m_bv_util.mk_numeral(fu().fm().m_powers2.m1(ebits-1, false), ebits-1),
                                  m_bv_util.mk_numeral(0, 1));
    inf_sig = m_bv_util.mk_numeral(0, sbits-1);
    inf_exp = top_exp;

    dbg_decouple("fpa2bv_rnd_max_exp", max_exp);
    dbg_decouple("fpa2bv_rnd_max_sig", max_sig);
    dbg_decouple("fpa2bv_rnd_inf_sig", inf_sig);
    dbg_decouple("fpa2bv_rnd_inf_exp", inf_exp);

    expr_ref ovfl_exp(m), max_inf_exp_neg(m), max_inf_exp_pos(m), n_d_check(m), n_d_exp(m);    
    m_simp.mk_ite(rm_zero_or_pos, max_exp, inf_exp, max_inf_exp_neg);
    m_simp.mk_ite(rm_zero_or_neg, max_exp, inf_exp, max_inf_exp_pos);
    m_simp.mk_ite(sgn_is_zero, max_inf_exp_pos, max_inf_exp_neg, ovfl_exp);
    t_sig = m_bv_util.mk_extract(sbits-1, sbits-1, sig);
    m_simp.mk_eq(t_sig, nil_1, n_d_check);
    m_simp.mk_ite(n_d_check, bot_exp /* denormal */, biased_exp, n_d_exp);
    m_simp.mk_ite(OVF, ovfl_exp, n_d_exp, exp);

    expr_ref max_inf_sig_neg(m), max_inf_sig_pos(m), ovfl_sig(m), rest_sig(m);
    m_simp.mk_ite(rm_zero_or_pos, max_sig, inf_sig, max_inf_sig_neg);
    m_simp.mk_ite(rm_zero_or_neg, max_sig, inf_sig, max_inf_sig_pos);
    m_simp.mk_ite(sgn_is_zero, max_inf_sig_pos, max_inf_sig_neg, ovfl_sig);
    rest_sig = m_bv_util.mk_extract(sbits-2, 0, sig);
    m_simp.mk_ite(OVF, ovfl_sig, rest_sig, sig);
    
    dbg_decouple("fpa2bv_rnd_max_inf_sig_neg", max_inf_sig_neg);
    dbg_decouple("fpa2bv_rnd_max_inf_sig_pos", max_inf_sig_pos);
    dbg_decouple("fpa2bv_rnd_rm_zero_or_neg", rm_zero_or_neg);
    dbg_decouple("fpa2bv_rnd_rm_zero_or_pos", rm_zero_or_pos);

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

    mk_fp(res_sgn, res_exp, res_sig, result);

    TRACE("fpa2bv_round", tout << "ROUND = " << mk_ismt2_pp(result, m) << std::endl; );
}


void fpa2bv_converter::reset(void) {
    dec_ref_map_key_values(m, m_const2bv);
    dec_ref_map_key_values(m, m_rm_const2bv);
    dec_ref_map_key_values(m, m_uf2bvuf);

    obj_map<func_decl, func_decl_triple>::iterator it = m_uf23bvuf.begin();
    obj_map<func_decl, func_decl_triple>::iterator end = m_uf23bvuf.end();
    for (; it != end; ++it) {
        m.dec_ref(it->m_key);
        m.dec_ref(it->m_value.f_sgn);
        m.dec_ref(it->m_value.f_sig);
        m.dec_ref(it->m_value.f_exp);
    }
    m_uf23bvuf.reset();

    m_extra_assertions.reset();
}
