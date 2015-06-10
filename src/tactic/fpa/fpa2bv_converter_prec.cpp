/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_converter_prec.cpp

Abstract:

    Conversion routines for Floating Point -> Bit-Vector

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/
#include"ast_smt2_pp.h"
#include"well_sorted.h"
#include <math.h>

#include"fpa2bv_converter_prec.h"

#define BVULT(X,Y,R) { expr_ref bvult_eq(m), bvult_not(m); m_simp.mk_eq(X, Y, bvult_eq); m_simp.mk_not(bvult_eq, bvult_not); expr_ref t(m); t = m_bv_util.mk_ule(X,Y); m_simp.mk_and(t, bvult_not, R); }
#define BVSLT(X,Y,R) { expr_ref bvslt_eq(m), bvslt_not(m); m_simp.mk_eq(X, Y, bvslt_eq); m_simp.mk_not(bvslt_eq, bvslt_not); expr_ref t(m); t = m_bv_util.mk_sle(X,Y); m_simp.mk_and(t, bvslt_not, R); }

#define MIN_EBITS 3
#define MIN_SBITS 3

fpa2bv_converter_prec::fpa2bv_converter_prec(ast_manager & m, fpa_approximation_mode mode) : 
    fpa2bv_converter(m),
    m_mode(mode) {
}

void fpa2bv_converter_prec::fix_bits(unsigned prec, expr_ref rounded,  unsigned sbits, unsigned ebits)//expr_ref& fixed,
{   //AZ: TODO: revise! minimal number of legal bits is 3!!!! Remove magic numbers
    unsigned szeroes = (unsigned) ((sbits-2)*(MAX_PRECISION - prec  +0.0) / MAX_PRECISION);//3 bits are minimum for the significand
    unsigned ezeroes = (unsigned) ((ebits - 2)*(MAX_PRECISION - prec + 0.0) / MAX_PRECISION);//2 bits are minimum for the exponent

    expr_ref fix_sig(m), fix_exp(m);    
    expr * sgn, *sig, *expn;
    split_fp( rounded.get(), sgn,sig,expn);
    if(ezeroes>0) {
        fix_exp=m.mk_eq(m_bv_util.mk_extract(ebits-2, ebits - ezeroes -1, sig), m_bv_util.mk_numeral(0,ezeroes));
        m_extra_assertions.push_back(fix_exp);
        SASSERT(is_well_sorted(m, fix_exp));
    }

    if(szeroes>0) {
        fix_sig=m.mk_eq(m_bv_util.mk_extract(sbits-2, sbits - szeroes -1, sig), m_bv_util.mk_numeral(0,szeroes));
        m_extra_assertions.push_back(fix_sig);
        SASSERT(is_well_sorted(m, fix_sig));
    }
}

void fpa2bv_converter_prec::mk_const(func_decl * f, unsigned prec, expr_ref & result) {
    switch (m_mode) {
    case FPAA_SMALL_FLOATS:
    {
        if (m_const2bv.contains(f))
            result = m_const2bv.find(f);
        else {
            if (prec == MAX_PRECISION)
                fpa2bv_converter::mk_const(f, result);
            else {
                unsigned ebits = fu().get_ebits(f->get_range());
                unsigned sbits = fu().get_sbits(f->get_range());
                double rel = prec/(double)MAX_PRECISION;
                unsigned new_ebits = (unsigned) (rel * (double)ebits);
                unsigned new_sbits = (unsigned) (rel * (double)sbits);
                if (new_ebits < MIN_EBITS) new_ebits = MIN_EBITS;
                if (new_sbits < MIN_SBITS) new_sbits = MIN_SBITS;
                sort_ref ns(m), fp_srt(m);
                ns = fu().mk_float_sort(new_ebits, new_sbits);
                app_ref small_const(m);
                small_const = m.mk_fresh_const("small_const", ns);

                fp_srt = fu().mk_float_sort(ebits, sbits);
                symbol name("asFloat");
                sort_ref rm_sort(m);
                rm_sort = fu().mk_rm_sort();
                //sort * domain[2] = { rm_sort, ns };
                //parameter parameters[2] = { parameter(ebits), parameter(sbits) };

                fpa2bv_converter::mk_const(small_const->get_decl(), result);
                m_const2bv.insert(f, result.get());
                m.inc_ref(f);
                m.inc_ref(result.get());
#ifdef Z3DEBUG
                std::cout << f->get_name() << " := " << small_const->get_decl()->get_name() <<
                        " [" << new_sbits<<","<<new_ebits<<"]"<<std::endl;
                std::cout.flush();
#endif
                TRACE("fpa2bv_prec", tout << f->get_name() << " := " << mk_ismt2_pp(result, m) << std::endl;);
            }
        }
        break;
    }
    case FPAA_PRECISE:
    case FPAA_FIXBITS:
        fpa2bv_converter::mk_const(f, result); break;
    default:
        UNREACHABLE();
        break;
    }
}
void fpa2bv_converter_prec::mk_small_op(func_decl * f, unsigned new_ebits, unsigned new_sbits, unsigned num, expr * const * args, func_decl_ref & small_op, expr_ref_vector & cast_args)
{
    if (new_ebits < MIN_EBITS) new_ebits = MIN_EBITS;
    if (new_sbits < MIN_SBITS) new_sbits = MIN_SBITS;
    sort_ref new_srt(m), rm_srt(m);    
    new_srt = fu().mk_float_sort(new_ebits, new_sbits);
    rm_srt = fu().mk_rm_sort();
    
    sort_ref_vector new_domain(m);
    cast_args.reset();

    for (unsigned i=0; i < num; i++) // Recreate the domain by replacing the full fpa sort with the smaller one.
    {
        sort * d_i = f->get_domain(i);
        expr * a_i = args[i];

        if (fu().is_rm(d_i))
        {
            new_domain.push_back(rm_srt);
            cast_args.push_back(a_i);
        }
        else if (fu().is_float(f->get_domain(i)))
        {
            sort * a_i_srt = to_app(a_i)->get_decl()->get_range();
            new_domain.push_back(new_srt);

            // Cast the corresponding argument to the right fpa size
            if (is_app(a_i))
            {                
                if (a_i_srt == new_srt)
                    cast_args.push_back(a_i);
                else {
                    app_ref rtz(m);
                    rtz = fu().mk_round_toward_zero();
                    expr_ref rm(m);
                    fpa2bv_converter::mk_rounding_mode(rtz->get_decl(), rm);
                
                    sort * d[2] = { rm_srt, a_i_srt };                                
                    symbol name("asFloat");
                    func_decl_ref fd(m);
                    fd = m.mk_func_decl(name, 2, d, new_srt, func_decl_info(fu().get_family_id(), OP_FPA_TO_FP, new_srt->get_num_parameters(), new_srt->get_parameters()));
             
                    expr_ref t(m);
                    expr * args[2] = { rm, a_i };
                    fpa2bv_converter::mk_to_fp(fd, 2, args, t);
                    cast_args.push_back(t);
                    SASSERT(is_well_sorted(m, t));
                }
            }
            else
                NOT_IMPLEMENTED_YET();
        }
        else
            // just keep everything else
            cast_args.push_back(a_i);
    }

    parameter parameters[2] = { parameter(new_ebits), parameter(new_sbits) };

    // May I reuse parts of the existing declaration? CMW: Sure.

    small_op = m.mk_func_decl(f->get_name(), num, new_domain.c_ptr(), new_srt,
                                func_decl_info(fu().get_family_id(), f->get_decl_kind(), 2, parameters));

    //std::cout<<small_op->get_name()<<"["<<new_sbits<<","<<new_ebits<<"] ";
    //for(unsigned i=0; i<num;i++)
        //std::cout<<mk_ismt2_pp(cast_args[i].get(),m);
    //std::cout<<std::endl;
    //std::cout.flush();

};
void fpa2bv_converter_prec::mk_small_op(func_decl * f, unsigned prec, unsigned num, expr * const * args, func_decl_ref & small_op, expr_ref_vector & cast_args) {
    unsigned ebits = fu().get_ebits(f->get_range());
    unsigned sbits = fu().get_sbits(f->get_range());
    double rel = prec/(double)MAX_PRECISION;
    unsigned new_ebits = (unsigned) (rel * (double)ebits);// (unsigned) (MIN_EBITS + rel * (double)(ebits-MIN_EBITS))
    unsigned new_sbits = (unsigned) (rel * (double)sbits);// (unsigned) (MIN_SBITS + rel * (double)(sbits-MIN_SBITS))
    mk_small_op(f,new_ebits,new_sbits,num,args, small_op, cast_args);
}

void fpa2bv_converter_prec::mk_cast_small_to_big(func_decl * f, expr * arg, expr_ref & result) {
    unsigned ebits = fu().get_ebits(f->get_range());
    unsigned sbits = fu().get_sbits(f->get_range());

    app_ref rtz(m);
    rtz = fu().mk_round_toward_zero();
    expr_ref rm(m);
    fpa2bv_converter::mk_rounding_mode(rtz->get_decl(), rm);
    sort_ref rm_srt(m);
    rm_srt = fu().mk_rm_sort();
    sort * d[2] = { rm_srt, to_app(arg)->get_decl()->get_range() };
    parameter parameters[2] = { parameter(ebits), parameter(sbits) };
    symbol name("asFloat");
    func_decl_ref cast_up(m);
    cast_up = m.mk_func_decl(name, 2, d, f->get_range(), func_decl_info(fu().get_family_id(), OP_FPA_TO_FP, f->get_range()->get_num_parameters(), parameters));
    expr * args[2] = { rm, arg };
    fpa2bv_converter::mk_to_fp(cast_up, 2, args, result);
}

void fpa2bv_converter_prec::mk_cast_small_to_big(unsigned sbits, unsigned ebits, expr * arg, expr_ref & result) {
    app_ref rtz(m);
    rtz = fu().mk_round_toward_zero();
    expr_ref rm(m);
    fpa2bv_converter::mk_rounding_mode(rtz->get_decl(), rm);
    sort_ref rm_srt(m);
    rm_srt = fu().mk_rm_sort();
    sort * d[2] = { rm_srt, to_app(arg)->get_decl()->get_range() };
    parameter parameters[2] = { parameter(ebits), parameter(sbits) };
    symbol name("asFloat");
    func_decl_ref cast_up(m);
    sort_ref ns(m);
    ns = fu().mk_float_sort(ebits, sbits);
    cast_up = m.mk_func_decl(name, 2, d, ns, func_decl_info(fu().get_family_id(), OP_FPA_TO_FP, 2, parameters));
    expr * args[2] = { rm, arg };
    fpa2bv_converter::mk_to_fp(cast_up, 2, args, result);
}


void fpa2bv_converter_prec::match_sorts(expr * a, expr * b, expr_ref & n_a, expr_ref & n_b)
{
    //Check if the sorts of lhs and rhs match, otherwise cast them to appropriate size?
    SASSERT(is_app_of(a, m_plugin->get_family_id(), OP_FPA_FP));
    SASSERT(is_app_of(b, m_plugin->get_family_id(), OP_FPA_FP));
    func_decl * a_decl = to_app(a)->get_decl();
    func_decl * b_decl = to_app(b)->get_decl();

    unsigned a_ebits = fu().get_ebits(a_decl->get_range());
    unsigned a_sbits = fu().get_sbits(a_decl->get_range());
    unsigned b_ebits = fu().get_ebits(b_decl->get_range());
    unsigned b_sbits = fu().get_sbits(b_decl->get_range());
    unsigned n_ebits, n_sbits;

    //if( (a_ebits == b_ebits) && (a_sbits == b_sbits))
    //{//No need for adjustment
    n_a = a;
    n_b = b;
    //}
    //else
    //{
    if ((a_ebits <= b_ebits) && (a_sbits<= b_sbits))
    {//sort of b is wider than sort of a, we cast a to the sort of b.
        mk_cast_small_to_big(b_sbits,b_ebits,a,n_a);
        n_b = b;
    }
    else if ((a_ebits >= b_ebits) && (a_sbits >= b_sbits))
    {
        n_a = a;
        mk_cast_small_to_big(a_sbits,a_ebits,b,n_b);
    }
    else
    {
        n_ebits = (a_ebits < b_ebits)? b_ebits:a_ebits;
        n_sbits = (a_sbits < b_sbits)? b_sbits:a_sbits;
        mk_cast_small_to_big(n_sbits,n_ebits,a,n_a);
        mk_cast_small_to_big(n_sbits,n_ebits,b,n_b);
    }
    //}
}
void fpa2bv_converter_prec::mk_eq(expr * a, expr * b, expr_ref & result) {
    // This is structural equality, not floating point equality.
    expr_ref na(m),nb(m);
    match_sorts(a,b,na,nb);
    fpa2bv_converter::mk_eq(na,nb,result);
}

void fpa2bv_converter_prec::mk_ite(expr * c, expr * t, expr * f, expr_ref & result) {    
    expr_ref nt(m),nf(m);
    match_sorts(t,f,nt,nf);
    fpa2bv_converter::mk_ite(c,nt,nf,result);
}



void fpa2bv_converter_prec::mk_add(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    // AZ: Switch can be moved just before the call to the fix_bits method, everything else should be the same
    switch (m_mode) {
    case FPAA_PRECISE:
        fpa2bv_converter::mk_add(f,num,args,result);
        break;
    case FPAA_SMALL_FLOATS:
        {
            func_decl_ref small_fd(m);
            expr_ref_vector small_args(m);
            mk_small_op(f, prec, num, args, small_fd, small_args);
            //expr_ref small_op(m);
            fpa2bv_converter::mk_add(small_fd, num, small_args.c_ptr(), result);
            //mk_cast_small_to_big(f, small_op, result);
            SASSERT(is_well_sorted(m, result));
            TRACE("fpa2bv_small_float_add", tout << "small_fd: " << mk_ismt2_pp(small_fd, m) << std::endl << 
                                            "result = " << mk_ismt2_pp(result, m) << std::endl; );
            break;
        }

    case FPAA_FIXBITS: {
        if (MAX_PRECISION == prec)
            fpa2bv_converter::mk_add(f,num,args,result);
        else{
            //Alternative encoding
            /*func_decl * nf = & func_decl(f->get_name(),
                                         f->get_arity(),
                                         f->get_domain(),
                                         f->get_range(),
                                         f->get_info());*/


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

            //Add the fixed zeroes here...?
            expr_ref sbits_zero(m), ebits_zero(m);
            //        std::cout<<"res_sgn: "<<m_bv_util.get_bv_size(res_sgn)<<std::endl;
            //        std::cout<<"res_sig: "<<m_bv_util.get_bv_size(res_sig)<<std::endl;
            //        std::cout<<"res_exp: "<<m_bv_util.get_bv_size(res_exp)<<std::endl;
            //        std::cout.flush();
            //m_bv_util.mk_extract(szeroes,sbits,res_sig),m_bv_util.mk_numeral(0,sbits-szeroes),sbits_zero);
            //m_bv_util.mk_extract(0,ezeroes,res_exp),m_bv_util.mk_numeral(0,ezeroes),ebits_zero);
            //mk_and()
            //std::cout<<"prec:"<<prec<<std::endl<<"sfixed: "<<sones<<std::endl<<"efixed: "<<ezeroes<<std::endl;
            //<<"sbits: "<<sbits<<std::endl<<"ebits: "<<ebits<<std::endl
            //std::cout.flush();
            //
            //            if(ezeroes>1)
            //                //Exponent = 1 bit for bias, fixed bits, actual exponent bits
            //                res_exp=m_bv_util.mk_concat(m_bv_util.mk_extract(ebits+1, ebits-1, res_exp),
            //                        m_bv_util.mk_concat(m_bv_util.mk_numeral(0,ezeroes),
            //                        m_bv_util.mk_extract(ebits - 2 - ezeroes, 0 ,res_exp)));
            //            if(sones>1)
            //                res_sig=m_bv_util.mk_concat(m_bv_util.mk_extract(sbits+3,sones+4,res_sig),
            //                        m_bv_util.mk_concat(m_bv_util.mk_numeral(0,sones),
            //                        m_bv_util.mk_extract(3,0,res_sig)));
            //
            //        std::cout<<"res_sgn': "<<m_bv_util.get_bv_size(res_sgn)<<std::endl;
            //        std::cout<<"res_sig': "<<m_bv_util.get_bv_size(res_sig)<<std::endl;
            //        std::cout<<"res_exp': "<<m_bv_util.get_bv_size(res_exp)<<std::endl;
            //        std::cout.flush();
            //std::cout<<res_exp.
            expr_ref is_zero_sig(m), nil_sbit4(m);
            nil_sbit4 = m_bv_util.mk_numeral(0, sbits+4);
            m_simp.mk_eq(res_sig, nil_sbit4, is_zero_sig);

            SASSERT(is_well_sorted(m, is_zero_sig));

            dbg_decouple("fpa2bv_add_is_zero_sig", is_zero_sig);

            expr_ref zero_case(m);
            mk_ite(rm_is_to_neg, nzero, pzero, zero_case);

            /*expr_ref rounded(m);
            round(f->get_range(), rm, res_sgn, res_sig, res_exp, rounded);


            mk_ite(is_zero_sig, zero_case, rounded, v7);*/



            expr_ref rounded(m);//, fixed(m);
            round(f->get_range(), rm, res_sgn, res_sig, res_exp, rounded);

            fix_bits(prec, rounded, sbits,ebits);
            mk_ite(is_zero_sig, zero_case, rounded, v7);

            //            signed sones=((sbits-3)*(MAX_PRECISION - prec +0.0)/MAX_PRECISION);//3 bits are minimum for the significand
            //              unsigned ezeroes=((ebits-2)*(MAX_PRECISION - prec+0.0)/MAX_PRECISION);//2 bits are minimum for the exponent
            //            expr_ref fix_sig(m), fix_exp(m), fix_sgn(m), rnd_sig(m), rnd_exp(m), rnd_sgn(m), rnd_lz(m);
            //            expr * sgn, *sig, *expn;
            //            split( rounded.get(), sgn,sig,expn);
            //
            //
            //            if(ezeroes>1)
            //                //Exponent = 1 bit for bias, fixed bits, actual exponent bits
            //                fix_exp=m_bv_util.mk_concat(m_bv_util.mk_extract(ebits-1, ebits-1, expn),
            //                        m_bv_util.mk_concat(m_bv_util.mk_numeral(0,ezeroes),
            //                                m_bv_util.mk_extract(ebits - 2 - ezeroes, 0 , expn)));
            //            if(sones>1)
            //                fix_sig=m_bv_util.mk_concat(m_bv_util.mk_extract(sbits-2,sones,sig),
            //                        m_bv_util.mk_numeral(0,sones));
            //
            //            mk_triple(sgn, fix_sig, fix_exp, fixed);
            //            SASSERT(is_well_sorted(m, fixed));
            //mk_ite(is_zero_sig, zero_case, rounded, v7);




            mk_ite(c6, v6, v7, result);
            mk_ite(c5, v5, result, result);
            mk_ite(c4, v4, result, result);
            mk_ite(c3, v3, result, result);
            mk_ite(c2, v2, result, result);
            mk_ite(c1, v1, result, result);

            SASSERT(is_well_sorted(m, result));

            TRACE("fpa2bv_add", tout << "ADD = " << mk_ismt2_pp(result, m) << std::endl; );
        }
        break;
    }
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::mk_sub(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    SASSERT(num == 3);
    expr_ref t(m);
    fpa2bv_converter::mk_neg(f, 1, &args[2], t);
    expr * nargs[3] = { args[0], args[1], t };

    switch (m_mode) {
    case FPAA_PRECISE:
        fpa2bv_converter::mk_add(f, 3, nargs, result);
        break;
    case FPAA_FIXBITS: // Call the add with prec
    case FPAA_SMALL_FLOATS:
        fpa2bv_converter_prec::mk_add(f, prec, 3, nargs, result);
        break;
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::mk_uminus(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    switch (m_mode) {
    case FPAA_PRECISE:
    case FPAA_SMALL_FLOATS:
    case FPAA_FIXBITS: // for now, encode fully.
        fpa2bv_converter::mk_neg(f,num,args,result);
        break;
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::mk_mul(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    switch (m_mode) {
    case FPAA_PRECISE:
            fpa2bv_converter::mk_mul(f,num,args,result);
        break;
    case FPAA_SMALL_FLOATS:
    {
        func_decl_ref small_fd(m);
        expr_ref_vector small_args(m);
        mk_small_op(f, prec, num, args, small_fd, small_args);
        expr_ref small_op(m);
        fpa2bv_converter::mk_mul(small_fd, num, small_args.c_ptr(), small_op);
        mk_cast_small_to_big(f, small_op, result);
        SASSERT(is_well_sorted(m, result));
        TRACE("fpa2bv_small_float_mul", tout << mk_ismt2_pp(result, m) << std::endl; );
        break;
    }
    case FPAA_FIXBITS: // for now, encode fully.
    { SASSERT(num == 3);

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
    unsigned ebits = m_util.get_ebits(f->get_range());
    unsigned sbits = m_util.get_sbits(f->get_range());
    SASSERT(ebits <= sbits);

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

    //expr_ref rounded(m);
    round(f->get_range(), rm, res_sgn, res_sig, res_exp, v7);

    //AZ:the only difference to the original
    fix_bits(prec, v7, sbits, ebits);

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
    break;
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::mk_div(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    switch (m_mode) {
    case FPAA_SMALL_FLOATS:
    {
        func_decl_ref small_fd(m);
        expr_ref_vector small_args(m);
        mk_small_op(f, prec, num, args, small_fd, small_args);
        expr_ref small_op(m);
        fpa2bv_converter::mk_div(small_fd, num, small_args.c_ptr(), small_op);
        mk_cast_small_to_big(f, small_op, result);
        SASSERT(is_well_sorted(m, result));
        TRACE("fpa2bv_small_float_div", tout << mk_ismt2_pp(result, m) << std::endl; );
        break;
    }
    case FPAA_PRECISE:
    case FPAA_FIXBITS: // for now, encode fully.
        fpa2bv_converter::mk_div(f,num,args,result);
        break;

        {
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

            //expr_ref rounded(m);//AZ
            round(f->get_range(), rm, res_sgn, res_sig, res_exp, v8);

            fix_bits(prec, v8,sbits,ebits);//AZ

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
        break;
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::mk_remainder(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    switch (m_mode) {
    case FPAA_SMALL_FLOATS:
        {
            func_decl_ref small_fd(m);
            expr_ref_vector small_args(m);
            mk_small_op(f, prec, num, args, small_fd, small_args);
            expr_ref small_op(m);
            fpa2bv_converter::mk_rem(small_fd, num, small_args.c_ptr(), small_op);
            mk_cast_small_to_big(f, small_op, result);
            SASSERT(is_well_sorted(m, result));
            TRACE("fpa2bv_small_float_remainder", tout << mk_ismt2_pp(result, m) << std::endl; );
            break;
        }
    case FPAA_PRECISE:
        fpa2bv_converter::mk_rem(f,num,args,result);
        break;
    case FPAA_FIXBITS: // for now, encode fully.
    {
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

        // (x is 0) -> x
        c4 = x_is_zero;
        v4 = pzero;

        // (y is 0) -> NaN.
        c5 = y_is_zero;
        v5 = nan;

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

        expr_ref rm(m);
        rm = m_bv_util.mk_numeral(BV_RM_TIES_TO_EVEN, 3);

        //expr_ref rounded(m);
        round(f->get_range(), rm, res_sgn, res_sig, res_exp, v7);

        fix_bits(prec, v7,sbits, ebits);

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
    break;
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::mk_abs(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    //This doesn't need approximation in it's current form
    switch (m_mode) {
    case FPAA_PRECISE:
    case FPAA_SMALL_FLOATS:
    case FPAA_FIXBITS: // for now, encode fully.
        fpa2bv_converter::mk_abs(f,num,args,result);
        break;
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::mk_min(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    switch (m_mode) {
    case FPAA_PRECISE:
    case FPAA_SMALL_FLOATS:
    case FPAA_FIXBITS: // for now, encode fully.
        fpa2bv_converter::mk_min(f,num,args,result);
        break;
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::mk_max(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    switch (m_mode) {
    case FPAA_PRECISE:
    case FPAA_SMALL_FLOATS:
    case FPAA_FIXBITS: // for now, encode fully.
        fpa2bv_converter::mk_max(f,num,args,result);
        break;
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::mk_fusedma(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    switch (m_mode) {
    case FPAA_SMALL_FLOATS:
        {
            func_decl_ref small_fd(m);
            expr_ref_vector small_args(m);
            mk_small_op(f, prec, num, args, small_fd, small_args);
            expr_ref small_op(m);
            fpa2bv_converter::mk_fma(small_fd, num, small_args.c_ptr(), small_op);
            mk_cast_small_to_big(f, small_op, result);
            SASSERT(is_well_sorted(m, result));
            TRACE("fpa2bv_small_float_fma", tout << mk_ismt2_pp(result, m) << std::endl; );
            break;
        }
    case FPAA_PRECISE:
        fpa2bv_converter::mk_fma(f,num,args,result);
        break;
    case FPAA_FIXBITS:
        {
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
            SASSERT(ebits <= sbits);

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
            res_sgn_c1 = m.mk_app(bvfid, OP_BAND, not_e_sgn, e_sgn, sign_bv);
            res_sgn_c2 = m.mk_app(bvfid, OP_BAND, e_sgn, not_f_sgn, not_sign_bv);
            res_sgn_c3 = m.mk_app(bvfid, OP_BAND, e_sgn, f_sgn);
            expr * res_sgn_or_args[3] = { res_sgn_c1, res_sgn_c2, res_sgn_c3 };
            res_sgn = m_bv_util.mk_bv_or(3, res_sgn_or_args);

            sticky_raw = m_bv_util.mk_extract(sbits-5, 0, sig_abs);
            sticky = m_bv_util.mk_zero_extend(sbits+3, m.mk_app(bvfid, OP_BREDOR, sticky_raw.get()));
            dbg_decouple("fpa2bv_fma_add_sum_sticky", sticky);

            expr * res_or_args[2] = {  m_bv_util.mk_extract(2*sbits-1, sbits-4, sig_abs), sticky };
            res_sig = m_bv_util.mk_bv_or(2, res_or_args);
            SASSERT(m_bv_util.get_bv_size(res_sig) == sbits+4);

            expr_ref is_zero_sig(m), nil_sbits4(m);
            nil_sbits4 = m_bv_util.mk_numeral(0, sbits+4);
            m_simp.mk_eq(res_sig, nil_sbits4, is_zero_sig);
            SASSERT(is_well_sorted(m, is_zero_sig));

            dbg_decouple("fpa2bv_fma_is_zero_sig", is_zero_sig);

            expr_ref zero_case(m);
            mk_ite(rm_is_to_neg, nzero, pzero, zero_case);


            //AZ: Should the zero case be constrained in some manner?
            expr_ref rounded(m);//, fixed(m);
            round(f->get_range(), rm, res_sgn, res_sig, res_exp, rounded);

            fix_bits(prec,rounded,sbits, ebits);

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
        break;
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::mk_sqrt(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    switch (m_mode) {
    case FPAA_SMALL_FLOATS:
    {
        func_decl_ref small_fd(m);
        expr_ref_vector small_args(m);
        mk_small_op(f, prec, num, args, small_fd, small_args);
        expr_ref small_op(m);
        fpa2bv_converter::mk_sqrt(small_fd, num, small_args.c_ptr(), small_op);
        mk_cast_small_to_big(f, small_op, result);
        SASSERT(is_well_sorted(m, result));
        TRACE("fpa2bv_small_float_sqrt", tout << mk_ismt2_pp(result, m) << std::endl; );
        break;
    }
    case FPAA_PRECISE:
    case FPAA_FIXBITS: // for now, encode fully.
        fpa2bv_converter::mk_sqrt(f,num,args,result);
        break;
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::mk_round_to_integral(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result) {
    switch (m_mode) {
    case FPAA_SMALL_FLOATS:
    {
        func_decl_ref small_fd(m);
        expr_ref_vector small_args(m);
        mk_small_op(f, prec, num, args, small_fd, small_args);
        expr_ref small_op(m);
        fpa2bv_converter::mk_round_to_integral(small_fd, num, small_args.c_ptr(), small_op);
        mk_cast_small_to_big(f, small_op, result);
        SASSERT(is_well_sorted(m, result));
        TRACE("fpa2bv_small_float_r2i", tout << mk_ismt2_pp(result, m) << std::endl; );
        break;
    }
    case FPAA_PRECISE:
    case FPAA_FIXBITS: // for now, encode fully.
        fpa2bv_converter::mk_sqrt(f,num,args,result);
        break;
    default: UNREACHABLE(); break;
    }
}

void fpa2bv_converter_prec::establish_sort(unsigned num, expr * const * args, unsigned & ebits, unsigned & sbits)
{
    unsigned ne,ns;
    //hardcoding for now
    ebits = 3;
    sbits = 3;
    for(unsigned i=0;i<num;i++)
    {
        sort * s;
        if(is_app(args[i]) && fu().is_float(s = to_app(args[i])->get_decl()->get_range()))
        {
            ne = fu().get_ebits(s);
            ns = fu().get_sbits(s);
            ebits = (ne < ebits)?ebits:ne;
            sbits = (ns < sbits)?sbits:ns;
        }
    }
}

void fpa2bv_converter_prec::mk_float_eq(func_decl * f, unsigned num, expr * const * args, expr_ref & result)
{
    switch (m_mode) {
        case FPAA_PRECISE:
        case FPAA_FIXBITS:
            fpa2bv_converter::mk_float_eq(f,num,args,result);
            break;
        case FPAA_SMALL_FLOATS:
        {
            unsigned sbits, ebits;

            func_decl_ref small_fd(m);
            expr_ref_vector small_args(m);
            establish_sort(num, args, ebits, sbits);
            mk_small_op(f, ebits, sbits, num, args, small_fd, small_args);
            fpa2bv_converter::mk_float_eq(small_fd, num, small_args.c_ptr(), result);
            SASSERT(is_well_sorted(m, result));
            TRACE("fpa2bv_small_float_add", tout << mk_ismt2_pp(result, m) << std::endl; );
            break;
        }
    }

}

void fpa2bv_converter_prec::mk_float_lt(func_decl * f, unsigned num, expr * const * args, expr_ref & result)
{
    switch (m_mode){
    case FPAA_PRECISE:
    case FPAA_FIXBITS:
        fpa2bv_converter::mk_float_lt(f,num,args,result);
        break;
    case FPAA_SMALL_FLOATS:    {
        unsigned sbits, ebits;

        func_decl_ref small_fd(m);
        expr_ref_vector small_args(m);
        establish_sort(num, args, ebits, sbits);
        mk_small_op(f, ebits, sbits, num, args, small_fd, small_args);
        fpa2bv_converter::mk_float_lt(small_fd, num, small_args.c_ptr(), result);
        SASSERT(is_well_sorted(m, result));
        TRACE("fpa2bv_small_float_add", tout << mk_ismt2_pp(result, m) << std::endl; );
        break;
    }
    }
}
void fpa2bv_converter_prec::mk_float_gt(func_decl * f, unsigned num, expr * const * args, expr_ref & result)
{
    switch (m_mode){
    case FPAA_PRECISE:
    case FPAA_FIXBITS:
        fpa2bv_converter::mk_float_gt(f,num,args,result);
        break;
    case FPAA_SMALL_FLOATS:    {
        unsigned sbits, ebits;

        func_decl_ref small_fd(m);
        expr_ref_vector small_args(m);
        establish_sort(num, args, ebits, sbits);
        mk_small_op(f, ebits, sbits, num, args, small_fd, small_args);
        fpa2bv_converter::mk_float_gt(small_fd, num, small_args.c_ptr(), result);
        SASSERT(is_well_sorted(m, result));
        TRACE("fpa2bv_small_float_add", tout << mk_ismt2_pp(result, m) << std::endl; );
        break;
    }
    }
}
void fpa2bv_converter_prec::mk_float_le(func_decl * f, unsigned num, expr * const * args, expr_ref & result)
{
    switch (m_mode){
    case FPAA_PRECISE:
    case FPAA_FIXBITS:
        fpa2bv_converter::mk_float_le(f,num,args,result);
        break;
    case FPAA_SMALL_FLOATS:    {
        unsigned sbits, ebits;

        func_decl_ref small_fd(m);
        expr_ref_vector small_args(m);
        establish_sort(num, args, ebits, sbits);
        mk_small_op(f, ebits, sbits, num, args, small_fd, small_args);
        fpa2bv_converter::mk_float_le(small_fd, num, small_args.c_ptr(), result);
        SASSERT(is_well_sorted(m, result));
        TRACE("fpa2bv_small_float_add", tout << mk_ismt2_pp(result, m) << std::endl; );
        break;
    }
    }
}
void fpa2bv_converter_prec::mk_float_ge(func_decl * f, unsigned num, expr * const * args, expr_ref & result)
{
    switch (m_mode){
    case FPAA_PRECISE:
    case FPAA_FIXBITS:
        fpa2bv_converter::mk_float_ge(f,num,args,result);
        break;
    case FPAA_SMALL_FLOATS:    {
        unsigned sbits, ebits;

        func_decl_ref small_fd(m);
        expr_ref_vector small_args(m);
        establish_sort(num, args, ebits, sbits);
        mk_small_op(f, ebits, sbits, num, args, small_fd, small_args);
        fpa2bv_converter::mk_float_ge(small_fd, num, small_args.c_ptr(), result);
        SASSERT(is_well_sorted(m, result));
        TRACE("fpa2bv_small_float_add", tout << mk_ismt2_pp(result, m) << std::endl; );
        break;
    }
    }
}
/*

void fpa2bv_converter_prec::mk_is_zero(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result)
{
    switch (m_mode){
    case FPAA_PRECISE:
    case FPAA_FIXBITS:
        fpa2bv_converter::mk_float_eq(f,num,args,result);
        break;
    case FPAA_SMALL_FLOATS:    {
        unsigned sbits, ebits;

        func_decl_ref small_fd(m);
        expr_ref_vector small_args(m);
        establish_sort(num, args, ebits, sbits);
        mk_small_op(f, ebits, sbits, num, args, small_fd, small_args);
        fpa2bv_converter::mk_is_zero(small_fd, num, small_args.c_ptr(), result);
        SASSERT(is_well_sorted(m, result));
        TRACE("fpa2bv_small_float_add", tout << mk_ismt2_pp(result, m) << std::endl; );
        break;
    }
    }
}
void fpa2bv_converter_prec::mk_is_nzero(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
void fpa2bv_converter_prec::mk_is_pzero(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
void fpa2bv_converter_prec::mk_is_sign_minus(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
void fpa2bv_converter_prec::mk_is_nan(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
void fpa2bv_converter_prec::mk_is_inf(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
void fpa2bv_converter_prec::mk_is_normal(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
void fpa2bv_converter_prec::mk_is_subnormal(func_decl * f, unsigned prec, unsigned num, expr * const * args, expr_ref & result);
*/






