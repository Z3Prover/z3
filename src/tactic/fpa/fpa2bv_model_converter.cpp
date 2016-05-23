/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_model_converter.h

Abstract:

    Model conversion for fpa2bv_converter

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/
#include"ast_smt2_pp.h"
#include"fpa_rewriter.h"
#include"fpa2bv_model_converter.h"

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
    for (obj_map<func_decl, func_decl*>::iterator it = m_uf2bvuf.begin();
         it != m_uf2bvuf.end();
         it++) {
        const symbol & n = it->m_key->get_name();
        out << "\n  (" << n << " ";
        unsigned indent = n.size() + 4;
        out << mk_ismt2_pp(it->m_value, m, indent) << ")";
    }
    for (obj_map<func_decl, std::pair<app*, app*> >::iterator it = m_specials.begin();
         it != m_specials.end();
         it++) {
        const symbol & n = it->m_key->get_name();
        out << "\n  (" << n << " ";
        unsigned indent = n.size() + 4;
        out << mk_ismt2_pp(it->m_value.first, m, indent) << "; " <<
               mk_ismt2_pp(it->m_value.second, m, indent) << ")";
    }
    out << ")";
}

model_converter * fpa2bv_model_converter::translate(ast_translation & translator) {
    fpa2bv_model_converter * res = alloc(fpa2bv_model_converter, translator.to());
    for (obj_map<func_decl, expr*>::iterator it = m_const2bv.begin();
         it != m_const2bv.end();
         it++)
    {
        func_decl * k = translator(it->m_key);
        expr * v = translator(it->m_value);
        res->m_const2bv.insert(k, v);
        translator.to().inc_ref(k);
        translator.to().inc_ref(v);
    }
    for (obj_map<func_decl, expr*>::iterator it = m_rm_const2bv.begin();
         it != m_rm_const2bv.end();
         it++)
    {
        func_decl * k = translator(it->m_key);
        expr * v = translator(it->m_value);
        res->m_rm_const2bv.insert(k, v);
        translator.to().inc_ref(k);
        translator.to().inc_ref(v);
    }
    for (obj_map<func_decl, func_decl*>::iterator it = m_uf2bvuf.begin();
         it != m_uf2bvuf.end();
         it++) {
        func_decl * k = translator(it->m_key);
        func_decl * v = translator(it->m_value);
        res->m_uf2bvuf.insert(k, v);
        translator.to().inc_ref(k);
        translator.to().inc_ref(v);
    }
    for (obj_map<func_decl, std::pair<app*, app*> >::iterator it = m_specials.begin();
         it != m_specials.end();
         it++) {
        func_decl * k = translator(it->m_key);
        app * v1 = translator(it->m_value.first);
        app * v2 = translator(it->m_value.second);
        res->m_specials.insert(k, std::pair<app*, app*>(v1, v2));
        translator.to().inc_ref(k);
        translator.to().inc_ref(v1);
        translator.to().inc_ref(v2);
    }
    return res;
}

expr_ref fpa2bv_model_converter::convert_bv2fp(sort * s, expr * sgn, expr * exp, expr * sig) {
    unsynch_mpz_manager & mpzm = m_fpa_util.fm().mpz_manager();
    unsynch_mpq_manager & mpqm = m_fpa_util.fm().mpq_manager();

    expr_ref res(m);
    mpf fp_val;

    unsigned ebits = m_fpa_util.get_ebits(s);
    unsigned sbits = m_fpa_util.get_sbits(s);

    unsigned sgn_sz = 1;
    unsigned exp_sz = ebits;
    unsigned sig_sz = sbits - 1;

    rational sgn_q(0), sig_q(0), exp_q(0);

    if (sgn) m_bv_util.is_numeral(sgn, sgn_q, sgn_sz);
    if (exp) m_bv_util.is_numeral(exp, exp_q, exp_sz);
    if (sig) m_bv_util.is_numeral(sig, sig_q, sig_sz);

    // un-bias exponent
    rational exp_unbiased_q;
    exp_unbiased_q = exp_q - m_fpa_util.fm().m_powers2.m1(ebits - 1);

    mpz sig_z; mpf_exp_t exp_z;
    mpzm.set(sig_z, sig_q.to_mpq().numerator());
    exp_z = mpzm.get_int64(exp_unbiased_q.to_mpq().numerator());

    m_fpa_util.fm().set(fp_val, ebits, sbits, !mpqm.is_zero(sgn_q.to_mpq()), exp_z, sig_z);

    mpzm.del(sig_z);

    res = m_fpa_util.mk_value(fp_val);

    TRACE("fpa2bv_mc", tout << "[" << mk_ismt2_pp(sgn, m) <<
                               " " << mk_ismt2_pp(exp, m) <<
                               " " << mk_ismt2_pp(sig, m) << "] == " <<
                               mk_ismt2_pp(res, m) << std::endl;);
    m_fpa_util.fm().del(fp_val);

    return res;
}

expr_ref fpa2bv_model_converter::convert_bv2fp(model * bv_mdl, sort * s, expr * bv) {
    SASSERT(m_bv_util.is_bv(bv));

    unsigned ebits = m_fpa_util.get_ebits(s);
    unsigned sbits = m_fpa_util.get_sbits(s);
    unsigned bv_sz = sbits + ebits;

    expr_ref sgn(m), exp(m), sig(m);
    sgn = m_bv_util.mk_extract(bv_sz - 1, bv_sz - 1, bv);
    exp = m_bv_util.mk_extract(bv_sz - 2, sbits - 1, bv);
    sig = m_bv_util.mk_extract(sbits - 2, 0, bv);

    expr_ref v_sgn(m), v_exp(m), v_sig(m);
    bv_mdl->eval(sgn, v_sgn);
    bv_mdl->eval(exp, v_exp);
    bv_mdl->eval(sig, v_sig);

    return convert_bv2fp(s, v_sgn, v_exp, v_sig);
}

expr_ref fpa2bv_model_converter::convert_bv2rm(expr * bv_rm) {
    expr_ref res(m);
    rational bv_val(0);
    unsigned sz = 0;

    if (m_bv_util.is_numeral(bv_rm, bv_val, sz)) {
        SASSERT(bv_val.is_uint64());
        switch (bv_val.get_uint64()) {
        case BV_RM_TIES_TO_AWAY: res = m_fpa_util.mk_round_nearest_ties_to_away(); break;
        case BV_RM_TIES_TO_EVEN: res = m_fpa_util.mk_round_nearest_ties_to_even(); break;
        case BV_RM_TO_NEGATIVE: res = m_fpa_util.mk_round_toward_negative(); break;
        case BV_RM_TO_POSITIVE: res = m_fpa_util.mk_round_toward_positive(); break;
        case BV_RM_TO_ZERO:
        default: res = m_fpa_util.mk_round_toward_zero();
        }
    }

    return res;
}

expr_ref fpa2bv_model_converter::convert_bv2rm(model * bv_mdl, expr * val) {
    expr_ref res(m);
    expr_ref eval_v(m);

    if (val && bv_mdl->eval(val, eval_v, true))
        res = convert_bv2rm(eval_v);

    return res;
}

expr_ref fpa2bv_model_converter::rebuild_floats(model * bv_mdl, sort * s, expr * e) {
    expr_ref result(m);
    TRACE("fpa2bv_mc", tout << "rebuild floats in " << mk_ismt2_pp(s, m) << " for " << mk_ismt2_pp(e, m) << std::endl;);

    if (m_fpa_util.is_float(s)) {
        if (m_fpa_util.is_numeral(e)) {
            result = e;
        }
        else {
            SASSERT(m_bv_util.is_bv(e) && m_bv_util.get_bv_size(e) == (m_fpa_util.get_ebits(s) + m_fpa_util.get_sbits(s)));
            result = convert_bv2fp(bv_mdl, s, e);
        }
    }
    else if (m_fpa_util.is_rm(s)) {
        if (m_fpa_util.is_rm_numeral(e)) {
            result = e;
        }
        else {
            SASSERT(m_bv_util.is_bv(e) && m_bv_util.get_bv_size(e) == 3);
            result = convert_bv2rm(bv_mdl, e);
        }
    }
    else if (is_app(e)) {
        app * a = to_app(e);
        expr_ref_vector new_args(m);
        for (unsigned i = 0; i < a->get_num_args(); i++)
            new_args.push_back(rebuild_floats(bv_mdl, a->get_decl()->get_domain()[i], a->get_arg(i)));
        result = m.mk_app(a->get_decl(), new_args.size(), new_args.c_ptr());
    }

    return result;
}

fpa2bv_model_converter::array_model fpa2bv_model_converter::convert_array_func_interp(func_decl * f, func_decl * bv_f, model * bv_mdl) {
    SASSERT(f->get_arity() == 0);
    array_util arr_util(m);

    array_model am(m);
    sort_ref_vector array_domain(m);    
    unsigned arity = f->get_range()->get_num_parameters()-1;

    expr_ref as_arr_mdl(m);
    as_arr_mdl = bv_mdl->get_const_interp(bv_f);
    if (as_arr_mdl == 0) return am;
    TRACE("fpa2bv_mc", tout << "arity=0 func_interp for " << mk_ismt2_pp(f, m) << " := " << mk_ismt2_pp(as_arr_mdl, m) << std::endl;);
    SASSERT(arr_util.is_as_array(as_arr_mdl));
    for (unsigned i = 0; i < arity; i++)
        array_domain.push_back(to_sort(f->get_range()->get_parameter(i).get_ast()));
    sort * rng = to_sort(f->get_range()->get_parameter(arity).get_ast());
        
    bv_f = arr_util.get_as_array_func_decl(to_app(as_arr_mdl));

    am.new_float_fd = m.mk_fresh_func_decl(arity, array_domain.c_ptr(), rng);
    am.new_float_fi = convert_func_interp(am.new_float_fd, bv_f, bv_mdl);    
    am.bv_fd = bv_f;
    am.result = arr_util.mk_as_array(f->get_range(), am.new_float_fd);
    return am;
}

func_interp * fpa2bv_model_converter::convert_func_interp(func_decl * f, func_decl * bv_f, model * bv_mdl) {        
    SASSERT(f->get_arity() > 0);
    func_interp * result = 0;
    sort * rng = f->get_range();
    sort * const * dmn = f->get_domain();     

    unsigned arity = bv_f->get_arity();
    func_interp * bv_fi = bv_mdl->get_func_interp(bv_f);

    if (bv_fi != 0) {
        fpa_rewriter rw(m);
        expr_ref ai(m);
        result = alloc(func_interp, m, arity);

        for (unsigned i = 0; i < bv_fi->num_entries(); i++) {
            func_entry const * bv_fe = bv_fi->get_entry(i);
            expr * const * bv_args = bv_fe->get_args();
            expr_ref_buffer new_args(m);

            for (unsigned j = 0; j < arity; j++) {
                sort * ft_dj = dmn[j];
                expr * bv_aj = bv_args[j];                
                ai = rebuild_floats(bv_mdl, ft_dj, bv_aj);
                m_th_rw(ai);
                new_args.push_back(ai);
            }

            expr_ref bv_fres(m), ft_fres(m);
            bv_fres = bv_fe->get_result();
            ft_fres = rebuild_floats(bv_mdl, rng, bv_fres);
            m_th_rw(ft_fres);
            result->insert_new_entry(new_args.c_ptr(), ft_fres);
        }

        expr_ref bv_els(m), ft_els(m);
        bv_els = bv_fi->get_else();
        ft_els = rebuild_floats(bv_mdl, rng, bv_els);
        m_th_rw(ft_els);
        result->set_else(ft_els);        
    }

    return result;
}

void fpa2bv_model_converter::convert(model * bv_mdl, model * float_mdl) {
    TRACE("fpa2bv_mc", tout << "BV Model: " << std::endl;
    for (unsigned i = 0; i < bv_mdl->get_num_constants(); i++)
        tout << bv_mdl->get_constant(i)->get_name() << " --> " <<
        mk_ismt2_pp(bv_mdl->get_const_interp(bv_mdl->get_constant(i)), m) << std::endl;
    for (unsigned i = 0; i < bv_mdl->get_num_functions(); i++) {
        func_decl * f = bv_mdl->get_function(i);
        tout << f->get_name() << "(...) := " << std::endl;
        func_interp * fi = bv_mdl->get_func_interp(f);
        for (unsigned j = 0; j < fi->num_entries(); j++) {
            func_entry const * fe = fi->get_entry(j);
            for (unsigned k = 0; k < f->get_arity(); k++) {
                tout << mk_ismt2_pp(fe->get_arg(k), m) << " ";
            }
            tout << "--> " << mk_ismt2_pp(fe->get_result(), m) << std::endl;
        }
        tout << "else " << mk_ismt2_pp(fi->get_else(), m) << std::endl;
    });

    obj_hashtable<func_decl> seen;

    for (obj_map<func_decl, std::pair<app*, app*> >::iterator it = m_specials.begin();
         it != m_specials.end();
         it++) {
        func_decl * f = it->m_key;
        expr_ref pzero(m), nzero(m);
        pzero = m_fpa_util.mk_pzero(f->get_range());
        nzero = m_fpa_util.mk_nzero(f->get_range());

        expr_ref pn(m), np(m);
        bv_mdl->eval(it->m_value.first, pn, true);
        bv_mdl->eval(it->m_value.second, np, true);
        seen.insert(it->m_value.first->get_decl());
        seen.insert(it->m_value.second->get_decl());

        rational pn_num, np_num;
        unsigned bv_sz;
        m_bv_util.is_numeral(pn, pn_num, bv_sz);
        m_bv_util.is_numeral(np, np_num, bv_sz);

        func_interp * flt_fi = alloc(func_interp, m, f->get_arity());
        expr * pn_args[2] = { pzero, nzero };
        if (pn != np) flt_fi->insert_new_entry(pn_args, (pn_num.is_one() ? nzero : pzero));
        flt_fi->set_else(np_num.is_one() ? nzero : pzero);

        float_mdl->register_decl(f, flt_fi);
        TRACE("fpa2bv_mc", tout << "fp.min/fp.max special: " << std::endl <<
                            mk_ismt2_pp(f, m) << " == " << mk_ismt2_pp(flt_fi->get_interp(), m) << std::endl;);
    }

    for (obj_map<func_decl, expr*>::iterator it = m_const2bv.begin();
         it != m_const2bv.end();
         it++)
    {
        func_decl * var = it->m_key;
        app * val = to_app(it->m_value);
        SASSERT(m_fpa_util.is_float(var->get_range()));
        SASSERT(var->get_range()->get_num_parameters() == 2);

        expr_ref sgn(m), sig(m), exp(m);
        bv_mdl->eval(val->get_arg(0), sgn, true);
        bv_mdl->eval(val->get_arg(1), exp, true);
        bv_mdl->eval(val->get_arg(2), sig, true);

        SASSERT(val->is_app_of(m_fpa_util.get_family_id(), OP_FPA_FP));

#ifdef Z3DEBUG
        SASSERT(to_app(val->get_arg(0))->get_decl()->get_arity() == 0);
        SASSERT(to_app(val->get_arg(1))->get_decl()->get_arity() == 0);
        SASSERT(to_app(val->get_arg(2))->get_decl()->get_arity() == 0);
        seen.insert(to_app(val->get_arg(0))->get_decl());
        seen.insert(to_app(val->get_arg(1))->get_decl());
        seen.insert(to_app(val->get_arg(2))->get_decl());
#else
        SASSERT(a->get_arg(0)->get_kind() == OP_EXTRACT);
        SASSERT(to_app(a->get_arg(0))->get_arg(0)->get_kind() == OP_EXTRACT);
        seen.insert(to_app(to_app(val->get_arg(0))->get_arg(0))->get_decl());
#endif

        if (!sgn && !sig && !exp)
            continue;

        expr_ref cv(m);
        cv = convert_bv2fp(var->get_range(), sgn, exp, sig);
        float_mdl->register_decl(var, cv);

        TRACE("fpa2bv_mc", tout << var->get_name() << " == " << mk_ismt2_pp(cv, m) << std::endl;);
    }

    for (obj_map<func_decl, expr*>::iterator it = m_rm_const2bv.begin();
         it != m_rm_const2bv.end();
         it++)
    {
        func_decl * var = it->m_key;
        SASSERT(m_fpa_util.is_rm(var->get_range()));
        expr * val = it->m_value;
        SASSERT(m_fpa_util.is_bv2rm(val));
        expr * bvval = to_app(val)->get_arg(0);
        expr_ref fv(m);
        fv = convert_bv2rm(bv_mdl, bvval);
        TRACE("fpa2bv_mc", tout << var->get_name() << " == " << mk_ismt2_pp(fv, m) << ")" << std::endl;);
        float_mdl->register_decl(var, fv);
        seen.insert(to_app(bvval)->get_decl());
    }

    for (obj_map<func_decl, func_decl*>::iterator it = m_uf2bvuf.begin();
        it != m_uf2bvuf.end();
        it++) {
        seen.insert(it->m_value);

        func_decl * f = it->m_key;        
        if (f->get_arity() == 0)
        {
            array_util au(m);
            if (au.is_array(f->get_range())) {
                array_model am = convert_array_func_interp(f, it->m_value, bv_mdl);
                if (am.new_float_fd) float_mdl->register_decl(am.new_float_fd, am.new_float_fi);
                if (am.result) float_mdl->register_decl(f, am.result);
                if (am.bv_fd) seen.insert(am.bv_fd);
            }
            else {
                // Just keep.
                SASSERT(!m_fpa_util.is_float(f->get_range()) && !m_fpa_util.is_rm(f->get_range()));
                expr_ref val(m);
                bv_mdl->eval(it->m_value, val);
                if (val) float_mdl->register_decl(f, val);
            }
        }            
        else {
            func_interp * fmv = convert_func_interp(f, it->m_value, bv_mdl);
            if (fmv) float_mdl->register_decl(f, fmv);
        }
    }

    // Keep all the non-float constants.
    unsigned sz = bv_mdl->get_num_constants();
    for (unsigned i = 0; i < sz; i++)
    {
        func_decl * c = bv_mdl->get_constant(i);
        if (!seen.contains(c))
            float_mdl->register_decl(c, bv_mdl->get_const_interp(c));
    }

    // And keep everything else
    sz = bv_mdl->get_num_functions();
    for (unsigned i = 0; i < sz; i++)
    {
        func_decl * f = bv_mdl->get_function(i);
        if (!seen.contains(f))
        {
            TRACE("fpa2bv_mc", tout << "Keeping: " << mk_ismt2_pp(f, m) << std::endl;);
            func_interp * val = bv_mdl->get_func_interp(f)->copy();
            float_mdl->register_decl(f, val);
        }
    }

    sz = bv_mdl->get_num_uninterpreted_sorts();
    for (unsigned i = 0; i < sz; i++)
    {
        sort * s = bv_mdl->get_uninterpreted_sort(i);
        ptr_vector<expr> u = bv_mdl->get_universe(s);
        float_mdl->register_usort(s, u.size(), u.c_ptr());
    }
}

model_converter * mk_fpa2bv_model_converter(ast_manager & m, fpa2bv_converter const & conv) {
    return alloc(fpa2bv_model_converter, m, conv);
}
