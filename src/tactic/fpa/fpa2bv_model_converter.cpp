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
    for (obj_hashtable<func_decl>::iterator it = m_decls_to_hide.begin();
         it != m_decls_to_hide.end();
         it++) {
        out << "\n  to hide: " << mk_ismt2_pp(*it, m);
    }
    out << ")" << std::endl;
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
    for (obj_hashtable<func_decl>::iterator it = m_decls_to_hide.begin();
         it != m_decls_to_hide.end();
         it++) {
        func_decl * k = translator(*it);
        res->m_decls_to_hide.insert(k);
        translator.to().inc_ref(k);
    }
    return res;
}

expr_ref fpa2bv_model_converter::convert_bv2fp(sort * s, expr * sgn, expr * exp, expr * sig) const {
    fpa_util fu(m);
    bv_util bu(m);
    unsynch_mpz_manager & mpzm = fu.fm().mpz_manager();
    unsynch_mpq_manager & mpqm = fu.fm().mpq_manager();

    expr_ref res(m);
    mpf fp_val;

    unsigned ebits = fu.get_ebits(s);
    unsigned sbits = fu.get_sbits(s);

    unsigned sgn_sz = 1;
    unsigned exp_sz = ebits;
    unsigned sig_sz = sbits - 1;

    rational sgn_q(0), sig_q(0), exp_q(0);

    if (sgn) bu.is_numeral(sgn, sgn_q, sgn_sz);
    if (exp) bu.is_numeral(exp, exp_q, exp_sz);
    if (sig) bu.is_numeral(sig, sig_q, sig_sz);

    // un-bias exponent
    rational exp_unbiased_q;
    exp_unbiased_q = exp_q - fu.fm().m_powers2.m1(ebits - 1);

    mpz sig_z; mpf_exp_t exp_z;
    mpzm.set(sig_z, sig_q.to_mpq().numerator());
    exp_z = mpzm.get_int64(exp_unbiased_q.to_mpq().numerator());

    fu.fm().set(fp_val, ebits, sbits, !mpqm.is_zero(sgn_q.to_mpq()), sig_z, exp_z);

    mpzm.del(sig_z);

    res = fu.mk_value(fp_val);

    TRACE("fpa2bv_mc", tout << "[" << mk_ismt2_pp(sgn, m) << 
                               " " << mk_ismt2_pp(exp, m) << 
                               " " << mk_ismt2_pp(sig, m) << "] == " << 
                               mk_ismt2_pp(res, m) << std::endl;);
    fu.fm().del(fp_val);

    return res;
}

expr_ref fpa2bv_model_converter::convert_bv2fp(model * bv_mdl, sort * s, expr * bv) const {    
    fpa_util fu(m);
    bv_util bu(m);

    SASSERT(bu.is_bv(bv));

    unsigned ebits = fu.get_ebits(s);
    unsigned sbits = fu.get_sbits(s);
    unsigned bv_sz = sbits + ebits;

    expr_ref sgn(m), exp(m), sig(m);
    sgn = bu.mk_extract(bv_sz - 1, bv_sz - 1, bv);
    exp = bu.mk_extract(bv_sz - 2, sbits - 1, bv);
    sig = bu.mk_extract(sbits - 2, 0, bv);

    expr_ref v_sgn(m), v_exp(m), v_sig(m);
    bv_mdl->eval(sgn, v_sgn);
    bv_mdl->eval(exp, v_exp);
    bv_mdl->eval(sig, v_sig);

    return convert_bv2fp(s, v_sgn, v_exp, v_sig);
}

expr_ref fpa2bv_model_converter::convert_bv2rm(expr * eval_v) const {
    fpa_util fu(m);
    bv_util bu(m);
    expr_ref res(m);   
    rational bv_val(0);
    unsigned sz = 0;

    if (bu.is_numeral(eval_v, bv_val, sz)) {
        SASSERT(bv_val.is_uint64());
        switch (bv_val.get_uint64()) {
        case BV_RM_TIES_TO_AWAY: res = fu.mk_round_nearest_ties_to_away(); break;
        case BV_RM_TIES_TO_EVEN: res = fu.mk_round_nearest_ties_to_even(); break;
        case BV_RM_TO_NEGATIVE: res = fu.mk_round_toward_negative(); break;
        case BV_RM_TO_POSITIVE: res = fu.mk_round_toward_positive(); break;
        case BV_RM_TO_ZERO:
        default: res = fu.mk_round_toward_zero();
        }
    }

    return res;
}

expr_ref fpa2bv_model_converter::convert_bv2rm(model * bv_mdl, func_decl * var, expr * val) const {
    fpa_util fu(m);
    bv_util bu(m);
    expr_ref res(m);

    expr_ref eval_v(m);        

    if (val && bv_mdl->eval(val, eval_v, true))
        res = convert_bv2rm(eval_v);

    return res;
}

void fpa2bv_model_converter::convert(model * bv_mdl, model * float_mdl) {
    fpa_util fu(m);
    bv_util bu(m);

    TRACE("fpa2bv_mc", tout << "BV Model: " << std::endl;
    for (unsigned i = 0; i < bv_mdl->get_num_constants(); i++)
        tout << bv_mdl->get_constant(i)->get_name() << " --> " <<
        mk_ismt2_pp(bv_mdl->get_const_interp(bv_mdl->get_constant(i)), m) << std::endl;
    );

    obj_hashtable<func_decl> seen;

    for (obj_hashtable<func_decl>::iterator it = m_decls_to_hide.begin();
         it != m_decls_to_hide.end();
         it++)
         seen.insert(*it);

    for (obj_map<func_decl, expr*>::iterator it = m_const2bv.begin();
         it != m_const2bv.end();
         it++)
    {
        func_decl * var = it->m_key;
        app * val = to_app(it->m_value);
        SASSERT(fu.is_float(var->get_range()));
        SASSERT(var->get_range()->get_num_parameters() == 2);

        expr_ref sgn(m), sig(m), exp(m);        
        bv_mdl->eval(val->get_arg(0), sgn, true);
        bv_mdl->eval(val->get_arg(1), exp, true);
        bv_mdl->eval(val->get_arg(2), sig, true);

        SASSERT(val->is_app_of(fu.get_family_id(), OP_FPA_FP));

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
        SASSERT(fu.is_rm(var->get_range()));
        expr * val = it->m_value;
        expr_ref fv(m);
        fv = convert_bv2rm(bv_mdl, var, val);
        TRACE("fpa2bv_mc", tout << var->get_name() << " == " << mk_ismt2_pp(fv, m) << std::endl;);
        float_mdl->register_decl(var, fv);
        seen.insert(to_app(val)->get_decl());
    }

    for (obj_map<func_decl, func_decl*>::iterator it = m_uf2bvuf.begin();
         it != m_uf2bvuf.end();
         it++) {
        seen.insert(it->m_value);

        func_decl * f = it->m_key;
        unsigned arity = f->get_arity();
        sort * rng = f->get_range();
        func_interp * flt_fi = alloc(func_interp, m, f->get_arity());

        func_interp * bv_fi = bv_mdl->get_func_interp(it->m_value);
        SASSERT(bv_fi->args_are_values());

        for (unsigned i = 0; i < bv_fi->num_entries(); i++) {
            func_entry const * bv_fe = bv_fi->get_entry(i);
            expr * const * bv_args = bv_fe->get_args();
            expr_ref_buffer new_args(m);

            for (unsigned j = 0; j < arity; j++) {
                sort * dj = f->get_domain(j);
                expr * aj = bv_args[j];
                if (fu.is_float(dj))
                    new_args.push_back(convert_bv2fp(bv_mdl, dj, aj));
                else if (fu.is_rm(dj)) {
                    expr_ref fv(m);
                    fv = convert_bv2rm(aj);
                    new_args.push_back(fv);
                }
                else
                    new_args.push_back(aj);
            }
            
            expr_ref ret(m);
            ret = bv_fe->get_result();
            if (fu.is_float(rng))
                ret = convert_bv2fp(bv_mdl, rng, ret);
            else if (fu.is_rm(rng))
                ret = convert_bv2rm(ret);

            flt_fi->insert_new_entry(new_args.c_ptr(), ret);            
        }

        expr_ref els(m);
        els = bv_fi->get_else();
        if (fu.is_float(rng))
            els = convert_bv2fp(bv_mdl, rng, els);
        else if (fu.is_rm(rng))
            els = convert_bv2rm(els);

        flt_fi->set_else(els);

        float_mdl->register_decl(f, flt_fi);        
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
            func_interp * val = bv_mdl->get_func_interp(f);
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

model_converter * mk_fpa2bv_model_converter(ast_manager & m,
                                            obj_map<func_decl, expr*> const & const2bv,
                                            obj_map<func_decl, expr*> const & rm_const2bv,
                                            obj_map<func_decl, func_decl*> const & uf2bvuf,
                                            obj_hashtable<func_decl> const & decls_to_hide) {
    return alloc(fpa2bv_model_converter, m, const2bv, rm_const2bv, uf2bvuf, decls_to_hide);
}
