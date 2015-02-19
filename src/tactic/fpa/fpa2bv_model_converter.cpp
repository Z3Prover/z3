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
    for (obj_map<func_decl, func_decl_triple>::iterator it = m_uf23bvuf.begin();
         it != m_uf23bvuf.end();
         it++) {
        const symbol & n = it->m_key->get_name();
        out << "\n  (" << n << " ";
        unsigned indent = n.size() + 4;
        out << mk_ismt2_pp(it->m_value.f_sgn, m, indent) << " ; " <<
            mk_ismt2_pp(it->m_value.f_sig, m, indent) << " ; " <<
            mk_ismt2_pp(it->m_value.f_exp, m, indent) << " ; " <<
            ")";
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
    return res;
}

void fpa2bv_model_converter::convert(model * bv_mdl, model * float_mdl) {
    fpa_util fu(m);
    bv_util bu(m);
    mpf fp_val;
    unsynch_mpz_manager & mpzm = fu.fm().mpz_manager();
    unsynch_mpq_manager & mpqm = fu.fm().mpq_manager();

    TRACE("fpa2bv_mc", tout << "BV Model: " << std::endl;
    for (unsigned i = 0; i < bv_mdl->get_num_constants(); i++)
        tout << bv_mdl->get_constant(i)->get_name() << " --> " <<
        mk_ismt2_pp(bv_mdl->get_const_interp(bv_mdl->get_constant(i)), m) << std::endl;
    );

    obj_hashtable<func_decl> seen;

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

        expr_ref sgn(m), sig(m), exp(m);        
        bv_mdl->eval(a->get_arg(0), sgn, true);        
        bv_mdl->eval(a->get_arg(1), exp, true);
        bv_mdl->eval(a->get_arg(2), sig, true);

        SASSERT(a->is_app_of(fu.get_family_id(), OP_FPA_FP));

#ifdef Z3DEBUG                
        SASSERT(to_app(a->get_arg(0))->get_decl()->get_arity() == 0);
        SASSERT(to_app(a->get_arg(1))->get_decl()->get_arity() == 0);
        SASSERT(to_app(a->get_arg(2))->get_decl()->get_arity() == 0);        
        seen.insert(to_app(a->get_arg(0))->get_decl());
        seen.insert(to_app(a->get_arg(1))->get_decl());
        seen.insert(to_app(a->get_arg(2))->get_decl());
#else        
        SASSERT(a->get_arg(0)->get_kind() == OP_EXTRACT);
        SASSERT(to_app(a->get_arg(0))->get_arg(0)->get_kind() == OP_EXTRACT);
        seen.insert(to_app(to_app(a->get_arg(0))->get_arg(0))->get_decl());
#endif

        if (!sgn && !sig && !exp)
            continue;

        unsigned sgn_sz = bu.get_bv_size(m.get_sort(a->get_arg(0)));        
        unsigned exp_sz = bu.get_bv_size(m.get_sort(a->get_arg(1)));
        unsigned sig_sz = bu.get_bv_size(m.get_sort(a->get_arg(2))) - 1;

        rational sgn_q(0), sig_q(0), exp_q(0);

        if (sgn) bu.is_numeral(sgn, sgn_q, sgn_sz);
        if (sig) bu.is_numeral(sig, sig_q, sig_sz);
        if (exp) bu.is_numeral(exp, exp_q, exp_sz);

        // un-bias exponent
        rational exp_unbiased_q;
        exp_unbiased_q = exp_q - fu.fm().m_powers2.m1(ebits - 1);

        mpz sig_z; mpf_exp_t exp_z;
        mpzm.set(sig_z, sig_q.to_mpq().numerator());
        exp_z = mpzm.get_int64(exp_unbiased_q.to_mpq().numerator());

        TRACE("fpa2bv_mc", tout << var->get_name() << " == [" << sgn_q.to_string() << " " <<
              mpzm.to_string(sig_z) << " " << exp_z << "(" << exp_q.to_string() << ")]" << std::endl;);

        fu.fm().set(fp_val, ebits, sbits, !mpqm.is_zero(sgn_q.to_mpq()), sig_z, exp_z);

        float_mdl->register_decl(var, fu.mk_value(fp_val));

        mpzm.del(sig_z);
    }

    for (obj_map<func_decl, expr*>::iterator it = m_rm_const2bv.begin();
         it != m_rm_const2bv.end();
         it++)
    {
        func_decl * var = it->m_key;
        expr * v = it->m_value;
        expr_ref eval_v(m);
        SASSERT(fu.is_rm(var->get_range()));
        rational bv_val(0);
        unsigned sz = 0;
        if (v && bv_mdl->eval(v, eval_v, true) && bu.is_numeral(eval_v, bv_val, sz)) {
            TRACE("fpa2bv_mc", tout << var->get_name() << " == " << bv_val.to_string() << std::endl;);
            SASSERT(bv_val.is_uint64());
            switch (bv_val.get_uint64())
            {
            case BV_RM_TIES_TO_AWAY: float_mdl->register_decl(var, fu.mk_round_nearest_ties_to_away()); break;
            case BV_RM_TIES_TO_EVEN: float_mdl->register_decl(var, fu.mk_round_nearest_ties_to_even()); break;
            case BV_RM_TO_NEGATIVE: float_mdl->register_decl(var, fu.mk_round_toward_negative()); break;
            case BV_RM_TO_POSITIVE: float_mdl->register_decl(var, fu.mk_round_toward_positive()); break;
            case BV_RM_TO_ZERO:
            default: float_mdl->register_decl(var, fu.mk_round_toward_zero());
            }
            SASSERT(v->get_kind() == AST_APP);
            seen.insert(to_app(v)->get_decl());
        }
    }

    for (obj_map<func_decl, func_decl*>::iterator it = m_uf2bvuf.begin();
         it != m_uf2bvuf.end();
         it++)
         seen.insert(it->m_value);

    for (obj_map<func_decl, func_decl_triple>::iterator it = m_uf23bvuf.begin();
         it != m_uf23bvuf.end();
         it++)
    {
        seen.insert(it->m_value.f_sgn);
        seen.insert(it->m_value.f_sig);
        seen.insert(it->m_value.f_exp);
    }

    fu.fm().del(fp_val);

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
                                            obj_map<func_decl, func_decl_triple> const & uf23bvuf) {
    return alloc(fpa2bv_model_converter, m, const2bv, rm_const2bv, uf2bvuf, uf23bvuf);
}
