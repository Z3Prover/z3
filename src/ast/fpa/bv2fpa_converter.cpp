/*++
    Copyright (c) 2012 Microsoft Corporation

Module Name:

    bv2fpa_converter.cpp

Abstract:

    Model conversion for fpa2bv_converter

Author:

    Christoph (cwinter) 2016-10-15

Notes:

--*/
#include<math.h>

#include "ast/ast_smt2_pp.h"
#include "ast/well_sorted.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/fpa_rewriter.h"

#include "ast/fpa/bv2fpa_converter.h"


bv2fpa_converter::bv2fpa_converter(ast_manager & m) :
    m(m),
    m_fpa_util(m),
    m_bv_util(m),
    m_th_rw(m) {
}

bv2fpa_converter::bv2fpa_converter(ast_manager & m, fpa2bv_converter & conv) :
    m(m),
    m_fpa_util(m),
    m_bv_util(m),
    m_th_rw(m) {
    for (auto const& kv : conv.m_const2bv) {
        m_const2bv.insert(kv.m_key, kv.m_value);
        m.inc_ref(kv.m_key);
        m.inc_ref(kv.m_value);
    }
    for (auto const& kv : conv.m_rm_const2bv) {
        m_rm_const2bv.insert(kv.m_key, kv.m_value);
        m.inc_ref(kv.m_key);
        m.inc_ref(kv.m_value);
    }
    for (auto const& kv : conv.m_uf2bvuf) {
        m_uf2bvuf.insert(kv.m_key, kv.m_value);
        m.inc_ref(kv.m_key);
        m.inc_ref(kv.m_value);
    }
    for (auto const& kv : conv.m_min_max_ufs) {
        m_min_max_specials.insert(kv.m_key, kv.m_value);
        m.inc_ref(kv.m_key);
        m.inc_ref(kv.m_value.first);
        m.inc_ref(kv.m_value.second);
    }
}

bv2fpa_converter::~bv2fpa_converter() {
    dec_ref_map_key_values(m, m_const2bv);
    dec_ref_map_key_values(m, m_rm_const2bv);
    for (auto const& kv : m_uf2bvuf) {
        m.dec_ref(kv.m_key);
        m.dec_ref(kv.m_value);
    }
    for (auto const& kv : m_min_max_specials) {
        m.dec_ref(kv.m_key);
        m.dec_ref(kv.m_value.first);
        m.dec_ref(kv.m_value.second);
    }
    m_uf2bvuf.reset();
    m_min_max_specials.reset();
}

expr_ref bv2fpa_converter::convert_bv2fp(sort * s, expr * sgn, expr * exp, expr * sig) {
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

    TRACE("bv2fpa", tout << "[" << mk_ismt2_pp(sgn, m) <<
                            " " << mk_ismt2_pp(exp, m) <<
                            " " << mk_ismt2_pp(sig, m) << "] == " <<
                            mk_ismt2_pp(res, m) << std::endl;);
    m_fpa_util.fm().del(fp_val);

    return res;
}

expr_ref bv2fpa_converter::convert_bv2fp(model_core * mc, sort * s, expr * bv) {
    SASSERT(m_bv_util.is_bv(bv));

    unsigned ebits = m_fpa_util.get_ebits(s);
    unsigned sbits = m_fpa_util.get_sbits(s);
    unsigned bv_sz = sbits + ebits;

    expr_ref bv_num(bv, m);
    if (!m_bv_util.is_numeral(bv) && is_app(bv)) {
        if (!mc->eval(to_app(bv)->get_decl(), bv_num)) {
            bv_num = m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(bv));
        }
    }
    expr_ref sgn(m), exp(m), sig(m);
    sgn = m_bv_util.mk_extract(bv_sz - 1, bv_sz - 1, bv_num);
    exp = m_bv_util.mk_extract(bv_sz - 2, sbits - 1, bv_num);
    sig = m_bv_util.mk_extract(sbits - 2, 0, bv_num);

    expr_ref v_sgn(m), v_exp(m), v_sig(m);
    m_th_rw(sgn, v_sgn);
    m_th_rw(exp, v_exp);
    m_th_rw(sig, v_sig);

    return convert_bv2fp(s, v_sgn, v_exp, v_sig);
}

expr_ref bv2fpa_converter::convert_bv2rm(expr * bv_rm) {
    expr_ref res(m);
    rational bv_val;

    if (m_bv_util.is_numeral(bv_rm, bv_val)) {
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
    else {
        std::cout << expr_ref(bv_rm, m) << " not converted\n";
    }

    return res;
}

expr_ref bv2fpa_converter::convert_bv2rm(model_core * mc, expr * val) {
    expr_ref res(m);

    if (val) {
        expr_ref eval_v(m);
        if (m_bv_util.is_numeral(val))
            res = convert_bv2rm(val);
        else if (is_app(val) && mc->eval(to_app(val)->get_decl(), eval_v))
            res = convert_bv2rm(eval_v);
        else {
            // BUG: doesn't work for parametric definition
            // needs to be an ite expression.
            res = m_fpa_util.mk_round_toward_zero();
        }
    }

    return res;
}

expr_ref bv2fpa_converter::rebuild_floats(model_core * mc, sort * s, expr * e) {
    expr_ref result(m);
    TRACE("bv2fpa_rebuild", tout << "rebuild floats in " << mk_ismt2_pp(s, m) << " for ";
                    if (e) tout << mk_ismt2_pp(e, m);
                    else tout << "nil";
                    tout << std::endl; );

    if (m_fpa_util.is_float(s)) {
        if (e == nullptr)
            result = m_fpa_util.mk_pzero(s);
        else if (m_fpa_util.is_numeral(e))
            result = e;
        else {
            SASSERT(m_bv_util.is_bv(e) && m_bv_util.get_bv_size(e) == (m_fpa_util.get_ebits(s) + m_fpa_util.get_sbits(s)));
            result = convert_bv2fp(mc, s, e);
        }
    }
    else if (m_fpa_util.is_rm(s)) {
        if (e == nullptr)
            result = m_fpa_util.mk_round_toward_zero();
        else if (m_fpa_util.is_rm_numeral(e))
            result = e;
        else {
            SASSERT(m_bv_util.is_bv(e) && m_bv_util.get_bv_size(e) == 3);
            result = convert_bv2rm(mc, e);
        }
    }
    else if (is_app(e)) {
        app * a = to_app(e);
        expr_ref_vector new_args(m);
        for (expr* arg : *a) {
            new_args.push_back(rebuild_floats(mc, m.get_sort(arg), arg));
        }
        result = m.mk_app(a->get_decl(), new_args.size(), new_args.c_ptr());
    }
    else if (is_var(e)) {
        result = e;
    }
    SASSERT(!result || m.get_sort(result) == s);
    return result;
}

bv2fpa_converter::array_model bv2fpa_converter::convert_array_func_interp(model_core * mc, func_decl * f, func_decl * bv_f) {
    SASSERT(f->get_arity() == 0);
    array_util arr_util(m);

    array_model am(m);
    sort_ref_vector array_domain(m);
    unsigned arity = f->get_range()->get_num_parameters()-1;

    expr_ref as_arr_mdl(m);
    as_arr_mdl = mc->get_const_interp(bv_f);
    if (as_arr_mdl == 0) return am;
    TRACE("bv2fpa", tout << "arity=0 func_interp for " << mk_ismt2_pp(f, m) << " := " << mk_ismt2_pp(as_arr_mdl, m) << std::endl;);
    SASSERT(arr_util.is_as_array(as_arr_mdl));
    for (unsigned i = 0; i < arity; i++)
        array_domain.push_back(to_sort(f->get_range()->get_parameter(i).get_ast()));
    sort * rng = to_sort(f->get_range()->get_parameter(arity).get_ast());

    bv_f = arr_util.get_as_array_func_decl(to_app(as_arr_mdl));

    am.new_float_fd = m.mk_fresh_func_decl(arity, array_domain.c_ptr(), rng);
    am.new_float_fi = convert_func_interp(mc, am.new_float_fd, bv_f);
    am.bv_fd = bv_f;
    am.result = arr_util.mk_as_array(am.new_float_fd);
    return am;
}

func_interp * bv2fpa_converter::convert_func_interp(model_core * mc, func_decl * f, func_decl * bv_f) {
    SASSERT(f->get_arity() > 0);
    func_interp * result = nullptr;
    sort * rng = f->get_range();
    sort * const * dmn = f->get_domain();

    unsigned arity = bv_f->get_arity();
    func_interp * bv_fi = mc->get_func_interp(bv_f);
    result = alloc(func_interp, m, arity);

    if (bv_fi) {
        fpa_rewriter rw(m);

        for (unsigned i = 0; i < bv_fi->num_entries(); i++) {
            func_entry const * bv_fe = bv_fi->get_entry(i);
            expr * const * bv_args = bv_fe->get_args();
            expr_ref_buffer new_args(m);

            for (unsigned j = 0; j < arity; j++) {
                sort * ft_dj = dmn[j];
                expr * bv_aj = bv_args[j];
                expr_ref ai = rebuild_floats(mc, ft_dj, to_app(bv_aj));
                m_th_rw(ai);
                new_args.push_back(std::move(ai));
            }

            expr_ref bv_fres(m);
            bv_fres = bv_fe->get_result();
            expr_ref ft_fres = rebuild_floats(mc, rng, to_app(bv_fres));
            m_th_rw(ft_fres);
            TRACE("bv2fpa",
                  tout << "func_interp entry #" << i << ":" << std::endl;
                  tout << "(" << bv_f->get_name();
                  for (unsigned i = 0; i < bv_f->get_arity(); i++)
                      tout << " " << mk_ismt2_pp(bv_args[i], m);
                  tout << ") = " << mk_ismt2_pp(bv_fres, m) << std::endl;
                  tout << " --> " << std::endl;
                  tout << "(" << f->get_name();
                  for (unsigned i = 0; i < new_args.size(); i++)
                      tout << " " << mk_ismt2_pp(new_args[i], m);
                  tout << ") = " << mk_ismt2_pp(ft_fres, m) << std::endl;);
            func_entry * fe = result->get_entry(new_args.c_ptr());
            if (fe == nullptr) {
                // Avoid over-specification of a partially interpreted theory function
                if (f->get_family_id() != m_fpa_util.get_family_id() ||
                    m_fpa_util.is_considered_uninterpreted(f, new_args.size(), new_args.c_ptr()))
                    result->insert_new_entry(new_args.c_ptr(), ft_fres);
            }
            else {
                // The BV model may have multiple equivalent entries using different
                // representations of NaN. We can only keep one and we check that
                // the results for all those entries are the same.
                if (m_fpa_util.is_float(rng) && ft_fres != fe->get_result())
                    throw default_exception("BUG: UF function entries disagree with each other");
            }
        }

        expr_ref bv_els(m);
        bv_els = bv_fi->get_else();
        if (bv_els) {
            expr_ref ft_els = rebuild_floats(mc, rng, bv_els);
            m_th_rw(ft_els);
            TRACE("bv2fpa", tout << "else=" << mk_ismt2_pp(ft_els, m) << std::endl;);
            result->set_else(ft_els);
        }
    }

    return result;
}

void bv2fpa_converter::convert_consts(model_core * mc, model_core * target_model, obj_hashtable<func_decl> & seen) {
    for (auto const& kv : m_const2bv) {
        func_decl * var = kv.m_key;
        app * val = to_app(kv.m_value);
        SASSERT(m_fpa_util.is_float(var->get_range()));
        SASSERT(var->get_range()->get_num_parameters() == 2);
        unsigned ebits = m_fpa_util.get_ebits(var->get_range());
        unsigned sbits = m_fpa_util.get_sbits(var->get_range());

        app * a0 = to_app(val->get_arg(0));

        expr_ref v0(m), v1(m), v2(m);
#ifdef Z3DEBUG
        app * a1 = to_app(val->get_arg(1));
        app * a2 = to_app(val->get_arg(2));
        v0 = mc->get_const_interp(a0->get_decl());
        v1 = mc->get_const_interp(a1->get_decl());
        v2 = mc->get_const_interp(a2->get_decl());
#else
        expr * bv = mc->get_const_interp(to_app(to_app(a0)->get_arg(0))->get_decl());
        if (bv == nullptr) {
            v0 = m_bv_util.mk_numeral(0, 1);
            v1 = m_bv_util.mk_numeral(0, ebits);
            v2 = m_bv_util.mk_numeral(0, sbits-1);
        }
        else {
            unsigned bv_sz = m_bv_util.get_bv_size(bv);
            v0 = m_bv_util.mk_extract(bv_sz-1, bv_sz-1, bv);
            v1 = m_bv_util.mk_extract(bv_sz-2, sbits-1, bv);
            v2 = m_bv_util.mk_extract(sbits-2, 0, bv);
        }
#endif

        if (!v0) v0 = m_bv_util.mk_numeral(0, 1);
        if (!v1) v1 = m_bv_util.mk_numeral(0, ebits);
        if (!v2) v2 = m_bv_util.mk_numeral(0, sbits-1);

        expr_ref sgn(m), exp(m), sig(m);
        m_th_rw(v0, sgn);
        m_th_rw(v1, exp);
        m_th_rw(v2, sig);

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

        expr_ref cv = convert_bv2fp(var->get_range(), sgn, exp, sig);
        target_model->register_decl(var, cv);

        TRACE("bv2fpa", tout << var->get_name() << " == " << mk_ismt2_pp(cv, m) << std::endl;);
    }
}

void bv2fpa_converter::convert_rm_consts(model_core * mc, model_core * target_model, obj_hashtable<func_decl> & seen) {
    for (auto const& kv : m_rm_const2bv) {
        func_decl * var = kv.m_key;
        SASSERT(m_fpa_util.is_rm(var->get_range()));
        expr * val = kv.m_value;
        SASSERT(m_fpa_util.is_bv2rm(val));
        expr * bvval = to_app(val)->get_arg(0);
        expr_ref fv = convert_bv2rm(mc, to_app(bvval));
        TRACE("bv2fpa", tout << var->get_name() << " == " << mk_ismt2_pp(fv, m) << std::endl;);
        target_model->register_decl(var, fv);
        seen.insert(to_app(bvval)->get_decl());
    }
}

void bv2fpa_converter::convert_min_max_specials(model_core * mc, model_core * target_model, obj_hashtable<func_decl> & seen) {
    for (auto const& kv : m_min_max_specials) {
        func_decl * f = kv.m_key;
        app * pn_cnst = kv.m_value.first;
        app * np_cnst = kv.m_value.second;

        expr_ref pzero(m), nzero(m);
        pzero = m_fpa_util.mk_pzero(f->get_range());
        nzero = m_fpa_util.mk_nzero(f->get_range());

        expr_ref pn(m), np(m);
        if (!mc->eval(pn_cnst->get_decl(), pn)) pn = pzero;
        if (!mc->eval(np_cnst->get_decl(), np)) np = pzero;
        seen.insert(pn_cnst->get_decl());
        seen.insert(np_cnst->get_decl());

        rational pn_num, np_num;
        unsigned bv_sz;
        m_bv_util.is_numeral(pn, pn_num, bv_sz);
        m_bv_util.is_numeral(np, np_num, bv_sz);

        func_interp * flt_fi = alloc(func_interp, m, f->get_arity());
        expr * pn_args[2] = { pzero, nzero };
        if (pn != np) flt_fi->insert_new_entry(pn_args, (pn_num.is_one() ? nzero : pzero));
        flt_fi->set_else(np_num.is_one() ? nzero : pzero);

        target_model->register_decl(f, flt_fi);
        TRACE("bv2fpa", tout << "fp.min/fp.max special: " << std::endl <<
            mk_ismt2_pp(f, m) << " == " << mk_ismt2_pp(flt_fi->get_interp(), m) << std::endl;);
    }
}

void bv2fpa_converter::convert_uf2bvuf(model_core * mc, model_core * target_model, obj_hashtable<func_decl> & seen) {
    for (auto const& kv : m_uf2bvuf) {
        func_decl * f = kv.m_key;
        func_decl * f_uf = kv.m_value;
        seen.insert(f_uf);

        if (f->get_arity() == 0)
        {
            array_util au(m);
            if (au.is_array(f->get_range())) {
                array_model am = convert_array_func_interp(mc, f, f_uf);
                if (am.new_float_fd) target_model->register_decl(am.new_float_fd, am.new_float_fi);
                if (am.result) target_model->register_decl(f, am.result);
                if (am.bv_fd) seen.insert(am.bv_fd);
            }
            else {
                // Just keep.
                SASSERT(!m_fpa_util.is_float(f->get_range()) && !m_fpa_util.is_rm(f->get_range()));
                expr_ref val(m);
                if (mc->eval(f_uf, val))
                    target_model->register_decl(f, val);
            }
        }
        else if (f->get_family_id() == m_fpa_util.get_fid()) {
            // kv.m_value contains the model for the unspecified cases of kv.m_key in terms of bit-vectors.
            // convert_func_interp rebuilds a func_interp on floats.

            //  f is a floating point function: f(x,y) : Float
            //  f_uf is a bit-vector function: f_uf(xB,yB) : BitVec
            //  then there is f_def: f_Bv(xB, yB) := if(range(xB),.., f_uf(xB,yB))
            //  f(x,y) := to_float(if(range(to_bv(x)), ... f_uf(to_bv(xB), to_bv(yB)))) - not practical
            //         := if(range_fp(x), ...., to_float(f_uf(...))                     - approach (via fpa_util::is_considered_uninterpreted)

            func_interp *fi = convert_func_interp(mc, f, f_uf);
            if (fi->num_entries() > 0 || fi->get_else() != nullptr)
                target_model->register_decl(f, fi);
            else
                dealloc(fi);
        }
    }

    TRACE("bv2fpa", tout << "Target model: " << *target_model; );
}

void bv2fpa_converter::display(std::ostream & out) {
    for (auto const& kv : m_const2bv) {
        const symbol & n = kv.m_key->get_name();
        out << "\n  (" << n << " ";
        unsigned indent = n.display_size() + 4;
        out << mk_ismt2_pp(kv.m_value, m, indent) << ")";
    }
    for (auto const& kv : m_rm_const2bv) {
        const symbol & n = kv.m_key->get_name();
        out << "\n  (" << n << " ";
        unsigned indent = n.display_size() + 4;
        out << mk_ismt2_pp(kv.m_value, m, indent) << ")";
    }
    for (auto const& kv : m_uf2bvuf) {
        const symbol & n = kv.m_key->get_name();
        out << "\n  (" << n << " ";
        unsigned indent = n.display_size() + 4;
        out << mk_ismt2_pp(kv.m_value, m, indent) << ")";
    }
    for (auto const& kv : m_min_max_specials) {
        const symbol & n = kv.m_key->get_name();
        out << "\n  (" << n << " ";
        unsigned indent = n.display_size() + 4;
        out << mk_ismt2_pp(kv.m_value.first, m, indent) << "; " <<
            mk_ismt2_pp(kv.m_value.second, m, indent) << ")";
    }
}

bv2fpa_converter * bv2fpa_converter::translate(ast_translation & translator) {
    bv2fpa_converter * res = alloc(bv2fpa_converter, translator.to());
    for (auto const& kv : m_const2bv) {
        func_decl * k = translator(kv.m_key);
        expr * v = translator(kv.m_value);
        res->m_const2bv.insert(k, v);
        translator.to().inc_ref(k);
        translator.to().inc_ref(v);
    }
    for (auto const& kv : m_rm_const2bv) {
        func_decl * k = translator(kv.m_key);
        expr * v = translator(kv.m_value);
        res->m_rm_const2bv.insert(k, v);
        translator.to().inc_ref(k);
        translator.to().inc_ref(v);
    }
    for (auto const& kv : m_uf2bvuf) {
        func_decl * k = translator(kv.m_key);
        func_decl * v = translator(kv.m_value);
        res->m_uf2bvuf.insert(k, v);
        translator.to().inc_ref(k);
        translator.to().inc_ref(v);
    }
    for (auto const& kv : m_min_max_specials) {
        func_decl * k = translator(kv.m_key);
        app * v1 = translator(kv.m_value.first);
        app * v2 = translator(kv.m_value.second);
        res->m_min_max_specials.insert(k, std::pair<app*, app*>(v1, v2));
        translator.to().inc_ref(k);
        translator.to().inc_ref(v1);
        translator.to().inc_ref(v2);
    }
    return res;
}
