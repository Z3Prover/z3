/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    theory_fpa.cpp

Abstract:

    Floating-Point Theory Plugin

Author:

    Christoph (cwinter) 2014-04-23

Revision History:

--*/
#include"ast_smt2_pp.h"
#include"smt_context.h"
#include"theory_fpa.h"
#include"theory_bv.h"
#include"smt_model_generator.h"

namespace smt {

    class fpa2bv_conversion_trail_elem : public trail<theory_fpa> {
        ast_manager & m;
        obj_map<expr, expr*> & m_conversions;
        expr * m_e;
    public:
        fpa2bv_conversion_trail_elem(ast_manager & m, obj_map<expr, expr*> & c, expr * e) : 
            m(m), m_conversions(c), m_e(e) {}
        virtual ~fpa2bv_conversion_trail_elem() {}
        virtual void undo(theory_fpa & th) {
            expr * v = m_conversions.find(m_e);
            m_conversions.remove(m_e);
            m.dec_ref(v);
        }
    };

    void theory_fpa::fpa2bv_converter_wrapped::mk_const(func_decl * f, expr_ref & result) {
        SASSERT(f->get_family_id() == null_family_id);
        SASSERT(f->get_arity() == 0);
        expr * r;
        if (m_const2bv.find(f, r)) {
            result = r;
        }
        else {
            sort * s = f->get_range();
            expr_ref bv(m);
            bv = m_th.wrap(m.mk_const(f));
            unsigned bv_sz = m_th.m_bv_util.get_bv_size(bv);
            unsigned ebits = m_th.m_fpa_util.get_ebits(s);
            unsigned sbits = m_th.m_fpa_util.get_sbits(s);
            SASSERT(bv_sz == ebits + sbits);
            m_th.m_converter.mk_fp(m_bv_util.mk_extract(bv_sz - 1, bv_sz - 1, bv),
                                   m_bv_util.mk_extract(bv_sz - 2, sbits - 1, bv),
                                   m_bv_util.mk_extract(sbits - 2, 0, bv),                                       
                                   result);
            SASSERT(m_th.m_fpa_util.is_float(result));
            m_const2bv.insert(f, result);
            m.inc_ref(f);
            m.inc_ref(result);
        }
    }        

    void theory_fpa::fpa2bv_converter_wrapped::mk_rm_const(func_decl * f, expr_ref & result) {
        SASSERT(f->get_family_id() == null_family_id);
        SASSERT(f->get_arity() == 0);
        expr * r;
        if (m_rm_const2bv.find(f, r)) {
            result = r;
        }
        else {
            SASSERT(is_rm(f->get_range()));
            result = m_th.wrap(m.mk_const(f));
            m_rm_const2bv.insert(f, result);
            m.inc_ref(f);
            m.inc_ref(result);
        }
    }

    theory_fpa::theory_fpa(ast_manager & m) :
        theory(m.mk_family_id("fpa")),
        m_converter(m, this),
        m_rw(m, m_converter, params_ref()),
        m_th_rw(m),
        m_trail_stack(*this),
        m_fpa_util(m_converter.fu()),
        m_bv_util(m_converter.bu()),
        m_arith_util(m_converter.au())
    {
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_th_rw.updt_params(p);
    }

    theory_fpa::~theory_fpa()
    {
        ast_manager & m = get_manager();
        dec_ref_map_values(m, m_conversions);
        dec_ref_map_values(m, m_wraps);
        dec_ref_map_values(m, m_unwraps);          
    }

    app * theory_fpa::fpa_value_proc::mk_value(model_generator & mg, ptr_vector<expr> & values) {
        ast_manager & m = m_th.get_manager();        

        TRACE("t_fpa_detail", for (unsigned i = 0; i < values.size(); i++)
                                  tout << "value[" << i << "] = " << mk_ismt2_pp(values[i], m) << std::endl;);
        
        mpf_manager & mpfm = m_fu.fm();
        unsynch_mpz_manager & mpzm = mpfm.mpz_manager();
        app * result;

        scoped_mpz bias(mpzm);
        mpzm.power(mpz(2), m_ebits - 1, bias);
        mpzm.dec(bias);

        scoped_mpz sgn_z(mpzm), sig_z(mpzm), exp_z(mpzm);
        unsigned bv_sz;

        if (values.size() == 1) {
            SASSERT(m_bu.is_bv(values[0]));
            SASSERT(m_bu.get_bv_size(values[0]) == (m_ebits + m_sbits));

            rational all_r(0);
            scoped_mpz all_z(mpzm);

            bool r = m_bu.is_numeral(values[0], all_r, bv_sz);
            SASSERT(r);
            SASSERT(bv_sz == (m_ebits + m_sbits));
            SASSERT(all_r.is_int());
            mpzm.set(all_z, all_r.to_mpq().numerator());

            mpzm.machine_div2k(all_z, m_ebits + m_sbits - 1, sgn_z);
            mpzm.mod(all_z, mpfm.m_powers2(m_ebits + m_sbits - 1), all_z);

            mpzm.machine_div2k(all_z, m_sbits - 1, exp_z);
            mpzm.mod(all_z, mpfm.m_powers2(m_sbits - 1), all_z);

            mpzm.set(sig_z, all_z);
        }
        else if (values.size() == 3) {            
            rational sgn_r(0), exp_r(0), sig_r(0);

            bool r = m_bu.is_numeral(values[0], sgn_r, bv_sz);
            SASSERT(r && bv_sz == 1);
            r = m_bu.is_numeral(values[1], exp_r, bv_sz);
            SASSERT(r && bv_sz == m_ebits);
            r = m_bu.is_numeral(values[2], sig_r, bv_sz);
            SASSERT(r && bv_sz == m_sbits - 1);
            
            SASSERT(mpzm.is_one(sgn_r.to_mpq().denominator()));
            SASSERT(mpzm.is_one(exp_r.to_mpq().denominator()));
            SASSERT(mpzm.is_one(sig_r.to_mpq().denominator()));

            mpzm.set(sgn_z, sgn_r.to_mpq().numerator());
            mpzm.set(exp_z, exp_r.to_mpq().numerator());
            mpzm.set(sig_z, sig_r.to_mpq().numerator());
        }
        else
            UNREACHABLE();

        scoped_mpz exp_u = exp_z - bias;
        SASSERT(mpzm.is_int64(exp_u));

        scoped_mpf f(mpfm);
        mpfm.set(f, m_ebits, m_sbits, mpzm.is_one(sgn_z), sig_z, mpzm.get_int64(exp_u));
        result = m_fu.mk_value(f);

        TRACE("t_fpa", tout << "fpa_value_proc::mk_value [" <<
                       mpzm.to_string(sgn_z) << "," <<
                       mpzm.to_string(exp_z) << "," <<
                       mpzm.to_string(sig_z) << "] --> " <<
                       mk_ismt2_pp(result, m_th.get_manager()) << "\n";);
        
        return result;
    }

    app * theory_fpa::fpa_rm_value_proc::mk_value(model_generator & mg, ptr_vector<expr> & values) {
        SASSERT(values.size() == 1);
        ast_manager & m = m_th.get_manager();
        
        TRACE("t_fpa_detail", for (unsigned i = 0; i < values.size(); i++)
              tout << "value[" << i << "] = " << mk_ismt2_pp(values[i], m) << std::endl;);

        app * result = 0;        
        unsigned bv_sz;

        rational val(0);
        bool r = m_bu.is_numeral(values[0], val, bv_sz);
        SASSERT(r);
        SASSERT(bv_sz == 3);
            
        switch (val.get_uint64())
        {
        case BV_RM_TIES_TO_AWAY: result = m_fu.mk_round_nearest_ties_to_away(); break;
        case BV_RM_TIES_TO_EVEN: result = m_fu.mk_round_nearest_ties_to_even(); break;
        case BV_RM_TO_NEGATIVE: result = m_fu.mk_round_toward_negative(); break;
        case BV_RM_TO_POSITIVE: result = m_fu.mk_round_toward_positive(); break;
        case BV_RM_TO_ZERO:
        default: result = m_fu.mk_round_toward_zero();
        }

        TRACE("t_fpa", tout << "fpa_rm_value_proc::mk_value result: " << 
                               mk_ismt2_pp(result, m_th.get_manager()) << "\n";);

        return result;
    }

    app_ref theory_fpa::wrap(expr * e) {
        SASSERT(!m_fpa_util.is_wrap(e));
        ast_manager & m = get_manager();
        sort * e_srt = m.get_sort(e);

        func_decl *w;

        if (!m_wraps.find(e_srt, w)) {
            SASSERT(!m_wraps.contains(e_srt));
            
            sort * bv_srt;
            if (m_converter.is_rm(e_srt))
                bv_srt = m_bv_util.mk_sort(3);
            else {
                SASSERT(m_converter.is_float(e_srt));
                unsigned ebits = m_fpa_util.get_ebits(e_srt);
                unsigned sbits = m_fpa_util.get_sbits(e_srt);
                bv_srt = m_bv_util.mk_sort(ebits + sbits);                
            }
                       
            w = m.mk_func_decl(get_family_id(), OP_FPA_INTERNAL_BVWRAP, 0, 0, 1, &e_srt, bv_srt);
            m_wraps.insert(e_srt, w);
            m.inc_ref(w);
        }

        app_ref res(m);
        res = m.mk_app(w, e);
        return res;
    }

    app_ref theory_fpa::unwrap(expr * e, sort * s) {
        SASSERT(!m_fpa_util.is_unwrap(e));
        ast_manager & m = get_manager();        
        sort * bv_srt = m.get_sort(e);

        func_decl *u;

        if (!m_unwraps.find(bv_srt, u)) {
            SASSERT(!m_unwraps.contains(bv_srt));
            u = m.mk_func_decl(get_family_id(), OP_FPA_INTERNAL_BVUNWRAP, 0, 0, 1, &bv_srt, s);
            m_unwraps.insert(bv_srt, u);
            m.inc_ref(u);
        }

        app_ref res(m);
        res = m.mk_app(u, e);
        return res;
    }
    
    expr_ref theory_fpa::convert_atom(expr * e) {
        ast_manager & m = get_manager();
        expr_ref res(m);
        proof_ref pr(m);
        m_rw(e, res);
        m_th_rw(res, res);
        SASSERT(is_app(res));
        SASSERT(m.is_bool(res));        
        return res;
    }

    expr_ref theory_fpa::convert_term(expr * e) {
        ast_manager & m = get_manager();        
        
        expr_ref e_conv(m), res(m);
        proof_ref pr(m);
        m_rw(e, e_conv);

        if (m_fpa_util.is_rm(e)) {
            SASSERT(is_sort_of(m.get_sort(e_conv), m_bv_util.get_family_id(), BV_SORT));
            SASSERT(m_bv_util.get_bv_size(e_conv) == 3);
            m_th_rw(e_conv, res);
        }
        else if (m_fpa_util.is_float(e)) {
            expr_ref sgn(m), sig(m), exp(m);
            m_converter.split_fp(e_conv, sgn, exp, sig);
            m_th_rw(sgn);
            m_th_rw(exp);
            m_th_rw(sig);            
            m_converter.mk_fp(sgn, exp, sig, res);
        }
        else
            UNREACHABLE();

        SASSERT(res.get() != 0);
        return res;
    }

    expr_ref theory_fpa::convert_conversion_term(expr * e) {
        /* This is for the conversion functions fp.to_* */
        ast_manager & m = get_manager();        
        expr_ref res(m);
        proof_ref pr(m);

        SASSERT(m_arith_util.is_real(e) || m_bv_util.is_bv(e));

        m_rw(e, res);
        m_th_rw(res, res);
        return res;
    }

    expr_ref theory_fpa::convert_unwrap(expr * e) {
        SASSERT(m_fpa_util.is_unwrap(e));
        ast_manager & m = get_manager();
        sort * srt = m.get_sort(e);
        expr_ref res(m);
        if (m_fpa_util.is_rm(srt)) {
            res = to_app(e)->get_arg(0);
        }
        else {
            SASSERT(m_fpa_util.is_float(srt));
            unsigned sbits = m_fpa_util.get_sbits(srt);
            expr_ref bv(m);
            bv = to_app(e)->get_arg(0);
            unsigned bv_sz = m_bv_util.get_bv_size(bv);
            m_converter.mk_fp(m_bv_util.mk_extract(bv_sz - 1, bv_sz - 1, bv),
                              m_bv_util.mk_extract(bv_sz - 2, sbits - 1, bv),
                              m_bv_util.mk_extract(sbits - 2, 0, bv),
                              res);
        }
        return res;
    }

    expr_ref theory_fpa::convert(expr * e)
    {
        ast_manager & m = get_manager();
        expr_ref res(m);

        if (m_conversions.contains(e)) {
            res = m_conversions.find(e);
            TRACE("t_fpa_detail", tout << "cached:" << std::endl;
                                  tout << mk_ismt2_pp(e, m) << std::endl << " -> " << std::endl <<
                                          mk_ismt2_pp(res, m) << std::endl;);
            return res;
        }
        else {
            if (m_fpa_util.is_unwrap(e))
                res = convert_unwrap(e);
            else if (m.is_bool(e))
                res = convert_atom(e);
            else if (m_fpa_util.is_float(e) || m_fpa_util.is_rm(e))
                res = convert_term(e);
            else if (m_arith_util.is_real(e) || m_bv_util.is_bv(e))
                res = convert_conversion_term(e);
            else
                UNREACHABLE();

            TRACE("t_fpa_detail", tout << "converted; caching:" << std::endl;
                                  tout << mk_ismt2_pp(e, m) << std::endl << " -> " << std::endl <<
                                          mk_ismt2_pp(res, m) << std::endl;);

            m_conversions.insert(e, res);
            m.inc_ref(res);
            m_trail_stack.push(fpa2bv_conversion_trail_elem(m, m_conversions, e));
        }

        return res;
    }

    expr_ref theory_fpa::mk_side_conditions()
    {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        simplifier & simp = ctx.get_simplifier();
        
        expr_ref res(m), t(m);
        proof_ref t_pr(m);
        res = m.mk_true();

        expr_ref_vector::iterator it = m_converter.m_extra_assertions.begin();
        expr_ref_vector::iterator end = m_converter.m_extra_assertions.end();
        for (; it != end; it++) {
            simp(*it, t, t_pr);
            res = m.mk_and(res, t);
        }
        m_converter.m_extra_assertions.reset();

        m_th_rw(res);
        
        CTRACE("t_fpa", !m.is_true(res), tout << "side condition: " << mk_ismt2_pp(res, m) << "\n";);
        return res;
    }

    void theory_fpa::assert_cnstr(expr * e) {
        if (get_manager().is_true(e)) return;
        TRACE("t_fpa_detail", tout << "asserting " << mk_ismt2_pp(e, get_manager()) << "\n";);        
        context & ctx = get_context();
        ctx.internalize(e, false);
        literal lit(ctx.get_literal(e));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);        
        TRACE("t_fpa_detail", tout << "done asserting " << mk_ismt2_pp(e, get_manager()) << "\n";);
    }    

    void theory_fpa::attach_new_th_var(enode * n) {
        context & ctx = get_context();
        theory_var v = mk_var(n);
        ctx.attach_th_var(n, this, v);
        TRACE("t_fpa_detail", tout << "new theory var: " << mk_ismt2_pp(n->get_owner(), get_manager()) << " := " << v << "\n";);
    }

    bool theory_fpa::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("t_fpa", tout << "internalizing atom: " << mk_ismt2_pp(atom, get_manager()) << "\n";);
        SASSERT(atom->get_family_id() == get_family_id());

        ast_manager & m = get_manager();
        context & ctx = get_context();

        if (ctx.b_internalized(atom))
            return true;

        unsigned num_args = atom->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(atom->get_arg(i), false);

        literal l(ctx.mk_bool_var(atom));
        ctx.set_var_theory(l.var(), get_id());

        expr_ref bv_atom(m);
        bv_atom = convert_atom(atom);        
        SASSERT(is_app(bv_atom) && m.is_bool(bv_atom));
        bv_atom = m.mk_and(bv_atom, mk_side_conditions());
        
        assert_cnstr(m.mk_iff(atom, bv_atom));
        return true;
    }

    bool theory_fpa::internalize_term(app * term) {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        TRACE("t_fpa", tout << "internalizing term: " << mk_ismt2_pp(term, get_manager()) << "\n";);
        SASSERT(term->get_family_id() == get_family_id());
        SASSERT(!ctx.e_internalized(term));        

        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(term->get_arg(i), false);
        
        enode * e = (ctx.e_internalized(term)) ? ctx.get_enode(term) :
                                                 ctx.mk_enode(term, false, false, true);
        
        if (is_attached_to_var(e))
            return false;

        attach_new_th_var(e);

        // The conversion operators fp.to_* appear in non-FP constraints.
        // The corresponding constraints will not be translated and added 
        // via convert(...) and assert_cnstr(...) in initialize_atom(...).
        // Therefore, we translate and assert them here.
        fpa_op_kind k = (fpa_op_kind)term->get_decl_kind();
        switch (k) {
        case OP_FPA_TO_UBV:
        case OP_FPA_TO_SBV:
        case OP_FPA_TO_REAL: 
        case OP_FPA_TO_IEEE_BV: {
            expr_ref conv(m);
            conv = convert(term);
            assert_cnstr(m.mk_eq(term, conv));
            assert_cnstr(mk_side_conditions());
            break;
        }
        default: /* ignore */;            
        }

        return true;
    }    

    void theory_fpa::apply_sort_cnstr(enode * n, sort * s) {
        TRACE("t_fpa", tout << "apply sort cnstr for: " << mk_ismt2_pp(n->get_owner(), get_manager()) << "\n";);
        SASSERT(n->get_owner()->get_family_id() == get_family_id() ||
                n->get_owner()->get_family_id() == null_theory_id);
        SASSERT(s->get_family_id() == get_family_id());

        if (!is_attached_to_var(n)) {
            attach_new_th_var(n);

            ast_manager & m = get_manager();
            context & ctx = get_context();

            app_ref owner(m);
            sort_ref owner_sort(m);
            owner = n->get_owner();
            owner_sort = m.get_sort(owner);

            if (m_fpa_util.is_rm(owner_sort)) {
                // For every RM term, we need to make sure that it's
                // associated bit-vector is within the valid range.            
                if (!m_fpa_util.is_unwrap(owner)) {
                    expr_ref valid(m), limit(m);
                    limit = m_bv_util.mk_numeral(4, 3);
                    valid = m_bv_util.mk_ule(wrap(owner), limit);
                    assert_cnstr(valid);
                }
            }

            if (!ctx.relevancy() && !m_fpa_util.is_unwrap(owner))
                assert_cnstr(m.mk_eq(unwrap(wrap(owner), owner_sort), owner));
        }
    }

    void theory_fpa::new_eq_eh(theory_var x, theory_var y) {        
        ast_manager & m = get_manager();

        TRACE("t_fpa", tout << "new eq: " << x << " = " << y << std::endl;);
        TRACE("t_fpa_detail", tout << mk_ismt2_pp(get_enode(x)->get_owner(), m) << " = " <<
                                      mk_ismt2_pp(get_enode(y)->get_owner(), m) << std::endl;);
        
        fpa_util & fu = m_fpa_util;

        expr_ref xe(m), ye(m);
        xe = get_enode(x)->get_owner();
        ye = get_enode(y)->get_owner();

        if ((m.is_bool(xe) && m.is_bool(ye)) || 
            (m_bv_util.is_bv(xe) && m_bv_util.is_bv(ye))) {
            SASSERT(to_app(xe)->get_decl()->get_family_id() == get_family_id());
            return;
        }
        
        expr_ref xc(m), yc(m);
        xc = convert(xe);
        yc = convert(ye);

        TRACE("t_fpa_detail", tout << "xc=" << mk_ismt2_pp(xc, m) << std::endl;
                              tout << "yc=" << mk_ismt2_pp(yc, m) << std::endl;);

        expr_ref c(m);

        if (fu.is_float(xe) && fu.is_float(ye))
        {
            expr *x_sgn, *x_sig, *x_exp;
            m_converter.split_fp(xc, x_sgn, x_exp, x_sig);
            expr *y_sgn, *y_sig, *y_exp;
            m_converter.split_fp(yc, y_sgn, y_exp, y_sig);

            c = m.mk_eq(m_bv_util.mk_concat(m_bv_util.mk_concat(x_sgn, x_exp), x_sig),
                        m_bv_util.mk_concat(m_bv_util.mk_concat(y_sgn, y_exp), y_sig));            
        }
        else
            c = m.mk_eq(xc, yc);
        
        m_th_rw(c);        
        assert_cnstr(m.mk_iff(m.mk_eq(xe, ye), c));
        assert_cnstr(mk_side_conditions());

        return;
    }

    void theory_fpa::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager & m = get_manager();

        TRACE("t_fpa", tout << "new diseq: " << x << " != " << y << std::endl;);
        TRACE("t_fpa_detail", tout << mk_ismt2_pp(get_enode(x)->get_owner(), m) << " != " <<
                                      mk_ismt2_pp(get_enode(y)->get_owner(), m) << std::endl;);

        expr_ref xe(m), ye(m);
        xe = get_enode(x)->get_owner();
        ye = get_enode(y)->get_owner();

        if ((m.is_bool(xe) && m.is_bool(ye)) ||
            (m_bv_util.is_bv(xe) && m_bv_util.is_bv(ye))) {
            SASSERT(to_app(xe)->get_decl()->get_family_id() == get_family_id());
            return;
        }

        fpa_util & fu = m_fpa_util;

        expr_ref xc(m), yc(m);
        xc = convert(xe);
        yc = convert(ye);

        expr_ref c(m);

        if (fu.is_float(xe) && fu.is_float(ye))
        {
            expr *x_sgn, *x_sig, *x_exp;
            m_converter.split_fp(xc, x_sgn, x_exp, x_sig);
            expr *y_sgn, *y_sig, *y_exp;
            m_converter.split_fp(yc, y_sgn, y_exp, y_sig);

            c = m.mk_not(m.mk_eq(m_bv_util.mk_concat(m_bv_util.mk_concat(x_sgn, x_exp), x_sig),
                                 m_bv_util.mk_concat(m_bv_util.mk_concat(y_sgn, y_exp), y_sig)));            
        }
        else
            c = m.mk_not(m.mk_eq(xc, yc));

        m_th_rw(c);
        assert_cnstr(m.mk_iff(m.mk_not(m.mk_eq(xe, ye)), c));
        assert_cnstr(mk_side_conditions());

        return;
    }

    void theory_fpa::push_scope_eh() {
        theory::push_scope_eh();
        m_trail_stack.push_scope();
    }

    void theory_fpa::pop_scope_eh(unsigned num_scopes) {                
        m_trail_stack.pop_scope(num_scopes);
        TRACE("t_fpa", tout << "pop " << num_scopes << "; now " << m_trail_stack.get_num_scopes() << "\n";);
        // unsigned num_old_vars = get_old_num_vars(num_scopes);        
        theory::pop_scope_eh(num_scopes);
    }    

    void theory_fpa::assign_eh(bool_var v, bool is_true) {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        expr * e = ctx.bool_var2expr(v);
        
        TRACE("t_fpa", tout << "assign_eh for: " << v << " (" << is_true << "):\n" << mk_ismt2_pp(e, m) << "\n";);
        
        expr_ref converted(m);
        converted = m.mk_and(convert(e), mk_side_conditions());
        if (is_true)
            assert_cnstr(m.mk_implies(e, converted));
        else 
            assert_cnstr(m.mk_implies(m.mk_not(e), m.mk_not(converted)));        
    }

    void theory_fpa::relevant_eh(app * n) {
        ast_manager & m = get_manager();
        TRACE("t_fpa", tout << "relevant_eh for: " << mk_ismt2_pp(n, m) << "\n";);

        mpf_manager & mpfm = m_fpa_util.fm();        

        if (m_fpa_util.is_float(n) || m_fpa_util.is_rm(n)) {
            if (!m_fpa_util.is_unwrap(n)) {
                expr_ref wrapped(m), c(m);
                wrapped = wrap(n);
                mpf_rounding_mode rm;
                scoped_mpf val(mpfm);
                if (m_fpa_util.is_rm_numeral(n, rm)) {
                    c = m.mk_eq(wrapped, m_bv_util.mk_numeral(rm, 3));                    
                    assert_cnstr(c);
                }
                else if (m_fpa_util.is_numeral(n, val)) {
                    expr_ref bv_val_e(m);
                    bv_val_e = convert(n);
                    SASSERT(is_app(bv_val_e));
                    SASSERT(to_app(bv_val_e)->get_num_args() == 3);
                    app_ref bv_val_a(to_app(bv_val_e.get()), m);
                    expr * args[] = { bv_val_a->get_arg(0), bv_val_a->get_arg(1), bv_val_a->get_arg(2) };
                    c = m.mk_eq(wrapped, m_bv_util.mk_concat(3, args));
                    c = m.mk_and(c, mk_side_conditions());
                    assert_cnstr(c);
                }
                else {
                    c = m.mk_eq(unwrap(wrapped, m.get_sort(n)), n);                    
                    assert_cnstr(c);
                }
            }
        }
        else if (n->get_family_id() == get_family_id()) {
            // These are the conversion functions fp.to_* */
            SASSERT(!m_fpa_util.is_float(n) && !m_fpa_util.is_rm(n));
        }
        else
            UNREACHABLE();
    }

    void theory_fpa::reset_eh() {
        TRACE("t_fpa", tout << "reset_eh\n";);
        pop_scope_eh(m_trail_stack.get_num_scopes());
        m_converter.reset();
        m_rw.reset();
        m_th_rw.reset();
        m_trail_stack.pop_scope(m_trail_stack.get_num_scopes());
        if (m_factory) dealloc(m_factory); m_factory = 0;
        ast_manager & m = get_manager();
        dec_ref_map_values(m, m_conversions);
        dec_ref_map_values(m, m_wraps);
        dec_ref_map_values(m, m_unwraps);
        theory::reset_eh();
    }

    final_check_status theory_fpa::final_check_eh() {
        TRACE("t_fpa", tout << "final_check_eh\n";);
        SASSERT(m_converter.m_extra_assertions.empty());
        return FC_DONE; 
    }

    void theory_fpa::init_model(model_generator & mg) {
        TRACE("t_fpa", tout << "initializing model" << std::endl; display(tout););
        m_factory = alloc(fpa_value_factory, get_manager(), get_family_id());
        mg.register_factory(m_factory);
    }

    model_value_proc * theory_fpa::mk_value(enode * n, model_generator & mg) {
        TRACE("t_fpa", tout << "mk_value for: " << mk_ismt2_pp(n->get_owner(), get_manager()) << 
                            " (sort " << mk_ismt2_pp(get_manager().get_sort(n->get_owner()), get_manager()) << ")\n";);

        ast_manager & m = get_manager();
        context & ctx = get_context();
        app_ref owner(m);
        owner = n->get_owner();

        // If the owner is not internalized, it doesn't have an enode associated.        
        SASSERT(ctx.e_internalized(owner));
        
        if (m_fpa_util.is_rm_numeral(owner) ||
            m_fpa_util.is_numeral(owner)) {
            return alloc(expr_wrapper_proc, owner);
        }
        
        model_value_proc * res = 0;

        app_ref wrapped(m);
        wrapped = wrap(owner);
        SASSERT(m_bv_util.is_bv(wrapped));

        CTRACE("t_fpa_detail", !ctx.e_internalized(wrapped),
                tout << "Model dependency not internalized: " <<
                mk_ismt2_pp(wrapped, m) <<
                " (owner " << (!ctx.e_internalized(owner) ? "not" : "is") <<
                " internalized)" << std::endl;);

        if (is_app_of(owner, get_family_id(), OP_FPA_FP)) {
            SASSERT(to_app(owner)->get_num_args() == 3);
            app_ref a0(m), a1(m), a2(m);
            a0 = to_app(owner->get_arg(0));
            a1 = to_app(owner->get_arg(1));
            a2 = to_app(owner->get_arg(2));
            unsigned ebits = m_fpa_util.get_ebits(m.get_sort(owner));
            unsigned sbits = m_fpa_util.get_sbits(m.get_sort(owner));
            fpa_value_proc * vp = alloc(fpa_value_proc, this, ebits, sbits);            
            vp->add_dependency(ctx.get_enode(a0));
            vp->add_dependency(ctx.get_enode(a1));
            vp->add_dependency(ctx.get_enode(a2));
            TRACE("t_fpa_detail", tout << "Depends on: " <<
                  mk_ismt2_pp(a0, m) << " eq. cls. #" << get_enode(a0)->get_root()->get_owner()->get_id() << std::endl <<
                  mk_ismt2_pp(a1, m) << " eq. cls. #" << get_enode(a1)->get_root()->get_owner()->get_id() << std::endl <<
                  mk_ismt2_pp(a2, m) << " eq. cls. #" << get_enode(a2)->get_root()->get_owner()->get_id() << std::endl;);
            res = vp;
        }
        else if (ctx.e_internalized(wrapped)) {
            if (m_fpa_util.is_rm(owner)) {
                fpa_rm_value_proc * vp = alloc(fpa_rm_value_proc, this);
                vp->add_dependency(ctx.get_enode(wrapped));
                res = vp;
            }
            else if (m_fpa_util.is_float(owner)) {
                unsigned ebits = m_fpa_util.get_ebits(m.get_sort(owner));
                unsigned sbits = m_fpa_util.get_sbits(m.get_sort(owner));
                fpa_value_proc * vp = alloc(fpa_value_proc, this, ebits, sbits);
                enode * en = ctx.get_enode(wrapped);
                vp->add_dependency(en);
                TRACE("t_fpa_detail", tout << "Depends on: " << mk_ismt2_pp(wrapped, m) << " eq. cls. #" << en->get_root()->get_owner()->get_id() << std::endl;);
                res = vp;
            }
        }
        else {
            unsigned ebits = m_fpa_util.get_ebits(m.get_sort(owner));
            unsigned sbits = m_fpa_util.get_sbits(m.get_sort(owner));
            return alloc(expr_wrapper_proc, m_fpa_util.mk_pzero(ebits, sbits));
        }

        SASSERT(res != 0);
        return res;
    }

    void theory_fpa::finalize_model(model_generator & mg) {}

    void theory_fpa::display(std::ostream & out) const
    {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        
        out << "fpa theory variables:" << std::endl;        
        ptr_vector<enode>::const_iterator it = ctx.begin_enodes();
        ptr_vector<enode>::const_iterator end = ctx.end_enodes();
        for (; it != end; it++) {
            theory_var v = (*it)->get_th_var(get_family_id());
            if (v != -1) out << v << " -> " <<
                mk_ismt2_pp((*it)->get_owner(), m) << std::endl;
        }

        out << "bv theory variables:" << std::endl;
        it = ctx.begin_enodes();
        end = ctx.end_enodes();
        for (; it != end; it++) {
            theory_var v = (*it)->get_th_var(m_bv_util.get_family_id());
            if (v != -1) out << v << " -> " <<
                mk_ismt2_pp((*it)->get_owner(), m) << std::endl;            
        }

        out << "arith theory variables:" << std::endl;
        it = ctx.begin_enodes();
        end = ctx.end_enodes();
        for (; it != end; it++) {
            theory_var v = (*it)->get_th_var(m_arith_util.get_family_id());
            if (v != -1) out << v << " -> " <<
                mk_ismt2_pp((*it)->get_owner(), m) << std::endl;
        }

        out << "equivalence classes:\n";
        it = ctx.begin_enodes();
        end = ctx.end_enodes();
        for (; it != end; ++it) {
            expr * n = (*it)->get_owner();
            expr * r = (*it)->get_root()->get_owner();
            out << r->get_id() << " --> " << mk_ismt2_pp(n, m) << std::endl;
        }
    }
};
