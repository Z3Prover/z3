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

    class fpa_atom_trail : public trail<theory_fpa> {
        bool_var m_var;
    public:
        fpa_atom_trail(bool_var v) : m_var(v) {}
        virtual ~fpa_atom_trail() {}
        virtual void undo(theory_fpa & th) {
            theory_fpa::atom * a = th.get_bv2a(m_var);
            a->~atom();
            th.erase_bv2a(m_var);
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
            func_decl *w, *u;
            m_th.get_wrap(s, w, u);
            expr_ref bv(m);
            bv = m.mk_app(w, m.mk_const(f));
            unsigned bv_sz = m_th.m_converter.bu().get_bv_size(bv);
            unsigned ebits = m_th.m_converter.fu().get_ebits(f->get_range());
            unsigned sbits = m_th.m_converter.fu().get_sbits(f->get_range());
            SASSERT(bv_sz == ebits + sbits);
            m_th.m_converter.mk_triple(m_bv_util.mk_extract(bv_sz - 1, bv_sz - 1, bv),
                                       m_bv_util.mk_extract(sbits - 2, 0, bv),
                                       m_bv_util.mk_extract(bv_sz - 2, sbits - 1, bv),
                                       result);

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

            sort * s = f->get_range();
            func_decl *w, *u;
            m_th.get_wrap(s, w, u);
            result = m.mk_app(w, m.mk_const(f));
            
            m_rm_const2bv.insert(f, result);
            m.inc_ref(f);
            m.inc_ref(result);
        }
    }

    theory_fpa::theory_fpa(ast_manager & m) :
        theory(m.mk_family_id("float")),
        m_converter(m, this),        
        m_rw(m, m_converter, params_ref()),
        m_th_rw(m),
        m_trail_stack(*this)
    {
    }

    theory_fpa::~theory_fpa()
    {
    }

    app * theory_fpa::fpa_value_proc::mk_value(model_generator & mg, ptr_vector<expr> & values) {
        TRACE("t_fpa", tout << "fpa_value_proc::mk_value for: " << mk_ismt2_pp(m_a, m_th.get_manager()) << "\n";);
        ast_manager & m = m_th.get_manager();
        context & ctx = m_th.get_context();        
        theory_id bv_id = m.mk_family_id("bv");
        theory_bv * th_bv = dynamic_cast<theory_bv *>(ctx.get_theory(bv_id));
        SASSERT(th_bv != 0);        
        
        float_util & fu = m_th.m_converter.fu();
        bv_util & bu = m_th.m_converter.bu();
        mpf_manager & mpfm = fu.fm();
        unsynch_mpq_manager & mpqm = mpfm.mpq_manager();
        unsynch_mpz_manager & mpzm = mpfm.mpz_manager();
        
        sort * s = m.get_sort(m_a);
        unsigned ebits = fu.get_ebits(s);
        unsigned sbits = fu.get_sbits(s);

        scoped_mpz bias(mpzm);
        mpzm.power(mpz(2), ebits - 1, bias);
        mpzm.dec(bias);

        app * result;
        float_op_kind k = (float_op_kind) to_app(m_a)->get_decl_kind();
        switch (k)
        {        
        case -1: {
            func_decl *w, *u;
            m_th.get_wrap(s, w, u);
            rational bv_val(0);
            scoped_mpz sgn(mpzm), sig(mpzm), exp(bias);
            app_ref bv_w(m);
            bv_w = m.mk_app(w, m_a);

            if (!th_bv->get_fixed_value(bv_w, bv_val))
                result = fu.mk_nan(ebits, sbits);
            else {
                scoped_mpz all_bits(mpzm);
                all_bits = bv_val.to_mpq().numerator();
                SASSERT(mpzm.is_one(bv_val.to_mpq().denominator()));
                
                mpzm.machine_div2k(all_bits, ebits + sbits - 1, sgn);

                scoped_mpz tmp_p(mpzm);
                mpzm.power(mpz(2), ebits + sbits - 1, tmp_p);

                if (mpzm.is_one(sgn)) mpzm.sub(all_bits, tmp_p, all_bits);

                mpzm.machine_div2k(all_bits, sbits - 1, exp);
                scoped_mpz exp_u(mpzm);
                mpzm.sub(exp, bias, exp_u);
                SASSERT(mpzm.is_int64(exp_u));
                
                mpzm.power(mpz(2), sbits - 1, tmp_p);
                mpzm.mod(all_bits, tmp_p, sig);

                scoped_mpf f(mpfm);                
                mpfm.set(f, ebits, sbits, mpzm.is_one(sgn), sig, mpzm.get_int64(exp_u));
                result = fu.mk_value(f);
            }
            break;
        }
        case OP_FLOAT_FP: {         
            bool is_internalized = ctx.e_internalized(m_a);
            if (is_internalized) {
                SASSERT(m_a->get_num_args() == 3);
                app_ref a_sgn(m), a_sig(m), a_exp(m);
                a_sgn = to_app(m_a->get_arg(0));
                a_exp = to_app(m_a->get_arg(1));
                a_sig = to_app(m_a->get_arg(2));

                scoped_mpz bias(mpzm);
                mpzm.power(mpz(2), ebits - 1, bias);
                mpzm.dec(bias);

                rational sgn(0), sig(0), exp(bias);
                th_bv->get_fixed_value(a_sgn, sgn);
                th_bv->get_fixed_value(a_sig, sig);
                th_bv->get_fixed_value(a_exp, exp);

                TRACE("t_fpa", tout << "sgn=" << sgn.to_string() << " ; " <<
                                       "sig=" << sig.to_string() << " ; " <<
                                       "exp=" << exp.to_string() << std::endl;);

                rational exp_u = exp - rational(bias);
                SASSERT(exp_u.is_int64());

                scoped_mpf f(mpfm);
                scoped_mpq sig_q(mpqm);
                sig_q = sig.to_mpq();
                mpfm.set(f, ebits, sbits, sgn.is_one(), sig_q.get().numerator(), exp_u.get_int64());
                result = fu.mk_value(f);
            }
            else {            
                result = fu.mk_nan(ebits, sbits);
            }
            break;
        }
        default:
            NOT_IMPLEMENTED_YET();
        }

        TRACE("t_fpa", tout << "fpa_value_proc::mk_value result: " << mk_ismt2_pp(result, m_th.get_manager()) << "\n";);
        return result;
    }

    app * theory_fpa::fpa_rm_value_proc::mk_value(model_generator & mg, ptr_vector<expr> & values) {        
        TRACE("t_fpa", tout << "fpa_rm_value_proc::mk_value for: " << mk_ismt2_pp(m_a, m_th.get_manager()) << "\n";);
        ast_manager & m = m_th.get_manager();
        context & ctx = m_th.get_context();
        theory_id bv_id = m.mk_family_id("bv");
        theory_bv * th_bv = dynamic_cast<theory_bv *>(ctx.get_theory(bv_id));

        app * result = 0;
        mpf_rounding_mode rm;
        if (m_th.m_converter.fu().is_rm_value(m_a, rm)) {
            result = m_a.get();
        }
        else {
            sort * s = m.get_sort(m_a);
            func_decl *w, *u;
            m_th.get_wrap(s, w, u);

            app_ref bv_w(m);
            bv_w = m.mk_app(w, m_a);

            rational val(0);
            if (ctx.e_internalized(bv_w))
                if (!th_bv->get_fixed_value(bv_w, val))
                    val = rational(0);
            
            switch (val.get_uint64())
            {
            case BV_RM_TIES_TO_AWAY: result = m_fu.mk_round_nearest_ties_to_away(); break;
            case BV_RM_TIES_TO_EVEN: result = m_fu.mk_round_nearest_ties_to_even(); break;
            case BV_RM_TO_NEGATIVE: result = m_fu.mk_round_toward_negative(); break;
            case BV_RM_TO_POSITIVE: result = m_fu.mk_round_toward_positive(); break;
            case BV_RM_TO_ZERO:
            default: result = m_fu.mk_round_toward_zero();
            }
        }

        TRACE("t_fpa", tout << "fpa_rm_value_proc::mk_value result: " << mk_ismt2_pp(result, m_th.get_manager()) << "\n";);
        return result;
    }

    void theory_fpa::get_wrap(sort * s, func_decl *& wrap, func_decl *& unwrap)
    {
        if (!m_wraps.find(s, wrap) || !m_unwraps.find(s, unwrap)) {
            SASSERT(!m_wraps.contains(s));
            ast_manager & m = get_manager();
            sort * bv_srt = 0;

            if (m_converter.is_rm(s))
                bv_srt = m_converter.bu().mk_sort(3);
            else {
                SASSERT(m_converter.is_float(s));                
                unsigned ebits = m_converter.fu().get_ebits(s);
                unsigned sbits = m_converter.fu().get_sbits(s);
                bv_srt = m_converter.bu().mk_sort(ebits + sbits);
            }

            wrap = m.mk_func_decl(get_family_id(), OP_FLOAT_INTERNAL_BVWRAP, 0, 0, 1, &s, bv_srt);
            unwrap = m.mk_func_decl(get_family_id(), OP_FLOAT_INTERNAL_BVUNWRAP, 0, 0, 1, &bv_srt, s);
            m_wraps.insert(s, wrap);
            m_unwraps.insert(s, unwrap);
            get_context().push_trail(insert_obj_map<context, sort, func_decl*>(m_wraps, s));
            get_context().push_trail(insert_obj_map<context, sort, func_decl*>(m_unwraps, s));
        }
    }
    
    expr_ref theory_fpa::convert_atom(expr * e) {
        ast_manager & m = get_manager();
        expr_ref res(m);
        proof_ref pr(m);
        m_rw(e, res);

        TRACE("t_fpa", tout << "converted atom:" << std::endl;
        tout << mk_ismt2_pp(e, m) << std::endl << " -> " << std::endl <<
            mk_ismt2_pp(res, m) << std::endl;);
        return res;
    }

    expr_ref theory_fpa::convert_term(expr * e) {
        ast_manager & m = get_manager();
        expr_ref res(m);
        proof_ref pr(m);
        m_rw(e, res);
        
        SASSERT(is_app(res));
        
        if (m_converter.fu().is_rm(e)) {
            SASSERT(is_sort_of(m.get_sort(res), m_converter.bu().get_family_id(), BV_SORT));
            SASSERT(m_converter.bu().get_bv_size(res) == 3);
        }
        else {
            SASSERT(to_app(res)->get_family_id() == get_family_id());
            decl_kind k = to_app(res)->get_decl_kind();
            if (k == OP_FLOAT_TO_FP) {
                SASSERT(to_app(res)->get_num_args() == 3);
                SASSERT(is_sort_of(m.get_sort(to_app(res)->get_arg(0)), m_converter.bu().get_family_id(), BV_SORT));
                SASSERT(is_sort_of(m.get_sort(to_app(res)->get_arg(1)), m_converter.bu().get_family_id(), BV_SORT));
                SASSERT(is_sort_of(m.get_sort(to_app(res)->get_arg(2)), m_converter.bu().get_family_id(), BV_SORT));

                expr *sgn, *sig, *exp;
                expr_ref s_sgn(m), s_sig(m), s_exp(m);
                m_converter.split_triple(res, sgn, sig, exp);
                m_th_rw(sgn, s_sgn);
                m_th_rw(sig, s_sig);
                m_th_rw(exp, s_exp);

                m_converter.mk_triple(s_sgn, s_sig, s_exp, res);
            }
            else {
                SASSERT(is_sort_of(m.get_sort(e), get_family_id(), ROUNDING_MODE_SORT));
                SASSERT(is_sort_of(m.get_sort(res), m_converter.bu().get_family_id(), BV_SORT));
            }
        }

        TRACE("t_fpa", tout << "converted term:" << std::endl;
                    tout << mk_ismt2_pp(e, m) << std::endl << " -> " << std::endl <<
                    mk_ismt2_pp(res, m) << std::endl;);
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

        TRACE("t_fpa", if (!m.is_true(res)) tout << "side condition: " << mk_ismt2_pp(res, m) << "\n";);
        return res;
    }

    void theory_fpa::assert_cnstr(expr * e) {
        if (get_manager().is_true(e)) return;
        TRACE("t_fpa", tout << "asserting " << mk_ismt2_pp(e, get_manager()) << "\n";);
        context& ctx = get_context();
        ctx.internalize(e, false);
        literal lit(ctx.get_literal(e));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }    

    void theory_fpa::attach_new_th_var(enode * n) {
        context & ctx = get_context();
        theory_var v = mk_var(n);
        ctx.attach_th_var(n, this, v);
        m_tvars.push_back(v);        
        TRACE("t_fpa", tout << "new theory var: " << mk_ismt2_pp(n->get_owner(), get_manager()) << " := " << v << "\n";);       
    }

    bool theory_fpa::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("t_fpa_detail", tout << "internalizing atom: " << mk_ismt2_pp(atom, get_manager()) << "\n";);
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
        bv_atom = m.mk_and(bv_atom, mk_side_conditions());
        
        expr_ref atom_iff(m);
        assert_cnstr(m.mk_iff(atom, bv_atom));
        return true;
    }

    bool theory_fpa::internalize_term(app * term) {
        TRACE("t_fpa_detail", tout << "internalizing term: " << mk_ismt2_pp(term, get_manager()) << "\n";);
        SASSERT(term->get_family_id() == get_family_id());
        SASSERT(!get_context().e_internalized(term));

        ast_manager & m = get_manager();
        context & ctx = get_context();

        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(term->get_arg(i), false);
        
        enode * e = (ctx.e_internalized(term)) ? ctx.get_enode(term) : 
                                                 ctx.mk_enode(term, false, false, true);

        if (is_attached_to_var(e))
            return false;

        attach_new_th_var(e);
        TRACE("t_fpa", tout << "internalized? " << (ctx.e_internalized(term)?"yes":"no") << std::endl;);
        return true;
    }    

    void theory_fpa::apply_sort_cnstr(enode * n, sort * s) {        
        TRACE("t_fpa", tout << "apply sort cnstr for: " << mk_ismt2_pp(n->get_owner(), get_manager()) << "\n";);        
        SASSERT(n->get_owner()->get_family_id() == get_family_id() ||
                n->get_owner()->get_family_id() == null_theory_id);
        SASSERT(s->get_family_id() == get_family_id());
        ast_manager & m = get_manager();        

        if (!is_attached_to_var(n))
            attach_new_th_var(n);
            
        app * owner = n->get_owner();
        sort * owner_sort = m.get_sort(owner);
        if (m_converter.is_rm(owner_sort)) {
            bv_util & bu = m_converter.bu();
            func_decl *wrap, *unwrap;
            get_wrap(owner_sort, wrap, unwrap);
            if (owner->get_decl() != unwrap)
            {                
                expr_ref converted(m), t(m);
                m_rw(owner, converted);
                t = bu.mk_ule(converted, bu.mk_numeral(4, 3));
                assert_cnstr(t);
            }
        }
    }

    void theory_fpa::new_eq_eh(theory_var x, theory_var y) {        
        ast_manager & m = get_manager();

        TRACE("t_fpa", tout << "new eq: " << x << " = " << y << std::endl;
                       tout << mk_ismt2_pp(get_enode(x)->get_owner(), m) << " = " << 
                               mk_ismt2_pp(get_enode(y)->get_owner(), m) << std::endl; );
        
        context & ctx = get_context();
        float_util & fu = m_converter.fu();
        bv_util & bu = m_converter.bu();
        mpf_manager & mpfm = fu.fm();

        app * xe = get_enode(x)->get_owner();
        app * ye = get_enode(y)->get_owner();        

        if (fu.is_float(xe) && fu.is_float(ye))
        {
            expr_ref xc(m), yc(m);
            xc = convert_term(xe);
            yc = convert_term(ye);

            expr *x_sgn, *x_sig, *x_exp;
            m_converter.split_triple(xc, x_sgn, x_sig, x_exp);
            expr *y_sgn, *y_sig, *y_exp;
            m_converter.split_triple(yc, y_sgn, y_sig, y_exp);

            expr_ref c(m);
            c = m.mk_and(m.mk_eq(x_sgn, y_sgn),
                         m.mk_eq(x_sig, y_sig),
                         m.mk_eq(x_exp, y_exp));
            assert_cnstr(c);
            assert_cnstr(mk_side_conditions());
        }
        else if (fu.is_rm(xe) && fu.is_rm(ye)) {
            expr_ref xc(m), yc(m);
            xc = convert_term(xe);
            yc = convert_term(ye);
            expr_ref c(m);
            c = m.mk_eq(xc, yc);
            assert_cnstr(c);
            assert_cnstr(mk_side_conditions());
        }
        
        return;
    }

    void theory_fpa::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager & m = get_manager();

        TRACE("t_fpa", tout << "new diseq: " << x << " != " << y << std::endl;
                       tout << mk_ismt2_pp(get_enode(x)->get_owner(), m) << " != " <<
                               mk_ismt2_pp(get_enode(y)->get_owner(), m) << std::endl;);

        context & ctx = get_context();
        float_util & fu = m_converter.fu();
        bv_util & bu = m_converter.bu();
        mpf_manager & mpfm = fu.fm();

        app * xe = get_enode(x)->get_owner();
        app * ye = get_enode(y)->get_owner();

        if (fu.is_float(xe) && fu.is_float(ye))
        {
            expr_ref xc(m), yc(m);
            xc = convert_term(xe);
            yc = convert_term(ye);

            expr *x_sgn, *x_sig, *x_exp;
            m_converter.split_triple(xc, x_sgn, x_sig, x_exp);
            expr *y_sgn, *y_sig, *y_exp;
            m_converter.split_triple(yc, y_sgn, y_sig, y_exp);

            expr_ref c(m);
            c = m.mk_or(m.mk_not(m.mk_eq(x_sgn, y_sgn)),
                        m.mk_not(m.mk_eq(x_sig, y_sig)),
                        m.mk_not(m.mk_eq(x_exp, y_exp)));
            assert_cnstr(c);
            assert_cnstr(mk_side_conditions());
        }
        else if (fu.is_rm(xe) && fu.is_rm(ye)) {
            expr_ref xc(m), yc(m);
            xc = convert_term(xe);
            yc = convert_term(ye);
            expr_ref c(m);
            c = m.mk_not(m.mk_eq(xc, yc));
            assert_cnstr(c);
            assert_cnstr(mk_side_conditions());
        }

        return;
    }

    void theory_fpa::push_scope_eh() {
        theory::push_scope_eh();
        m_trail_stack.push_scope();
    }

    void theory_fpa::pop_scope_eh(unsigned num_scopes) {
        TRACE("t_fpa", tout << num_scopes << "\n";);        
        m_trail_stack.pop_scope(num_scopes);
        unsigned num_old_vars = get_old_num_vars(num_scopes);
        for (unsigned i = num_old_vars; i < get_num_vars(); i++) {
            // m_trans_map.erase(get_enode(m_tvars[i])->get_owner());
        }
        m_tvars.shrink(num_old_vars);
        theory::pop_scope_eh(num_scopes);
    }    

    void theory_fpa::assign_eh(bool_var v, bool is_true) {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        expr * e = ctx.bool_var2expr(v);
        
        TRACE("t_fpa", tout << "assign_eh for: " << v << " (" << is_true << "):\n" << mk_ismt2_pp(e, m) << "\n";);
        
        expr_ref converted(m);
        m_rw(e, converted);
        converted = m.mk_and(converted, mk_side_conditions());
        if (!is_true) converted = m.mk_not(converted);
        assert_cnstr(converted);
    }

    void theory_fpa::relevant_eh(app * n) {
        TRACE("t_fpa", tout << "relevant_eh for: " << mk_ismt2_pp(n, get_manager()) << "\n";);
        
        NOT_IMPLEMENTED_YET();

        ast_manager & m = get_manager();

        if (m.is_bool(n))
            return;

        float_util & fu = m_converter.fu();
        bv_util & bu = m_converter.bu();
        mpf_manager & mpfm = fu.fm();

        if (bu.is_bv(n))
            return;

        sort * s = m.get_sort(n);
        func_decl *wrap, *unwrap;
        get_wrap(s, wrap, unwrap);

        if (n->get_decl() != unwrap) {
            expr * wrapped = m.mk_app(wrap, n);
            mpf_rounding_mode rm;
            scoped_mpf val(mpfm);
            if (fu.is_rm_value(n, rm))
                assert_cnstr(m.mk_eq(wrapped, bu.mk_numeral(rm, 3)));
            else if (fu.is_value(n, val)) {
                unsigned sz = val.get().get_ebits() + val.get().get_sbits();
                scoped_mpq q(fu.fm().mpq_manager());
                mpfm.to_rational(val, q);
                assert_cnstr(m.mk_eq(wrapped, bu.mk_numeral(rational(q), sz)));
            }
            else
                assert_cnstr(m.mk_eq(m.mk_app(unwrap, wrapped), n));
        }
    }

    void theory_fpa::reset_eh() {
        TRACE("t_fpa", tout << "reset_eh for: " << "\n";);
        pop_scope_eh(m_trail_stack.get_num_scopes());
        m_rw.reset();
        m_bool_var2atom.reset();
        m_temporaries.reset();
        m_tvars.reset();
        theory::reset_eh();
    }

    void theory_fpa::init_model(model_generator & mg) {
        TRACE("t_fpa", tout << "initializing model" << std::endl;);
        m_factory = alloc(fpa_factory, get_manager(), get_family_id());
        mg.register_factory(m_factory);
        TRACE("t_fpa", display(tout););
    }

    model_value_proc * theory_fpa::mk_value(enode * n, model_generator & mg) {
        TRACE("t_fpa", tout << "mk_value for: " << mk_ismt2_pp(n->get_owner(), get_manager()) << "\n";);

        ast_manager & m = get_manager();
        float_util & fu = m_converter.fu();

        expr * owner = n->get_owner();
        sort * o_srt = m.get_sort(owner);

        mpf_rounding_mode rm;

        if (fu.is_rm_value(n->get_owner(), rm))
            return alloc(expr_wrapper_proc, n->get_owner());
        else if (fu.is_value(n->get_owner()))
            return alloc(expr_wrapper_proc, n->get_owner());
        else if (fu.is_rm(owner))
            return alloc(fpa_rm_value_proc, this, app_ref(to_app(owner), m));
        else if (fu.is_float(owner))
            return alloc(fpa_value_proc, this, app_ref(to_app(owner), m));
        
        UNREACHABLE();
        return 0;
    }

    void theory_fpa::finalize_model(model_generator & mg) {}

    void theory_fpa::display(std::ostream & out) const
    {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        
        out << "theory variables:" << std::endl;        
        ptr_vector<enode>::const_iterator it = ctx.begin_enodes();
        ptr_vector<enode>::const_iterator end = ctx.end_enodes();
        for (; it != end; it++)
            out << (*it)->get_th_var(get_family_id()) << " -> " <<
            mk_ismt2_pp((*it)->get_owner(), m) << std::endl; 
    }
};
