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

    theory_fpa::theory_fpa(ast_manager & m) :
        theory(m.mk_family_id("float")),
        m_converter(m),
        m_rw(m, m_converter, params_ref()),
        m_trans_map(m),
        m_trail_stack(*this)
    {
    }

    theory_fpa::~theory_fpa()
    {
    }

    bool theory_fpa::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("t_fpa", tout << "internalizing atom: " << mk_ismt2_pp(atom, get_manager()) << "\n";);
        SASSERT(atom->get_family_id() == get_family_id());
        NOT_IMPLEMENTED_YET();
    }

    bool theory_fpa::internalize_term(app * term) {
        TRACE("t_fpa", tout << "internalizing term: " << mk_ismt2_pp(term, get_manager()) << "\n";);
        SASSERT(term->get_family_id() == get_family_id());
        SASSERT(!get_context().e_internalized(term));

        ast_manager & m = get_manager();
        context & ctx = get_context();
        simplifier & simp = ctx.get_simplifier();        
        
        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(term->get_arg(i), false);

        expr_ref res(m);
        m_rw(term, res);
        SASSERT(is_app(res) && to_app(res)->get_num_args() == 3);
        app * a = to_app(res);
        TRACE("t_fpa", tout << "converted: " << mk_ismt2_pp(res, get_manager()) << "\n";);

        expr_ref sgn(m), sig(m), exp(m);
        proof_ref pr_sgn(m), pr_sig(m), pr_exp(m);
        simp(a->get_arg(0), sgn, pr_sgn);
        simp(a->get_arg(1), sig, pr_sig);
        simp(a->get_arg(2), exp, pr_exp);        

        expr_ref bv_v_sgn(m), bv_v_sig(m), bv_v_exp(m);
        bv_v_sgn = m.mk_fresh_const("fpa2bv", m.get_sort(sgn));
        bv_v_sig = m.mk_fresh_const("fpa2bv", m.get_sort(sig));
        bv_v_exp = m.mk_fresh_const("fpa2bv", m.get_sort(exp));        
        expr_ref e1(m), e2(m), e3(m);
        e1 = m.mk_eq(bv_v_sgn, sgn);
        e2 = m.mk_eq(bv_v_sig, sig);
        e3 = m.mk_eq(bv_v_exp, exp);
        ctx.internalize(e1, false);
        ctx.internalize(e2, false);
        ctx.internalize(e3, false);
        ctx.mk_th_axiom(get_id(), 1, &ctx.get_literal(e1));
        ctx.mk_th_axiom(get_id(), 1, &ctx.get_literal(e2));
        ctx.mk_th_axiom(get_id(), 1, &ctx.get_literal(e3));
        ctx.mark_as_relevant(e1);
        ctx.mark_as_relevant(e2);
        ctx.mark_as_relevant(e3);

        expr_ref s_term(m);
        m_converter.mk_triple(bv_v_sgn, bv_v_sig, bv_v_exp, s_term);

        SASSERT(!m_trans_map.contains(term));
        m_trans_map.insert(term, s_term, 0);

        enode * e = ctx.mk_enode(term, false, false, true);
        theory_var v = mk_var(e);        
        ctx.attach_th_var(e, this, v);
        TRACE("t_fpa", tout << "new theory var: " << mk_ismt2_pp(term, get_manager()) << " := " << v << "\n";);
        SASSERT(e->get_th_var(get_id()) != null_theory_var);

        return v != null_theory_var;
    }

    void theory_fpa::apply_sort_cnstr(enode * n, sort * s) {
        if (!is_attached_to_var(n)) {
            TRACE("t_fpa", tout << "apply sort cnstr for: " << mk_ismt2_pp(n->get_owner(), get_manager()) << "\n";);
            context & ctx = get_context();
            ast_manager & m = get_manager();
            simplifier & simp = ctx.get_simplifier();
            app * owner = n->get_owner();
            expr_ref converted(m);

            theory_var v = mk_var(n);            
            ctx.attach_th_var(n, this, v);
            m_rw(owner, converted);
            m_trans_map.insert(owner, converted, 0);
            
            if (m_converter.is_rm_sort(m.get_sort(owner))) {
                expr_ref bv_v(m), eq(m);
                bv_v = m.mk_fresh_const("fpa2bv", m.get_sort(converted));                
                eq = m.mk_eq(bv_v, converted);
                ctx.internalize(eq, false);
                literal l = ctx.get_literal(eq);
                ctx.mk_th_axiom(get_id(), 1, &l);
            }
            else {
                app * a = to_app(converted);
                expr_ref sgn(m), sig(m), exp(m);
                proof_ref pr_sgn(m), pr_sig(m), pr_exp(m);
                simp(a->get_arg(0), sgn, pr_sgn);
                simp(a->get_arg(1), sig, pr_sig);
                simp(a->get_arg(2), exp, pr_exp);

                ctx.internalize(sgn, false);
                ctx.internalize(sig, false);
                ctx.internalize(exp, false);

                expr_ref bv_v_sgn(m), bv_v_sig(m), bv_v_exp(m);
                bv_v_sgn = m.mk_fresh_const("fpa2bv", m.get_sort(sgn));
                bv_v_sig = m.mk_fresh_const("fpa2bv", m.get_sort(sig));
                bv_v_exp = m.mk_fresh_const("fpa2bv", m.get_sort(exp));
                expr_ref e1(m), e2(m), e3(m);
                e1 = m.mk_eq(bv_v_sgn, sgn);
                e2 = m.mk_eq(bv_v_sig, sig);
                e3 = m.mk_eq(bv_v_exp, exp);
                ctx.internalize(e1, true);
                ctx.internalize(e2, true);
                ctx.internalize(e3, true);
                ctx.mk_th_axiom(get_id(), 1, &ctx.get_literal(e1));
                ctx.mk_th_axiom(get_id(), 1, &ctx.get_literal(e2));
                ctx.mk_th_axiom(get_id(), 1, &ctx.get_literal(e3));
                ctx.mark_as_relevant(e1);
                ctx.mark_as_relevant(e2);
                ctx.mark_as_relevant(e3);
            }

            TRACE("t_fpa", tout << "new theory var (const): " << mk_ismt2_pp(owner, get_manager()) << " := " << v << "\n";);
        }
    }

    void theory_fpa::new_eq_eh(theory_var x, theory_var y) {
        TRACE("t_fpa", tout << "new eq: " << x << " = " << y << "\n";);
        ast_manager & m = get_manager();
        context & ctx = get_context();
        app * ax = get_enode(x)->get_owner();
        app * ay = get_enode(y)->get_owner();

        expr * ex, * ey;
        proof * px, * py;
        m_trans_map.get(ax, ex, px);
        m_trans_map.get(ay, ey, py);

        expr * sgn_x, * sig_x, * exp_x;
        expr * sgn_y, * sig_y, * exp_y;
        split_triple(ex, sgn_x, sig_x, exp_x);
        split_triple(ey, sgn_y, sig_y, exp_y);
                
        expr_ref e1(m), e2(m), e3(m);
        e1 = m.mk_eq(sgn_x, sgn_y);
        e2 = m.mk_eq(sig_x, sig_y);
        e3 = m.mk_eq(exp_x, exp_y);
        ctx.internalize(e1, true);
        ctx.internalize(e2, true);
        ctx.internalize(e3, true);
        ctx.mk_th_axiom(get_id(), 1, &ctx.get_literal(e1));
        ctx.mk_th_axiom(get_id(), 1, &ctx.get_literal(e2));
        ctx.mk_th_axiom(get_id(), 1, &ctx.get_literal(e3));
        ctx.mark_as_relevant(e1);
        ctx.mark_as_relevant(e2);
        ctx.mark_as_relevant(e3);
    }

    void theory_fpa::new_diseq_eh(theory_var x, theory_var y) {
        TRACE("t_fpa", tout << "new eq: " << x << " = " << y << "\n";);
        ast_manager & m = get_manager();
        context & ctx = get_context();
        app * ax = get_enode(x)->get_owner();
        app * ay = get_enode(y)->get_owner();

        expr * ex, *ey;
        proof * px, *py;
        m_trans_map.get(ax, ex, px);
        m_trans_map.get(ay, ey, py);

        expr * sgn_x, *sig_x, *exp_x;
        expr * sgn_y, *sig_y, *exp_y;
        split_triple(ex, sgn_x, sig_x, exp_x);
        split_triple(ex, sgn_y, sig_y, exp_y);

        expr_ref e1(m), e2(m), e3(m);
        e1 = m.mk_not(m.mk_eq(sgn_x, sgn_y));
        e2 = m.mk_or(e1, m.mk_not(m.mk_eq(sig_x, sig_y)));
        e3 = m.mk_or(e2, m.mk_not(m.mk_eq(exp_x, exp_y)));
        ctx.internalize(e3, true);
        ctx.mk_th_axiom(get_id(), 1, &ctx.get_literal(e3));
        ctx.mark_as_relevant(e3);
    }

    void theory_fpa::push_scope_eh() {
        theory::push_scope_eh();
        m_trail_stack.push_scope();
    }

    void theory_fpa::pop_scope_eh(unsigned num_scopes) {
        m_trail_stack.pop_scope(num_scopes);
        theory::pop_scope_eh(num_scopes);
    }

    model_value_proc * theory_fpa::mk_value(enode * n, model_generator & mg) {        
        ast_manager & m = get_manager();
        context & ctx = get_context();
        bv_util & bu = m_converter.bu();
        float_util & fu = m_converter.fu();
        mpf_manager & mpfm = fu.fm();
        unsynch_mpz_manager & mpzm = mpfm.mpz_manager();
        unsynch_mpq_manager & mpqm = mpfm.mpq_manager();

        theory_var v = n->get_th_var(get_id());
        SASSERT(v != null_theory_var);
        expr * fpa_e = get_enode(v)->get_owner();
        TRACE("t_fpa", tout << "mk_value for: " << mk_ismt2_pp(fpa_e, m) << "\n";);
        
        expr * bv_e;
        proof * bv_pr;
        m_trans_map.get(fpa_e, bv_e, bv_pr);

        expr_wrapper_proc * res = 0;

        if (fu.is_rm(m.get_sort(fpa_e))) {
            SASSERT(ctx.e_internalized(bv_e));
            sort * s = m.get_sort(bv_e);
            family_id fid = s->get_family_id();
            theory_bv * bv_th = (theory_bv*)ctx.get_theory(fid);
            rational val;
            if (!bv_th->get_fixed_value(ctx.get_enode(bv_e)->get_owner(), val)) {
                NOT_IMPLEMENTED_YET();  
            } 
            else
            {
                app * fp_val_e;
                SASSERT(val.is_uint64());
                switch (val.get_uint64())
                {
                case BV_RM_TIES_TO_AWAY: fp_val_e = fu.mk_round_nearest_ties_to_away(); break;
                case BV_RM_TIES_TO_EVEN: fp_val_e = fu.mk_round_nearest_ties_to_even(); break;
                case BV_RM_TO_NEGATIVE: fp_val_e = fu.mk_round_toward_negative(); break;
                case BV_RM_TO_POSITIVE: fp_val_e = fu.mk_round_toward_positive(); break;
                case BV_RM_TO_ZERO:
                default: fp_val_e = fu.mk_round_toward_zero();
                }                
                
                TRACE("t_fpa", tout << mk_ismt2_pp(fpa_e, m) << " := " << mk_ismt2_pp(fp_val_e, m) << std::endl;);
                res = alloc(expr_wrapper_proc, fp_val_e);
            }
        }
        else {
            expr * bv_sgn, *bv_sig, *bv_exp;
            split_triple(bv_e, bv_sgn, bv_sig, bv_exp);

            SASSERT(ctx.e_internalized(bv_sgn));
            SASSERT(ctx.e_internalized(bv_sig));
            SASSERT(ctx.e_internalized(bv_exp));

            enode * e_sgn = ctx.get_enode(bv_sgn);
            enode * e_sig = ctx.get_enode(bv_sig);
            enode * e_exp = ctx.get_enode(bv_exp);            

            TRACE("t_fpa", tout << "bv rep: [" << mk_ismt2_pp(e_sgn->get_owner(), m) << " "
                                             << mk_ismt2_pp(e_sig->get_owner(), m) << " "
                                             << mk_ismt2_pp(e_exp->get_owner(), m) << "]\n";);

            sort * s = m.get_sort(e_sgn->get_owner());
            family_id fid = s->get_family_id();
            theory_bv * bv_th = (theory_bv*)ctx.get_theory(fid);                       

            SASSERT(bv_th->is_attached_to_var(e_sgn));
            SASSERT(bv_th->is_attached_to_var(e_sig));
            SASSERT(bv_th->is_attached_to_var(e_exp));

            unsigned sig_sz, exp_sz;
            sig_sz = bu.get_bv_size(e_sig->get_owner());
            exp_sz = bu.get_bv_size(e_exp->get_owner());

            rational sgn_r(0), sig_r(0), exp_r(0);            
            
            if (!bv_th->get_fixed_value(e_sgn->get_owner(), sgn_r) ||
                !bv_th->get_fixed_value(e_sig->get_owner(), sig_r) ||
                !bv_th->get_fixed_value(e_exp->get_owner(), exp_r))  {
                NOT_IMPLEMENTED_YET();
            }
            else {
                TRACE("t_fpa", tout << "bv model: [" << sgn_r.to_string() << " "
                                                   << sig_r.to_string() << " "
                                                   << exp_r.to_string() << "]\n";);

                // un-bias exponent
                rational exp_unbiased_r;
                exp_unbiased_r = exp_r - mpfm.m_powers2.m1(exp_sz - 1);

                mpz sig_z; mpf_exp_t exp_z;
                mpq sig_q, exp_q;
                mpz sig_num, exp_num;
                mpqm.set(sig_q, sig_r.to_mpq());
                mpzm.set(sig_num, sig_q.numerator());
                mpqm.set(exp_q, exp_unbiased_r.to_mpq());
                mpzm.set(exp_num, exp_q.numerator());
                mpzm.set(sig_z, sig_num);
                exp_z = mpzm.get_int64(exp_num);

                mpf fp_val;
                mpfm.set(fp_val, exp_sz, sig_sz + 1, !sgn_r.is_zero(), sig_z, exp_z);

                app * fp_val_e;
                fp_val_e = fu.mk_value(fp_val);

                TRACE("t_fpa", tout << mk_ismt2_pp(fpa_e, m) << " := " << mk_ismt2_pp(fp_val_e, m) << std::endl;);

                mpfm.del(fp_val);
                mpzm.del(sig_num);
                mpzm.del(exp_num);
                mpqm.del(sig_q);
                mpqm.del(exp_q);
                mpzm.del(sig_z);

                res = alloc(expr_wrapper_proc, fp_val_e);
            }
        }

        return res;
    }

    void theory_fpa::assign_eh(bool_var v, bool is_true) {
        TRACE("t_fpa", tout << "assign_eh for: " << v << " (" << is_true << ")\n";);
        UNREACHABLE();
    }

    void theory_fpa::relevant_eh(app * n) {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        float_util & fu = m_converter.fu();
        if (ctx.e_internalized(n)) {
            SASSERT(m_trans_map.contains(n));
            expr * ex;
            proof * px;
            m_trans_map.get(n, ex, px);

            if (fu.is_rm(m.get_sort(n))) {
                ctx.mark_as_relevant(ex);
            }
            else {
                expr * bv_sgn, *bv_sig, *bv_exp;
                split_triple(ex, bv_sgn, bv_sig, bv_exp);

                ctx.mark_as_relevant(bv_sgn);
                ctx.mark_as_relevant(bv_sig);
                ctx.mark_as_relevant(bv_exp);
            }
        }
        else
            NOT_IMPLEMENTED_YET();
    }
};
