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

    bool theory_fpa::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("fpa", tout << "internalizing atom: " << mk_ismt2_pp(atom, get_manager()) << "\n";);
        SASSERT(atom->get_family_id() == get_family_id());
        NOT_IMPLEMENTED_YET();
    }

    bool theory_fpa::internalize_term(app * term) {
        TRACE("fpa", tout << "internalizing term: " << mk_ismt2_pp(term, get_manager()) << "\n";);
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
        TRACE("fpa", tout << "converted: " << mk_ismt2_pp(res, get_manager()) << "\n";);

        expr_ref sgn(m), sig(m), exp(m);
        proof_ref pr_sgn(m), pr_sig(m), pr_exp(m);
        simp(a->get_arg(0), sgn, pr_sgn);
        simp(a->get_arg(1), sig, pr_sig);
        simp(a->get_arg(2), exp, pr_exp);        

        ctx.internalize(sgn, false);
        ctx.internalize(sig, false);
        ctx.internalize(exp, false);

        expr_ref s_term(m);
        m_converter.mk_triple(sgn, sig, exp, s_term);

        SASSERT(!m_trans_map.contains(term));
        m_trans_map.insert(term, s_term, 0);

        enode * e = ctx.mk_enode(term, false, false, true);
        theory_var v = mk_var(e);
        ctx.attach_th_var(e, this, v);
        TRACE("fpa", tout << "new theory var: " << mk_ismt2_pp(term, get_manager()) << " := " << v << "\n";);
        SASSERT(e->get_th_var(get_id()) != null_theory_var);

        return v != null_theory_var;
    }

    void theory_fpa::apply_sort_cnstr(enode * n, sort * s) {
        if (!is_attached_to_var(n)) {
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
                ctx.internalize(converted, false);
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
            }

            TRACE("fpa", tout << "new const: " << mk_ismt2_pp(owner, get_manager()) << " := " << v << "\n";);
        }
    }

    void theory_fpa::new_eq_eh(theory_var x, theory_var y) {
        TRACE("fpa", tout << "new eq: " << x << " = " << y << "\n";);
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
                
        literal_vector lits;
        lits.push_back(mk_eq(ax, ay, true));

        expr_ref e1(m), e2(m), e3(m);
        e1 = m.mk_eq(sgn_x, sgn_y);
        e2 = m.mk_eq(sig_x, sig_y);
        e3 = m.mk_eq(exp_x, exp_y);
        ctx.internalize(e1, true);
        ctx.internalize(e2, true);
        ctx.internalize(e3, true);
        lits.push_back(ctx.get_literal(e1));
        lits.push_back(ctx.get_literal(e2));
        lits.push_back(ctx.get_literal(e3));
        
        ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());
    }

    void theory_fpa::new_diseq_eh(theory_var x, theory_var y) {
        TRACE("fpa", tout << "new eq: " << x << " = " << y << "\n";);
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

        ctx.internalize(m.mk_not(m.mk_eq(sgn_x, sgn_y)), true);
        ctx.internalize(m.mk_not(m.mk_eq(sig_x, sig_y)), true);
        ctx.internalize(m.mk_not(m.mk_eq(exp_x, exp_y)), true);
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
        unsynch_mpz_manager & mpzm = fu.fm().mpz_manager();
        unsynch_mpq_manager & mpqm = fu.fm().mpq_manager();

        theory_var v = n->get_th_var(get_id());
        SASSERT(v != null_theory_var);
        expr * fpa_e = get_enode(v)->get_owner();
        TRACE("fpa", tout << "mk_value for: " << mk_ismt2_pp(fpa_e, m) << "\n";);
        
        expr * bv_e;
        proof * bv_pr;
        m_trans_map.get(fpa_e, bv_e, bv_pr);

        expr_wrapper_proc * res = 0;

        if (fu.is_rm(m.get_sort(fpa_e))) {
            SASSERT(ctx.e_internalized(bv_e));
            sort * s = m.get_sort(bv_e);
            family_id fid = s->get_family_id();
            theory * bv_th = ctx.get_theory(fid);

            enode * ev = ctx.get_enode(bv_e);
            ptr_vector<expr> pve;
            app_ref mv(m);
            mv = ((expr_wrapper_proc*)bv_th->mk_value(ev, mg))->mk_value(mg, pve);
            
            rational val(0);
            unsigned sz = 0;
            if (bu.is_numeral(mv, val, sz)) {                
                app_ref fp_val_e(m);
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
                
                TRACE("fpa", tout << mk_ismt2_pp(fpa_e, m) << " := " << mk_ismt2_pp(fp_val_e, m) << std::endl;);
                res = alloc(expr_wrapper_proc, fp_val_e);
                m.inc_ref(fp_val_e);
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

            sort * s = m.get_sort(e_sgn->get_owner());
            family_id fid = s->get_family_id();
            theory * bv_th = ctx.get_theory(fid);

            expr_wrapper_proc * mv_sgn = (expr_wrapper_proc*)bv_th->mk_value(e_sgn, mg);
            expr_wrapper_proc * mv_sig = (expr_wrapper_proc*)bv_th->mk_value(e_sig, mg);
            expr_wrapper_proc * mv_exp = (expr_wrapper_proc*)bv_th->mk_value(e_exp, mg);

            ptr_vector<expr> pve;
            app_ref bvm_sgn(m), bvm_sig(m), bvm_exp(m);
            bvm_sgn = mv_sgn->mk_value(mg, pve);
            bvm_sig = mv_sig->mk_value(mg, pve);
            bvm_exp = mv_exp->mk_value(mg, pve);

            TRACE("fpa", tout << "bv model: [" << mk_ismt2_pp(bvm_sgn, get_manager()) << " "
                  << mk_ismt2_pp(bvm_sig, get_manager()) << " "
                  << mk_ismt2_pp(bvm_exp, get_manager()) << "]\n";);

            unsigned sgn_sz, sig_sz, exp_sz;
            rational sgn_q(0), sig_q(0), exp_q(0);
            if (bvm_sgn) bu.is_numeral(bvm_sgn, sgn_q, sgn_sz);
            if (bvm_sig) bu.is_numeral(bvm_sig, sig_q, sig_sz);
            if (bvm_exp) bu.is_numeral(bvm_exp, exp_q, exp_sz);

            // un-bias exponent
            rational exp_unbiased_q;
            exp_unbiased_q = exp_q - fu.fm().m_powers2.m1(exp_sz - 1);

            mpz sig_z; mpf_exp_t exp_z;
            mpzm.set(sig_z, sig_q.to_mpq().numerator());
            exp_z = mpzm.get_int64(exp_unbiased_q.to_mpq().numerator());

            mpf fp_val;
            fu.fm().set(fp_val, exp_sz, sig_sz+1, !mpqm.is_zero(sgn_q.to_mpq()), sig_z, exp_z);            

            app_ref fp_val_e(m);
            fp_val_e = fu.mk_value(fp_val);
            mpzm.del(sig_z);

            TRACE("fpa", tout << mk_ismt2_pp(fpa_e, m) << " := " << mk_ismt2_pp(fp_val_e, m) << std::endl;);

            res = alloc(expr_wrapper_proc, fp_val_e);
            m.inc_ref(fp_val_e);
        }

        return res;
    }
};
