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

    class mk_atom_trail : public trail<theory_fpa> {
        bool_var m_var;
    public:
        mk_atom_trail(bool_var v) : m_var(v) {}
        virtual ~mk_atom_trail() {}
        virtual void undo(theory_fpa & th) {
            theory_fpa::atom * a = th.get_bv2a(m_var);
            a->~atom();
            th.erase_bv2a(m_var);
        }
    };

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

    void theory_fpa::mk_bv_eq(expr * x, expr * y) {
        SASSERT(get_sort(x)->get_family_id() == m_converter.bu().get_family_id());
        ast_manager & m = get_manager();
        context & ctx = get_context();  
        theory_id bv_tid = ctx.get_theory(m.get_sort(x)->get_family_id())->get_id();
        literal l = mk_eq(x, y, false);        
        ctx.mk_th_axiom(get_id(), 1, &l);
        ctx.mark_as_relevant(l);
    }

    expr_ref theory_fpa::mk_eq_bv_const(expr_ref const & e) {
        ast_manager & m = get_manager();
        context & ctx = get_context();
        expr_ref bv_const(m);
        bv_const = m.mk_fresh_const(0, m.get_sort(e));
        mk_bv_eq(bv_const, e);
        return bv_const;
    }

    bool theory_fpa::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("t_fpa", tout << "internalizing atom: " << mk_ismt2_pp(atom, get_manager()) << "\n";);
        SASSERT(atom->get_family_id() == get_family_id());

        ast_manager & m = get_manager();
        context & ctx = get_context();
        simplifier & simp = ctx.get_simplifier();
        bv_util & bu = m_converter.bu();        
        expr_ref bv_atom(m);

        unsigned num_args = atom->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(atom->get_arg(i), false);

        m_rw(atom, bv_atom);

        ctx.internalize(bv_atom, gate_ctx);
        literal def = ctx.get_literal(bv_atom);
        literal l(ctx.mk_bool_var(atom));
        ctx.set_var_theory(l.var(), get_id());
        pred_atom * a = new (get_region()) pred_atom(l, def);
        insert_bv2a(l.var(), a);
        m_trail_stack.push(mk_atom_trail(l.var()));
        
        if (!ctx.relevancy()) {
            ctx.mk_th_axiom(get_id(), l, ~def);
            ctx.mk_th_axiom(get_id(), ~l, def);
        }

        return true;
    }

    bool theory_fpa::internalize_term(app * term) {
        TRACE("t_fpa", tout << "internalizing term: " << mk_ismt2_pp(term, get_manager()) << "\n";);
        SASSERT(term->get_family_id() == get_family_id());
        SASSERT(!get_context().e_internalized(term));

        ast_manager & m = get_manager();
        context & ctx = get_context();
        simplifier & simp = ctx.get_simplifier();
        bv_util & bu = m_converter.bu();
        sort * term_sort = m.get_sort(term);
        expr_ref t(m), bv_term(m);

        unsigned num_args = term->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            ctx.internalize(term->get_arg(i), false);

        m_rw(term, t);

        if (m_converter.is_rm_sort(term_sort)) {            
            SASSERT(is_app(t));
            expr_ref bv_rm(m);
            proof_ref bv_pr(m);
            simp(t, bv_rm, bv_pr);

            bv_term = mk_eq_bv_const(bv_rm);
        }
        else if (m_converter.is_float(term_sort)) {
            SASSERT(is_app(t) && to_app(t)->get_num_args() == 3);            
            app * a = to_app(t);
            expr_ref sgn(m), sig(m), exp(m);
            proof_ref pr_sgn(m), pr_sig(m), pr_exp(m);
            simp(a->get_arg(0), sgn, pr_sgn);
            simp(a->get_arg(1), sig, pr_sig);
            simp(a->get_arg(2), exp, pr_exp);

            expr_ref bv_v_sgn = mk_eq_bv_const(sgn);
            expr_ref bv_v_sig = mk_eq_bv_const(sig);
            expr_ref bv_v_exp = mk_eq_bv_const(exp);

            m_converter.mk_triple(bv_v_sgn, bv_v_sig, bv_v_exp, bv_term);
        }
        else if (term->get_decl_kind() == OP_TO_IEEE_BV) {
            SASSERT(is_app(t));
            expr_ref bv_e(m);
            proof_ref bv_pr(m);
            simp(t, bv_e, bv_pr);

            bv_term = mk_eq_bv_const(bv_e);
        }
        else
            NOT_IMPLEMENTED_YET();

        TRACE("t_fpa", tout << "converted: " << mk_ismt2_pp(bv_term, get_manager()) << "\n";);

        SASSERT(!m_trans_map.contains(term));
        m_trans_map.insert(term, bv_term, 0);

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
                mk_eq_bv_const(converted);
            }
            else {
                app * a = to_app(converted);
                expr_ref sgn(m), sig(m), exp(m);
                proof_ref pr_sgn(m), pr_sig(m), pr_exp(m);
                simp(a->get_arg(0), sgn, pr_sgn);
                simp(a->get_arg(1), sig, pr_sig);
                simp(a->get_arg(2), exp, pr_exp);

                mk_eq_bv_const(sgn);
                mk_eq_bv_const(sig);
                mk_eq_bv_const(exp);
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
        expr * ex, *ey;
        proof * px, *py;
        m_trans_map.get(ax, ex, px);
        m_trans_map.get(ay, ey, py);

        if (m_converter.fu().is_float(m.get_sort(get_enode(x)->get_owner()))) {            
            expr * sgn_x, *sig_x, *exp_x;
            expr * sgn_y, *sig_y, *exp_y;
            split_triple(ex, sgn_x, sig_x, exp_x);
            split_triple(ey, sgn_y, sig_y, exp_y);

            mk_bv_eq(sgn_x, sgn_y);
            mk_bv_eq(sig_x, sig_y);
            mk_bv_eq(exp_x, exp_y);
        }
        else if (m_converter.fu().is_rm(m.get_sort(get_enode(x)->get_owner()))) {
            mk_bv_eq(ex, ey);
        }
        else
            UNREACHABLE();
    }

    void theory_fpa::new_diseq_eh(theory_var x, theory_var y) {
        TRACE("t_fpa", tout << "new diseq: " << x << " != " << y << "\n";);
        ast_manager & m = get_manager();
        context & ctx = get_context();
        
        app * ax = get_enode(x)->get_owner();
        app * ay = get_enode(y)->get_owner();
        expr * ex, *ey;
        proof * px, *py;
        m_trans_map.get(ax, ex, px);
        m_trans_map.get(ay, ey, py);

        expr_ref deq(m);

        if (m_converter.fu().is_float(m.get_sort(get_enode(x)->get_owner()))) {
            expr * sgn_x, *sig_x, *exp_x;
            expr * sgn_y, *sig_y, *exp_y;
            split_triple(ex, sgn_x, sig_x, exp_x);
            split_triple(ex, sgn_y, sig_y, exp_y);
            
            deq = m.mk_or(m.mk_not(m.mk_eq(sgn_x, sgn_y)),
                          m.mk_not(m.mk_eq(sig_x, sig_y)),
                          m.mk_not(m.mk_eq(exp_x, exp_y)));            
        } 
        else if (m_converter.fu().is_rm(m.get_sort(get_enode(x)->get_owner()))) {
            deq = m.mk_not(m.mk_eq(ex, ey));            
        }
        else
            UNREACHABLE();
        
        ctx.internalize(deq, true);
        ctx.mk_th_axiom(get_id(), 1, &ctx.get_literal(deq));
        ctx.mark_as_relevant(deq);
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
        sort * fpa_e_srt = m.get_sort(fpa_e);
        expr_wrapper_proc * res = 0;

        if (fu.is_rm(fpa_e_srt)) {
            SASSERT(ctx.e_internalized(bv_e));
            sort * s = m.get_sort(bv_e);
            family_id fid = s->get_family_id();
            theory_bv * bv_th = (theory_bv*)ctx.get_theory(fid);
            rational val;
            if (!bv_th->get_fixed_value(ctx.get_enode(bv_e)->get_owner(), val)) {
                UNREACHABLE();
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
        else if (fu.is_float(fpa_e_srt)) {
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
                UNREACHABLE();
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
        else
            UNREACHABLE();

        return res;
    }

    void theory_fpa::assign_eh(bool_var v, bool is_true) {
        TRACE("t_fpa", tout << "assign_eh for: " << v << " (" << is_true << ")\n";);
        /* CMW: okay to ignore? */
    }

    void theory_fpa::relevant_eh(app * n) {
        TRACE("t_fpa", tout << "relevant_eh for: " << mk_ismt2_pp(n, get_manager()) << "\n";);
        ast_manager & m = get_manager();
        context & ctx = get_context();
        float_util & fu = m_converter.fu();
        bv_util & bu = m_converter.bu();

        if (m.is_bool(n)) {
            bool_var v = ctx.get_bool_var(n);
            atom * a = get_bv2a(v);
            pred_atom * pa = static_cast<pred_atom*>(a);
            ctx.mark_as_relevant(pa->m_def);            
            ctx.mk_th_axiom(get_id(), pa->m_var, ~pa->m_def);
            ctx.mk_th_axiom(get_id(), ~pa->m_var, pa->m_def);
        }
        else if (ctx.e_internalized(n)) {
            SASSERT(m_trans_map.contains(n));
            expr * ex;
            proof * px;
            m_trans_map.get(n, ex, px);
            sort * n_srt = m.get_sort(n);

            if (fu.is_rm(n_srt)) {
                ctx.mark_as_relevant(ex);                
            }
            else if (fu.is_float(n_srt)) {
                expr * bv_sgn, *bv_sig, *bv_exp;
                split_triple(ex, bv_sgn, bv_sig, bv_exp);

                ctx.mark_as_relevant(bv_sgn);
                ctx.mark_as_relevant(bv_sig);
                ctx.mark_as_relevant(bv_exp);
            }
            else if (n->get_decl()->get_decl_kind() == OP_TO_IEEE_BV) {                
                literal l = mk_eq(n, ex, false);
                ctx.mark_as_relevant(l);
                ctx.mk_th_axiom(get_id(), 1, &l);
            }
            else
                NOT_IMPLEMENTED_YET();
        }
        else
            UNREACHABLE();
    }

    void theory_fpa::reset_eh() {
        pop_scope_eh(m_trail_stack.get_num_scopes());
        m_bool_var2atom.reset();  
        theory::reset_eh();
    }
};
