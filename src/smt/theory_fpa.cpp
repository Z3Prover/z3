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
#include "ast/ast_smt2_pp.h"
#include "smt/smt_context.h"
#include "smt/theory_fpa.h"
#include "smt/theory_bv.h"
#include "smt/smt_model_generator.h"
#include "ast/fpa/bv2fpa_converter.h"

namespace smt {

    theory_fpa::theory_fpa(context& ctx) :
        theory(ctx, ctx.get_manager().mk_family_id("fpa")),
        m_th_rw(ctx.get_manager()),
        m_converter(ctx.get_manager(), m_th_rw),
        m_rw(ctx.get_manager(), m_converter, params_ref()),
        m_trail_stack(),
        m_fpa_util(m_converter.fu()),
        m_bv_util(m_converter.bu()),
        m_arith_util(m_converter.au()),
        m_is_initialized(true)
    {
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_th_rw.updt_params(p);        
    }

    theory_fpa::~theory_fpa()
    {
        m_trail_stack.reset();

        if (m_is_initialized) {
            dec_ref_map_key_values(m, m_conversions);
            dec_ref_collection_values(m, m_is_added_to_model);

            m_converter.reset();
            m_rw.reset();
            m_th_rw.reset();
            m_is_initialized = false;
        }

        SASSERT(m_trail_stack.get_num_scopes() == 0);
        SASSERT(m_conversions.empty());
        SASSERT(m_is_added_to_model.empty());
    }

    app * theory_fpa::fpa_value_proc::mk_value(model_generator & mg, expr_ref_vector const & values) {
        TRACE("t_fpa_detail",
              ast_manager & m = m_th.get_manager();
              for (unsigned i = 0; i < values.size(); i++)
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

            VERIFY(m_bu.is_numeral(values[0], all_r, bv_sz));
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
            (void)r;

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
        mpfm.set(f, m_ebits, m_sbits, mpzm.is_one(sgn_z), mpzm.get_int64(exp_u), sig_z);
        result = m_fu.mk_value(f);

        TRACE("t_fpa", tout << "result: [" <<
                       mpzm.to_string(sgn_z) << "," <<
                       mpzm.to_string(exp_z) << "," <<
                       mpzm.to_string(sig_z) << "] --> " <<
                       mk_ismt2_pp(result, m_th.get_manager()) << std::endl;);

        return result;
    }

    app * theory_fpa::fpa_rm_value_proc::mk_value(model_generator & mg, expr_ref_vector const & values) {
        SASSERT(values.size() == 1);

        TRACE("t_fpa_detail",
              ast_manager & m = m_th.get_manager();
              for (unsigned i = 0; i < values.size(); i++)
              tout << "value[" << i << "] = " << mk_ismt2_pp(values[i], m) << std::endl;);

        app * result = nullptr;
        unsigned bv_sz;

        rational val(0);
        VERIFY(m_bu.is_numeral(values[0], val, bv_sz));
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

        TRACE("t_fpa", tout << "result: " << mk_ismt2_pp(result, m_th.get_manager()) << std::endl;);

        return result;
    }


    expr_ref theory_fpa::convert(expr * e)
    {
        expr_ref res(m);
        expr * ccnv;
        TRACE("t_fpa", tout << "converting " << mk_ismt2_pp(e, m) << std::endl;);

        if (m_conversions.find(e, ccnv)) {
            res = ccnv;
            TRACE("t_fpa_detail", tout << "cached:" << std::endl;
            tout << mk_ismt2_pp(e, m) << std::endl << " -> " << std::endl <<
                mk_ismt2_pp(res, m) << std::endl;);
        }
        else {
            res = m_rw.convert(m_th_rw, e);

            TRACE("t_fpa_detail", tout << "converted; caching:" << std::endl;
                                  tout << mk_ismt2_pp(e, m) << std::endl << " -> " << std::endl <<
                                          mk_ismt2_pp(res, m) << std::endl;);

            m_conversions.insert(e, res);
            m.inc_ref(e);
            m.inc_ref(res);
            m_trail_stack.push(insert_ref2_map<ast_manager, expr, expr>(m, m_conversions, e, res.get()));
        }

        return res;
    }

    expr_ref theory_fpa::mk_side_conditions()
    {

        expr_ref res(m), t(m);
        expr_ref_vector fmls(m);
        proof_ref t_pr(m);

        for (expr* arg : m_converter.m_extra_assertions) {
            ctx.get_rewriter()(arg, t, t_pr);
            fmls.push_back(std::move(t));
        }
        m_converter.m_extra_assertions.reset();
        res = m.mk_and(fmls);

        m_th_rw(res);

        CTRACE("t_fpa", !m.is_true(res), tout << "side condition: " << mk_ismt2_pp(res, m) << std::endl;);
        return res;
    }

    void theory_fpa::assert_cnstr(expr * e) {
        if (m.is_true(e)) return;
        TRACE("t_fpa_detail", tout << "asserting " << mk_ismt2_pp(e, m) << "\n";);
        if (m.has_trace_stream()) log_axiom_instantiation(e);
        ctx.internalize(e, false);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        literal lit(ctx.get_literal(e));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }

    void theory_fpa::attach_new_th_var(enode * n) {
        theory_var v = mk_var(n);
        ctx.attach_th_var(n, this, v);
        TRACE("t_fpa", tout << "new theory var: " << mk_ismt2_pp(n->get_expr(), m) << " := " << v << "\n";);
    }

    bool theory_fpa::internalize_atom(app * atom, bool gate_ctx) {
        TRACE("t_fpa_internalize", tout << "internalizing atom: " << mk_ismt2_pp(atom, m) << std::endl;);
        SASSERT(atom->get_family_id() == get_family_id());

        if (ctx.b_internalized(atom))
            return true;

        ctx.internalize(atom->get_args(), atom->get_num_args(), false);

        literal l(ctx.mk_bool_var(atom));
        ctx.set_var_theory(l.var(), get_id());

        expr_ref bv_atom(m_rw.convert_atom(m_th_rw, atom));
        expr_ref bv_atom_w_side_c(m), atom_eq(m);
        bv_atom_w_side_c = m.mk_and(bv_atom, mk_side_conditions());
        m_th_rw(bv_atom_w_side_c);
        atom_eq = m.mk_eq(atom, bv_atom_w_side_c);
        assert_cnstr(atom_eq);
        return true;
    }

    bool theory_fpa::internalize_term(app * term) {
        TRACE("t_fpa_internalize", tout << "internalizing term: " << mk_ismt2_pp(term, m) << "\n";);
        SASSERT(term->get_family_id() == get_family_id());
        SASSERT(!ctx.e_internalized(term));

        ctx.internalize(term->get_args(), term->get_num_args(), false);

        enode * e = (ctx.e_internalized(term)) ? ctx.get_enode(term) :
                                                 ctx.mk_enode(term, false, false, true);

        if (!is_attached_to_var(e)) {
            attach_new_th_var(e);

            // The conversion operators fp.to_* appear in non-FP constraints.
            // The corresponding constraints will not be translated and added
            // via convert(...) and assert_cnstr(...) in initialize_atom(...).
            // Therefore, we translate and assert them here.
            fpa_op_kind k = (fpa_op_kind)term->get_decl_kind();
            switch (k) {
            case OP_FPA_TO_FP:
            case OP_FPA_TO_UBV:
            case OP_FPA_TO_SBV:
            case OP_FPA_TO_REAL:
            case OP_FPA_TO_IEEE_BV: {
                expr_ref conv = convert(term);
                expr_ref eq(m.mk_eq(term, conv), m);
                assert_cnstr(eq);
                assert_cnstr(mk_side_conditions());
                break;
            }
            default: /* ignore */;
            }
        }

        return true;
    }

    void theory_fpa::apply_sort_cnstr(enode * n, sort * s) {
        TRACE("t_fpa", tout << "apply sort cnstr for: " << mk_ismt2_pp(n->get_expr(), m) << "\n";);
        SASSERT(s->get_family_id() == get_family_id());
        SASSERT(m_fpa_util.is_float(s) || m_fpa_util.is_rm(s));
        SASSERT(m_fpa_util.is_float(n->get_expr()) || m_fpa_util.is_rm(n->get_expr()));
        SASSERT(n->get_expr()->get_decl()->get_range() == s);

        app * owner = n->get_expr();

        if (!is_attached_to_var(n)) {
            attach_new_th_var(n);

            if (m_fpa_util.is_rm(s)) {
                // For every RM term, we need to make sure that it's
                // associated bit-vector is within the valid range.
                if (!m_fpa_util.is_bv2rm(owner)) {
                    expr_ref valid(m), limit(m);
                    limit = m_bv_util.mk_numeral(4, 3);
                    valid = m_bv_util.mk_ule(m_converter.wrap(owner), limit);
                    assert_cnstr(valid);
                }
            }

            if (!ctx.relevancy())
                relevant_eh(owner);
        }
    }

    void theory_fpa::new_eq_eh(theory_var x, theory_var y) {
        enode * e_x = get_enode(x);
        enode * e_y = get_enode(y);

        TRACE("t_fpa", tout << "new eq: " << x << " = " << y << std::endl;
                       tout << mk_ismt2_pp(e_x->get_expr(), m) << std::endl << " = " << std::endl <<
                               mk_ismt2_pp(e_y->get_expr(), m) << std::endl;);

        fpa_util & fu = m_fpa_util;

        expr * xe = e_x->get_expr();
        expr * ye = e_y->get_expr();

        if (m_fpa_util.is_bvwrap(xe) || m_fpa_util.is_bvwrap(ye))
            return;

        expr_ref xc = convert(xe);
        expr_ref yc = convert(ye);

        TRACE("t_fpa_detail", tout << "xc = " << mk_ismt2_pp(xc, m) << std::endl <<
                                      "yc = " << mk_ismt2_pp(yc, m) << std::endl;);

        expr_ref c(m);

        if ((fu.is_float(xe) && fu.is_float(ye)) ||
            (fu.is_rm(xe) && fu.is_rm(ye)))
            m_converter.mk_eq(xc, yc, c);
        else
            c = m.mk_eq(xc, yc);

        m_th_rw(c);

        expr_ref xe_eq_ye(m), c_eq_iff(m);
        xe_eq_ye = m.mk_eq(xe, ye);
        c_eq_iff = m.mk_iff(xe_eq_ye, c);
        assert_cnstr(c_eq_iff);
        assert_cnstr(mk_side_conditions());
    }

    void theory_fpa::new_diseq_eh(theory_var x, theory_var y) {
        enode * e_x = get_enode(x);
        enode * e_y = get_enode(y);

        TRACE("t_fpa", tout << "new diseq: " << x << " != " << y << std::endl;
                       tout << mk_ismt2_pp(e_x->get_expr(), m) << std::endl << " != " << std::endl <<
                           mk_ismt2_pp(e_y->get_expr(), m) << std::endl;);

        fpa_util & fu = m_fpa_util;

        expr * xe = e_x->get_expr();
        expr * ye = e_y->get_expr();

        if (m_fpa_util.is_bvwrap(xe) || m_fpa_util.is_bvwrap(ye))
            return;

        expr_ref xc = convert(xe);
        expr_ref yc = convert(ye);

        expr_ref c(m);

        if ((fu.is_float(xe) && fu.is_float(ye))||
            (fu.is_rm(xe) && fu.is_rm(ye))) {
            m_converter.mk_eq(xc, yc, c);
            c = m.mk_not(c);
        }
        else {
            expr_ref xc_eq_yc(m);
            xc_eq_yc = m.mk_eq(xc, yc);
            c = m.mk_not(xc_eq_yc);
        }

        m_th_rw(c);

        expr_ref xe_eq_ye(m), not_xe_eq_ye(m), c_eq_iff(m);
        xe_eq_ye = m.mk_eq(xe, ye);
        not_xe_eq_ye = m.mk_not(xe_eq_ye);
        c_eq_iff = m.mk_iff(not_xe_eq_ye, c);
        assert_cnstr(c_eq_iff);
        assert_cnstr(mk_side_conditions());
    }

    theory* theory_fpa::mk_fresh(context* new_ctx) {
        return alloc(theory_fpa, *new_ctx);
    }

    void theory_fpa::push_scope_eh() {
        theory::push_scope_eh();
        m_trail_stack.push_scope();
    }

    void theory_fpa::pop_scope_eh(unsigned num_scopes) {
        m_trail_stack.pop_scope(num_scopes);
        TRACE("t_fpa", tout << "pop " << num_scopes << "; now " << m_trail_stack.get_num_scopes() << "\n";);
        theory::pop_scope_eh(num_scopes);
    }

    void theory_fpa::assign_eh(bool_var v, bool is_true) {
        expr * e = ctx.bool_var2expr(v);

        TRACE("t_fpa", tout << "assign_eh for: " << v << " (" << is_true << "):\n" << mk_ismt2_pp(e, m) << "\n";);

        expr_ref converted = convert(e);
        converted = m.mk_and(converted, mk_side_conditions());

        expr_ref cnstr(m);
        cnstr = (is_true) ? m.mk_implies(e, converted) : m.mk_implies(converted, e);
        m_th_rw(cnstr);
        assert_cnstr(cnstr);
    }

    void theory_fpa::relevant_eh(app * n) {
        TRACE("t_fpa", tout << "relevant_eh for: " << mk_ismt2_pp(n, m) << "\n";);

        mpf_manager & mpfm = m_fpa_util.fm();

        if (m_fpa_util.is_float(n) || m_fpa_util.is_rm(n)) {
            if (!m_fpa_util.is_fp(n)) {
                expr_ref wrapped(m), c(m);
                wrapped = m_converter.wrap(n);
                mpf_rounding_mode rm;
                scoped_mpf val(mpfm);
                if (m_fpa_util.is_rm_numeral(n, rm)) {
                    expr_ref rm_num(m);
                    rm_num = m_bv_util.mk_numeral(rm, 3);
                    c = m.mk_eq(wrapped, rm_num);
                    assert_cnstr(c);
                }
                else if (m_fpa_util.is_numeral(n, val)) {
                    expr_ref bv_val_e(m), cc_args(m);
                    bv_val_e = convert(n);
                    SASSERT(is_app(bv_val_e));
                    SASSERT(to_app(bv_val_e)->get_num_args() == 3);
                    app_ref bv_val_a(m);
                    bv_val_a = to_app(bv_val_e.get());
                    expr * args[] = { bv_val_a->get_arg(0), bv_val_a->get_arg(1), bv_val_a->get_arg(2) };
                    cc_args = m_bv_util.mk_concat(3, args);
                    c = m.mk_eq(wrapped, cc_args);
                    assert_cnstr(c);
                    assert_cnstr(mk_side_conditions());
                }
                else {
                    expr_ref wu(m);
                    wu = m.mk_eq(m_converter.unwrap(wrapped, n->get_sort()), n);
                    TRACE("t_fpa", tout << "w/u eq: " << std::endl << mk_ismt2_pp(wu, m) << std::endl;);
                    assert_cnstr(wu);
                }
            }
        }
        else if (n->get_family_id() == get_family_id()) {
            // These are the conversion functions fp.to_* */
            SASSERT(!m_fpa_util.is_float(n) && !m_fpa_util.is_rm(n));
        }
        else {
            /* Theory variables can be merged when (= bv-term (bvwrap fp-term)),
               in which case context::relevant_eh may call theory_fpa::relevant_eh
               after theory_bv::relevant_eh, regardless of whether theory_fpa is
               interested in this term. But, this can only happen because of
               (bvwrap ...) terms, i.e., `n' must be a bit-vector expression,
               which we can safely ignore. */
            SASSERT(m_bv_util.is_bv(n));
        }
    }

    void theory_fpa::reset_eh() {
        TRACE("t_fpa", tout << "reset_eh\n";);
        pop_scope_eh(m_trail_stack.get_num_scopes());
        m_converter.reset();
        m_rw.reset();
        m_th_rw.reset();
        m_trail_stack.pop_scope(m_trail_stack.get_num_scopes());
        if (m_factory) {
            dealloc(m_factory);
            m_factory = nullptr;
        }
        dec_ref_map_key_values(m, m_conversions);
        dec_ref_collection_values(m, m_is_added_to_model);
        theory::reset_eh();
    }

    final_check_status theory_fpa::final_check_eh() {
        TRACE("t_fpa", tout << "final_check_eh\n";);
        SASSERT(m_converter.m_extra_assertions.empty());
        return FC_DONE;
    }

    void theory_fpa::init_model(model_generator & mg) {
        TRACE("t_fpa", tout << "initializing model" << std::endl; display(tout););
        m_factory = alloc(fpa_value_factory, m, get_family_id());
        mg.register_factory(m_factory);
    }

    enode* theory_fpa::ensure_enode(expr* e) {
        ctx.ensure_internalized(e);
        enode* n = ctx.get_enode(e);
        ctx.mark_as_relevant(n);
        return n;
    }

    app* theory_fpa::get_ite_value(expr* e) {
        expr* e1, *e2, *e3;
        while (m.is_ite(e, e1, e2, e3) && ctx.e_internalized(e)) {
            if (ctx.get_enode(e2)->get_root() == ctx.get_enode(e)->get_root()) {
                e = e2;
            }
            else if (ctx.get_enode(e3)->get_root() == ctx.get_enode(e)->get_root()) {
                e = e3;
            }
            else {
                break;
            }
        }
        return to_app(e);
    }

    model_value_proc * theory_fpa::mk_value(enode * n, model_generator & mg) {
        TRACE("t_fpa", tout << "mk_value for: " << mk_ismt2_pp(n->get_expr(), m) <<
                            " (sort " << mk_ismt2_pp(n->get_expr()->get_sort(), m) << ")\n";);

        app_ref owner(m);
        owner = get_ite_value(n->get_expr());

        // If the owner is not internalized, it doesn't have an enode associated.
        SASSERT(ctx.e_internalized(owner));

        if (m_fpa_util.is_rm_numeral(owner) ||
            m_fpa_util.is_numeral(owner)) {
            return alloc(expr_wrapper_proc, owner);
        }

        model_value_proc * res = nullptr;

        app_ref wrapped(m);
        wrapped = m_converter.wrap(owner);
        SASSERT(m_bv_util.is_bv(wrapped));

        CTRACE("t_fpa_detail", !ctx.e_internalized(wrapped),
                tout << "Model dependency not internalized: " <<
                mk_ismt2_pp(wrapped, m) <<
                " (owner " << (!ctx.e_internalized(owner) ? "not" : "is") <<
                " internalized)" << std::endl;);

        if (m_fpa_util.is_fp(owner)) {
            SASSERT(to_app(owner)->get_num_args() == 3);
            app_ref a0(m), a1(m), a2(m);
            a0 = to_app(owner->get_arg(0));
            a1 = to_app(owner->get_arg(1));
            a2 = to_app(owner->get_arg(2));
            unsigned ebits = m_fpa_util.get_ebits(owner->get_sort());
            unsigned sbits = m_fpa_util.get_sbits(owner->get_sort());
            fpa_value_proc * vp = alloc(fpa_value_proc, this, ebits, sbits);
            vp->add_dependency(ctx.get_enode(a0));
            vp->add_dependency(ctx.get_enode(a1));
            vp->add_dependency(ctx.get_enode(a2));
            TRACE("t_fpa_detail", tout << "Depends on: " <<
                  mk_ismt2_pp(a0, m) << " eq. cls. #" << get_enode(a0)->get_root()->get_expr()->get_id() << std::endl <<
                  mk_ismt2_pp(a1, m) << " eq. cls. #" << get_enode(a1)->get_root()->get_expr()->get_id() << std::endl <<
                  mk_ismt2_pp(a2, m) << " eq. cls. #" << get_enode(a2)->get_root()->get_expr()->get_id() << std::endl;);
            res = vp;
        }
        else if (m_fpa_util.is_bv2rm(owner)) {
            SASSERT(to_app(owner)->get_num_args() == 1);
            app_ref a0(m);
            a0 = to_app(owner->get_arg(0));
            fpa_rm_value_proc * vp = alloc(fpa_rm_value_proc, this);
            vp->add_dependency(ctx.get_enode(a0));
            TRACE("t_fpa_detail", tout << "Depends on: " <<
                mk_ismt2_pp(a0, m) << " eq. cls. #" << get_enode(a0)->get_root()->get_expr()->get_id() << std::endl;);
            res = vp;
        }
        else if (ctx.e_internalized(wrapped)) {
            if (m_fpa_util.is_rm(owner)) {
                fpa_rm_value_proc * vp = alloc(fpa_rm_value_proc, this);
                vp->add_dependency(ctx.get_enode(wrapped));
                res = vp;
            }
            else if (m_fpa_util.is_float(owner)) {
                unsigned ebits = m_fpa_util.get_ebits(owner->get_sort());
                unsigned sbits = m_fpa_util.get_sbits(owner->get_sort());
                fpa_value_proc * vp = alloc(fpa_value_proc, this, ebits, sbits);
                enode * en = ctx.get_enode(wrapped);
                vp->add_dependency(en);
                TRACE("t_fpa_detail", tout << "Depends on: " << mk_ismt2_pp(wrapped, m) << " eq. cls. #" << en->get_root()->get_expr()->get_id() << std::endl;);
                res = vp;
            }
        }
        else {
            unsigned ebits = m_fpa_util.get_ebits(owner->get_sort());
            unsigned sbits = m_fpa_util.get_sbits(owner->get_sort());
            return alloc(expr_wrapper_proc, m_fpa_util.mk_pzero(ebits, sbits));
        }

        SASSERT(res != 0);
        return res;
    }

    void theory_fpa::finalize_model(model_generator & mg) {
        proto_model & mdl = mg.get_model();
        proto_model new_model(m);

        bv2fpa_converter bv2fp(m, m_converter);

        obj_hashtable<func_decl> seen;
        bv2fp.convert_min_max_specials(&mdl, &new_model, seen);
        bv2fp.convert_uf2bvuf(&mdl, &new_model, seen);

        for (func_decl* f : seen) 
            mdl.unregister_decl(f);

        for (unsigned i = 0; i < new_model.get_num_constants(); i++) {
            func_decl * f = new_model.get_constant(i);
            mdl.register_decl(f, new_model.get_const_interp(f));
        }

        for (unsigned i = 0; i < new_model.get_num_functions(); i++) {
            func_decl * f = new_model.get_function(i);
            func_interp * fi = new_model.get_func_interp(f)->copy();
            mdl.register_decl(f, fi);
        }
    }

    void theory_fpa::display(std::ostream & out) const
    {

        bool first = true;
        for (enode* n : ctx.enodes()) {
            theory_var v = n->get_th_var(get_family_id());
            if (v != -1) {
                if (first) out << "fpa theory variables:" << std::endl;
                out << v << " -> " <<
                    mk_ismt2_pp(n->get_expr(), m) << std::endl;
                first = false;
            }
        }
        // if there are no fpa theory variables, was fp ever used?
        if (first) return;

        out << "bv theory variables:" << std::endl;
        for (enode * n : ctx.enodes()) {
            theory_var v = n->get_th_var(m_bv_util.get_family_id());
            if (v != -1) out << v << " -> " <<
                mk_ismt2_pp(n->get_expr(), m) << std::endl;
        }

        out << "arith theory variables:" << std::endl;
        for (enode* n : ctx.enodes()) {
            theory_var v = n->get_th_var(m_arith_util.get_family_id());
            if (v != -1) out << v << " -> " <<
                mk_ismt2_pp(n->get_expr(), m) << std::endl;
        }

        out << "equivalence classes:\n";
        for (enode * n : ctx.enodes()) {
            expr * e = n->get_expr();
            expr * r = n->get_root()->get_expr();
            out << r->get_id() << " --> " << mk_ismt2_pp(e, m) << std::endl;
        }
    }
};
