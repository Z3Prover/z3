/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    fpa_solver.cpp

Abstract:

    Floating-Point Theory Plugin

Author:

    Christoph (cwinter) 2014-04-23

Revision History:

--*/

#include "sat/smt/fpa_solver.h"

namespace fpa {

    solver::solver(euf::solver& ctx) :
        euf::th_euf_solver(ctx, ctx.get_manager().mk_family_id("fpa")),
        m_th_rw(ctx.get_manager()),
        m_converter(ctx.get_manager(), m_th_rw),
        m_rw(ctx.get_manager(), m_converter, params_ref()),    
        m_fpa_util(m_converter.fu()),
        m_bv_util(m_converter.bu()),
        m_arith_util(m_converter.au())
    {
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_th_rw.updt_params(p);        
    }

    solver::~solver() {
        dec_ref_map_key_values(m, m_conversions);
        dec_ref_collection_values(m, m_is_added_to_model);                
        SASSERT(m_conversions.empty());
        SASSERT(m_is_added_to_model.empty());
    }


    expr_ref solver::convert(expr* e)
    {
        expr_ref res(m);
        expr* ccnv;
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

            // ctx.push(fpa2bv_conversion_trail_elem(m, m_conversions, e));
        }
        return res;
    }

    sat::literal_vector solver::mk_side_conditions() {
        sat::literal_vector conds;
        expr_ref t(m);
        for (expr* arg : m_converter.m_extra_assertions) {
            ctx.get_rewriter()(arg, t);
            m_th_rw(t);
            conds.push_back(b_internalize(t));
        }
        m_converter.m_extra_assertions.reset();
        return conds;
    }

    void solver::attach_new_th_var(enode * n) {
        theory_var v = mk_var(n);
        ctx.attach_th_var(n, this, v);
        TRACE("t_fpa", tout << "new theory var: " << mk_ismt2_pp(n->get_expr(), m) << " := " << v << "\n";);
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool redundant) {
        SASSERT(m.is_bool(e));
        if (!visit_rec(m, e, sign, root, redundant))
            return sat::null_literal;
        return expr2literal(e);
    }

    void solver::internalize(expr* e, bool redundant) {
        visit_rec(m, e, false, false, redundant);
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());
    }

    bool solver::visit(expr* e) {
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e, m_is_redundant);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        app* a = to_app(e);
        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n)
            n = mk_enode(e, false);
        SASSERT(!n->is_attached_to(get_id()));
        mk_var(n);
        if (m.is_bool(e)) {
            sat::literal atom(ctx.get_si().add_bool_var(e), false);
            atom = ctx.attach_lit(atom, e);
            sat::literal bv_atom = b_internalize(m_rw.convert_atom(m_th_rw, e));
            sat::literal_vector conds = mk_side_conditions();     
            conds.push_back(bv_atom);
            add_equiv_and(atom, conds);
            if (root) {
                if (sign)
                    atom.neg();
                add_unit(atom);
            }
            return true;
        }

        switch (a->get_decl_kind()) {
            case OP_FPA_TO_FP:
            case OP_FPA_TO_UBV:
            case OP_FPA_TO_SBV:
            case OP_FPA_TO_REAL:
            case OP_FPA_TO_IEEE_BV: {
                expr_ref conv = convert(e);
                expr_ref eq = ctx.mk_eq(e, conv); 
                add_unit(b_internalize(eq));
                add_units(mk_side_conditions());
                break;
            }
            default: /* ignore */;
        }
        return true;
    }

    void solver::apply_sort_cnstr(enode * n, sort * s) {
        TRACE("t_fpa", tout << "apply sort cnstr for: " << mk_ismt2_pp(n->get_expr(), m) << "\n";);
        SASSERT(s->get_family_id() == get_id());
        SASSERT(m_fpa_util.is_float(s) || m_fpa_util.is_rm(s));
        SASSERT(m_fpa_util.is_float(n->get_expr()) || m_fpa_util.is_rm(n->get_expr()));
        SASSERT(n->get_expr()->get_decl()->get_range() == s);

        expr * owner = n->get_expr();

        if (is_attached_to_var(n))
            return;
        attach_new_th_var(n);

        if (m_fpa_util.is_rm(s)) {
            // For every RM term, we need to make sure that it's
            // associated bit-vector is within the valid range.
            if (!m_fpa_util.is_bv2rm(owner)) {
                expr_ref valid(m), limit(m);
                limit = m_bv_util.mk_numeral(4, 3);
                valid = m_bv_util.mk_ule(m_converter.wrap(owner), limit);
                add_unit(b_internalize(valid));
            }
        }
        activate(owner);
    }

    void solver::activate(expr* n) {
        TRACE("t_fpa", tout << "relevant_eh for: " << mk_ismt2_pp(n, m) << "\n";);

        mpf_manager& mpfm = m_fpa_util.fm();

        if (m_fpa_util.is_float(n) || m_fpa_util.is_rm(n)) {
            if (!m_fpa_util.is_fp(n)) {
                app_ref wrapped = m_converter.wrap(n);
                mpf_rounding_mode rm;
                scoped_mpf val(mpfm);
                if (m_fpa_util.is_rm_numeral(n, rm)) {
                    expr_ref rm_num(m);
                    rm_num = m_bv_util.mk_numeral(rm, 3);
                    add_unit(b_internalize(ctx.mk_eq(wrapped, rm_num)));
                }
                else if (m_fpa_util.is_numeral(n, val)) {
                    expr_ref bv_val_e(m), cc_args(m);
                    bv_val_e = convert(n);
                    SASSERT(is_app(bv_val_e));
                    SASSERT(to_app(bv_val_e)->get_num_args() == 3);
                    app_ref bv_val_a(m);
                    bv_val_a = to_app(bv_val_e.get());
                    expr* args[] = { bv_val_a->get_arg(0), bv_val_a->get_arg(1), bv_val_a->get_arg(2) };
                    cc_args = m_bv_util.mk_concat(3, args);
                    add_unit(b_internalize(ctx.mk_eq(wrapped, cc_args)));
                    add_units(mk_side_conditions());
                }
                else {
                    expr_ref wu = ctx.mk_eq(m_converter.unwrap(wrapped, m.get_sort(n)), n);
                    TRACE("t_fpa", tout << "w/u eq: " << std::endl << mk_ismt2_pp(wu, m) << std::endl;);
                    add_unit(b_internalize(wu));
                }
            }
        }
        else if (is_app(n) && to_app(n)->get_family_id() == get_id()) {
            // These are the conversion functions fp.to_* */
            SASSERT(!m_fpa_util.is_float(n) && !m_fpa_util.is_rm(n));
        }
        else {
            /* Theory variables can be merged when (= bv-term (bvwrap fp-term)),
               in which case context::relevant_eh may call solver::relevant_eh
               after theory_bv::relevant_eh, regardless of whether solver is
               interested in this term. But, this can only happen because of
               (bvwrap ...) terms, i.e., `n' must be a bit-vector expression,
               which we can safely ignore. */
            SASSERT(m_bv_util.is_bv(n));
        }
    }

    void solver::ensure_equality_relation(theory_var x, theory_var y) {
        enode* e_x = var2enode(x);
        enode* e_y = var2enode(y);

        TRACE("t_fpa", tout << "new eq: " << x << " = " << y << std::endl;
        tout << mk_ismt2_pp(e_x->get_expr(), m) << std::endl << " = " << std::endl <<
            mk_ismt2_pp(e_y->get_expr(), m) << std::endl;);

        fpa_util& fu = m_fpa_util;

        expr* xe = e_x->get_expr();
        expr* ye = e_y->get_expr();

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

        sat::literal eq1 = b_internalize(ctx.mk_eq(e_x, e_y));
        sat::literal eq2 = b_internalize(c);
        add_equiv(eq1, eq2);
        add_units(mk_side_conditions());
    }

    void solver::new_eq_eh(euf::th_eq const& eq) {
        ensure_equality_relation(eq.v1(), eq.v2());
    }

    void solver::new_diseq_eh(euf::th_eq const& eq) {
        ensure_equality_relation(eq.v1(), eq.v2());
    }

    void solver::asserted(sat::literal l) {
        expr* e = ctx.bool_var2expr(l.var());

        TRACE("t_fpa", tout << "assign_eh for: " << v << " (" << is_true << "):\n" << mk_ismt2_pp(e, m) << "\n";);

        sat::literal c = b_internalize(convert(e));
        sat::literal_vector conds = mk_side_conditions();
        conds.push_back(c);
        if (l.sign()) {
            for (sat::literal sc : conds)
                add_clause(l, sc);
        }
        else {
            for (auto& sc : conds)
                sc.neg();
            conds.push_back(l);
            add_clause(conds);
        }
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        expr* e = n->get_expr();
        app_ref wrapped(m);
        expr_ref value(m);
        auto is_wrapped = [&]() {
            if (!wrapped) wrapped = m_converter.wrap(e);
            return expr2enode(wrapped) != nullptr;
        };
        if (m_fpa_util.is_fp(e)) {
            SASSERT(n->num_args() == 3);
            expr* a = values.get(n->get_arg(0)->get_root_id());
            expr* b = values.get(n->get_arg(1)->get_root_id());
            expr* c = values.get(n->get_arg(2)->get_root_id());
            value = bvs2fpa_value(m.get_sort(e), a, b, c);
        }
        else if (m_fpa_util.is_bv2rm(e)) {
            SASSERT(n->num_args() == 1);
            value = bv2rm_value(values.get(n->get_arg(0)->get_root_id()));
        }
        else if (m_fpa_util.is_rm(e) && is_wrapped()) 
            value = bv2rm_value(values.get(expr2enode(wrapped)->get_root_id()));        
        else if (m_fpa_util.is_float(e) && is_wrapped()) 
            value = bvs2fpa_value(m.get_sort(e), expr2enode(wrapped), nullptr, nullptr);        
        else {
            unsigned ebits = m_fpa_util.get_ebits(m.get_sort(e));
            unsigned sbits = m_fpa_util.get_sbits(m.get_sort(e));
            value = m_fpa_util.mk_pzero(ebits, sbits);
        }
        values.set(n->get_root_id(), value);
    }

    expr* solver::bv2rm_value(expr* b) {
        app* result = nullptr;
        unsigned bv_sz;
        rational val(0);
        VERIFY(m_bv_util.is_numeral(b, val, bv_sz));
        SASSERT(bv_sz == 3);

        switch (val.get_uint64()) {        
        case BV_RM_TIES_TO_AWAY: result = m_fpa_util.mk_round_nearest_ties_to_away(); break;
        case BV_RM_TIES_TO_EVEN: result = m_fpa_util.mk_round_nearest_ties_to_even(); break;
        case BV_RM_TO_NEGATIVE: result = m_fpa_util.mk_round_toward_negative(); break;
        case BV_RM_TO_POSITIVE: result = m_fpa_util.mk_round_toward_positive(); break;
        case BV_RM_TO_ZERO:
        default: result = m_fpa_util.mk_round_toward_zero();
        }

        TRACE("t_fpa", tout << "result: " << mk_ismt2_pp(result, m) << std::endl;);
        return result;
    }


    expr* solver::bvs2fpa_value(sort* s, expr* a, expr* b, expr* c) {
        mpf_manager& mpfm = m_fpa_util.fm();
        unsynch_mpz_manager& mpzm = mpfm.mpz_manager();
        app* result;
        unsigned ebits = m_fpa_util.get_ebits(s);
        unsigned sbits = m_fpa_util.get_sbits(s);

        scoped_mpz bias(mpzm);
        mpzm.power(mpz(2), ebits - 1, bias);
        mpzm.dec(bias);

        scoped_mpz sgn_z(mpzm), sig_z(mpzm), exp_z(mpzm);
        unsigned bv_sz;

        if (b == nullptr) {
            SASSERT(m_bv_util.is_bv(a));
            SASSERT(m_bv_util.get_bv_size(a) == (ebits + sbits));

            rational all_r(0);
            scoped_mpz all_z(mpzm);

            VERIFY(m_bv_util.is_numeral(a, all_r, bv_sz));
            SASSERT(bv_sz == (ebits + sbits));
            SASSERT(all_r.is_int());
            mpzm.set(all_z, all_r.to_mpq().numerator());

            mpzm.machine_div2k(all_z, ebits + sbits - 1, sgn_z);
            mpzm.mod(all_z, mpfm.m_powers2(ebits + sbits - 1), all_z);

            mpzm.machine_div2k(all_z, sbits - 1, exp_z);
            mpzm.mod(all_z, mpfm.m_powers2(sbits - 1), all_z);

            mpzm.set(sig_z, all_z);
        }
        else {
            SASSERT(b);
            SASSERT(c);
            rational sgn_r(0), exp_r(0), sig_r(0);

            bool r = m_bv_util.is_numeral(a, sgn_r, bv_sz);
            SASSERT(r && bv_sz == 1);
            r = m_bv_util.is_numeral(b, exp_r, bv_sz);
            SASSERT(r && bv_sz == ebits);
            r = m_bv_util.is_numeral(c, sig_r, bv_sz);
            SASSERT(r && bv_sz == sbits - 1);
            (void)r;

            SASSERT(mpzm.is_one(sgn_r.to_mpq().denominator()));
            SASSERT(mpzm.is_one(exp_r.to_mpq().denominator()));
            SASSERT(mpzm.is_one(sig_r.to_mpq().denominator()));

            mpzm.set(sgn_z, sgn_r.to_mpq().numerator());
            mpzm.set(exp_z, exp_r.to_mpq().numerator());
            mpzm.set(sig_z, sig_r.to_mpq().numerator());
        }

        scoped_mpz exp_u = exp_z - bias;
        SASSERT(mpzm.is_int64(exp_u));

        scoped_mpf f(mpfm);
        mpfm.set(f, ebits, sbits, mpzm.is_one(sgn_z), mpzm.get_int64(exp_u), sig_z);
        result = m_fpa_util.mk_value(f);

        TRACE("t_fpa", tout << "result: [" <<
            mpzm.to_string(sgn_z) << "," <<
            mpzm.to_string(exp_z) << "," <<
            mpzm.to_string(sig_z) << "] --> " <<
            mk_ismt2_pp(result, m) << std::endl;);

        return result;
    }

    void solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        expr* e = n->get_expr();
        if (m_fpa_util.is_fp(e)) {
            SASSERT(n->num_args() == 3);
            for (enode* arg : euf::enode_args(n))
                dep.add(n, arg);
        }
        else if (m_fpa_util.is_bv2rm(e)) {
            SASSERT(n->num_args() == 1);
            dep.add(n, n->get_arg(0));
        }
        else if (m_fpa_util.is_rm(e) || m_fpa_util.is_float(e)) {
            app_ref wrapped = m_converter.wrap(e);
            if (expr2enode(wrapped))
                dep.add(n, expr2enode(wrapped));
        }
    }

    std::ostream& solver::display(std::ostream & out) const {
        bool first = true;
        for (enode* n : ctx.get_egraph().nodes()) {
            theory_var v = n->get_th_var(m_fpa_util.get_family_id());
            if (v != -1) {
                if (first) out << "fpa theory variables:" << std::endl;
                out << v << " -> " <<
                    mk_ismt2_pp(n->get_expr(), m) << std::endl;
                first = false;
            }
        }
        // if there are no fpa theory variables, was fp ever used?
        if (first) 
            return out;

        out << "bv theory variables:" << std::endl;
        for (enode * n : ctx.get_egraph().nodes()) {
            theory_var v = n->get_th_var(m_bv_util.get_family_id());
            if (v != -1) out << v << " -> " <<
                mk_ismt2_pp(n->get_expr(), m) << std::endl;
        }

        out << "arith theory variables:" << std::endl;
        for (enode* n : ctx.get_egraph().nodes()) {
            theory_var v = n->get_th_var(m_arith_util.get_family_id());
            if (v != -1) out << v << " -> " <<
                mk_ismt2_pp(n->get_expr(), m) << std::endl;
        }

        out << "equivalence classes:\n";
        for (enode * n : ctx.get_egraph().nodes()) {
            expr * e = n->get_expr();
            out << n->get_root_id() << " --> " << mk_ismt2_pp(e, m) << std::endl;
        }
        return out;
    }

};
