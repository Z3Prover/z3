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
#include "ast/fpa/bv2fpa_converter.h"

namespace fpa {

    solver::solver(euf::solver& ctx) :
        euf::th_euf_solver(ctx, symbol("fpa"), ctx.get_manager().mk_family_id("fpa")),
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
        SASSERT(m_conversions.empty());
    }


    expr_ref solver::convert(expr* e) {    
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

            ctx.push(insert_ref2_map<ast_manager, expr, expr>(m, m_conversions, e, res.get()));
        }
        return res;
    }

    sat::literal_vector solver::mk_side_conditions() {
        sat::literal_vector conds;
        expr_ref t(m);
        for (expr* arg : m_converter.m_extra_assertions) {
            ctx.get_rewriter()(arg, t);
            m_th_rw(t);
            conds.push_back(mk_literal(t));
        }
        m_converter.m_extra_assertions.reset();
        return conds;
    }

    void solver::attach_new_th_var(enode* n) {
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
        if (visited(e))
            return true;
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
        TRACE("fp", tout << "post: " << mk_bounded_pp(e, m) << "\n";);
        m_nodes.push_back(std::tuple(n, sign, root));
        ctx.push(push_back_trail(m_nodes));
        return true;
    }

    void solver::apply_sort_cnstr(enode* n, sort* s) {
        TRACE("t_fpa", tout << "apply sort cnstr for: " << mk_ismt2_pp(n->get_expr(), m) << "\n";);
        SASSERT(s->get_family_id() == get_id());
        SASSERT(m_fpa_util.is_float(s) || m_fpa_util.is_rm(s));
        SASSERT(m_fpa_util.is_float(n->get_expr()) || m_fpa_util.is_rm(n->get_expr()));
        SASSERT(n->get_decl()->get_range() == s);

        if (is_attached_to_var(n))
            return;
        attach_new_th_var(n);

        expr* owner = n->get_expr();

        if (m_fpa_util.is_rm(s) && !m_fpa_util.is_bv2rm(owner)) {
            // For every RM term, we need to make sure that it's
            // associated bit-vector is within the valid range.
            expr_ref valid(m), limit(m);
            limit = m_bv_util.mk_numeral(4, 3);
            valid = m_bv_util.mk_ule(m_converter.wrap(owner), limit);
            add_unit(mk_literal(valid));
        }
        activate(owner);
    }

    bool solver::unit_propagate() {

        if (m_nodes.size() <= m_nodes_qhead)
            return false;
        ctx.push(value_trail<unsigned>(m_nodes_qhead));
        for (; m_nodes_qhead < m_nodes.size(); ++m_nodes_qhead) 
            unit_propagate(m_nodes[m_nodes_qhead]);
        return true;
    }

    void solver::unit_propagate(std::tuple<enode*, bool, bool> const& t) {
        auto [n, sign, root] = t;
        expr* e = n->get_expr();
        app* a = to_app(e);
        if (m.is_bool(e)) {
            sat::literal atom(ctx.get_si().add_bool_var(e), false);
            atom = ctx.attach_lit(atom, e);
            sat::literal bv_atom = mk_literal(m_rw.convert_atom(m_th_rw, e));
            sat::literal_vector conds = mk_side_conditions();
            conds.push_back(bv_atom);
            add_equiv_and(atom, conds);
            if (root) {
                if (sign)
                    atom.neg();
                add_unit(atom);
            }
        }
        else {
            switch (a->get_decl_kind()) {
            case OP_FPA_TO_FP:
            case OP_FPA_TO_UBV:
            case OP_FPA_TO_SBV:
            case OP_FPA_TO_REAL:
            case OP_FPA_TO_IEEE_BV: {
                expr_ref conv = convert(e);
                add_unit(eq_internalize(e, conv));
                add_units(mk_side_conditions());
                break;
            }
            default: /* ignore */
                break;
            }
        }

    }

    void solver::activate(expr* n) {
        TRACE("t_fpa", tout << "relevant_eh for: " << mk_ismt2_pp(n, m) << "\n";);

        mpf_manager& mpfm = m_fpa_util.fm();

        if (m_fpa_util.is_float(n) || m_fpa_util.is_rm(n)) {
            expr* a = nullptr, * b = nullptr, * c = nullptr;
            if (!m_fpa_util.is_fp(n)) {
                app_ref wrapped = m_converter.wrap(n);
                mpf_rounding_mode rm;
                scoped_mpf val(mpfm);
                if (m_fpa_util.is_rm_numeral(n, rm)) {
                    expr_ref rm_num(m);
                    rm_num = m_bv_util.mk_numeral(rm, 3);
                    add_unit(eq_internalize(wrapped, rm_num)); 
                }
                else if (m_fpa_util.is_numeral(n, val)) {
                    expr_ref bv_val_e(convert(n), m);
                    VERIFY(m_fpa_util.is_fp(bv_val_e, a, b, c));
                    expr* args[] = { a, b, c };
                    expr_ref cc_args(m_bv_util.mk_concat(3, args), m);
                    add_unit(eq_internalize(wrapped, cc_args));
                    add_units(mk_side_conditions());
                }
                else 
                    add_unit(eq_internalize(m_converter.unwrap(wrapped, n->get_sort()), n));                
            }
        }
        else if (is_app(n) && to_app(n)->get_family_id() == get_id()) {
            // These are the conversion functions fp.to_* */
            SASSERT(!m_fpa_util.is_float(n) && !m_fpa_util.is_rm(n));
        }
        else {
            /* Theory variables can be merged when (= bv-term (bvwrap fp-term)) */
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

        sat::literal eq1 = eq_internalize(xe, ye); 
        sat::literal eq2 = mk_literal(c);
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

        TRACE("t_fpa", tout << "assign_eh for: " << l << "\n" << mk_ismt2_pp(e, m) << "\n";);

        sat::literal c = mk_literal(convert(e));
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
            value = m_converter.bv2fpa_value(e->get_sort(), a, b, c);
        }
        else if (m_fpa_util.is_bv2rm(e)) {
            SASSERT(n->num_args() == 1);
            value = m_converter.bv2rm_value(values.get(n->get_arg(0)->get_root_id()));
        }
        else if (m_fpa_util.is_rm(e) && is_wrapped())
            value = m_converter.bv2rm_value(values.get(expr2enode(wrapped)->get_root_id()));
        else if (m_fpa_util.is_rm(e))
            value = m_fpa_util.mk_round_toward_zero();
        else if (m_fpa_util.is_float(e) && is_wrapped()) {
            expr* a = values.get(expr2enode(wrapped)->get_root_id());
            value = m_converter.bv2fpa_value(e->get_sort(), a);
        }
        else {
            SASSERT(m_fpa_util.is_float(e));
            unsigned ebits = m_fpa_util.get_ebits(e->get_sort());
            unsigned sbits = m_fpa_util.get_sbits(e->get_sort());
            value = m_fpa_util.mk_pzero(ebits, sbits);
        }
        values.set(n->get_root_id(), value);
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        expr* e = n->get_expr();
        if (m_fpa_util.is_fp(e)) {
            SASSERT(n->num_args() == 3);
            for (enode* arg : euf::enode_args(n))
                dep.add(n, arg);
            return true;
        }
        else if (m_fpa_util.is_bv2rm(e)) {
            SASSERT(n->num_args() == 1);
            dep.add(n, n->get_arg(0));
            return true;
        }
        else if (m_fpa_util.is_rm(e) || m_fpa_util.is_float(e)) {
            euf::enode* wrapped = expr2enode(m_converter.wrap(e));
            if (wrapped)
                dep.add(n, wrapped);
            return nullptr != wrapped;
        }
        else 
            return false;
    }

    std::ostream& solver::display(std::ostream& out) const {
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
        for (enode* n : ctx.get_egraph().nodes()) {
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
        for (enode* n : ctx.get_egraph().nodes()) {
            expr* e = n->get_expr();
            out << n->get_root_id() << " --> " << mk_ismt2_pp(e, m) << std::endl;
        }
        return out;
    }

    void solver::finalize_model(model& mdl) {
        model new_model(m);

        bv2fpa_converter bv2fp(m, m_converter);

        obj_hashtable<func_decl> seen;
        bv2fp.convert_min_max_specials(&mdl, &new_model, seen);
        bv2fp.convert_uf2bvuf(&mdl, &new_model, seen);

        for (func_decl* f : seen)
            mdl.unregister_decl(f);

        for (unsigned i = 0; i < new_model.get_num_constants(); i++) {
            func_decl* f = new_model.get_constant(i);
            mdl.register_decl(f, new_model.get_const_interp(f));
        }

        for (unsigned i = 0; i < new_model.get_num_functions(); i++) {
            func_decl* f = new_model.get_function(i);
            func_interp* fi = new_model.get_func_interp(f)->copy();
            mdl.register_decl(f, fi);
        }
    }

};
