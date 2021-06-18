/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_internalize.cpp

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_solver.h"

namespace arith {

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool learned) {
        init_internalize();
        flet<bool> _is_learned(m_is_redundant, learned);
        internalize_atom(e);
        literal lit = ctx.expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e, bool redundant) {
        init_internalize();
        flet<bool> _is_learned(m_is_redundant, redundant);
        if (m.is_bool(e))
            internalize_atom(e);
        else
            internalize_term(e);
    }

    void solver::init_internalize() {
        force_push();
        // initialize 0, 1 variables:
        if (!m_internalize_initialized) {
            get_one(true);
            get_one(false);
            get_zero(true);
            get_zero(false);
            ctx.push(value_trail<bool>(m_internalize_initialized));
            m_internalize_initialized = true;
        }
    }

    lpvar solver::get_one(bool is_int) {
        return add_const(1, is_int ? m_one_var : m_rone_var, is_int);
    }

    lpvar solver::get_zero(bool is_int) {
        return add_const(0, is_int ? m_zero_var : m_rzero_var, is_int);
    }

    void solver::ensure_nla() {
        if (!m_nla) {
            m_nla = alloc(nla::solver, *m_solver.get(), m.limit());
            for (auto const& _s : m_scopes) {
                (void)_s;
                m_nla->push();
            }
            smt_params_helper prms(s().params());
            m_nla->settings().run_order() = prms.arith_nl_order();
            m_nla->settings().run_tangents() = prms.arith_nl_tangents();
            m_nla->settings().run_horner() = prms.arith_nl_horner();
            m_nla->settings().horner_subs_fixed() = prms.arith_nl_horner_subs_fixed();
            m_nla->settings().horner_frequency() = prms.arith_nl_horner_frequency();
            m_nla->settings().horner_row_length_limit() = prms.arith_nl_horner_row_length_limit();
            m_nla->settings().run_grobner() = prms.arith_nl_grobner();
            m_nla->settings().run_nra() = prms.arith_nl_nra();
            m_nla->settings().grobner_subs_fixed() = prms.arith_nl_grobner_subs_fixed();
            m_nla->settings().grobner_eqs_growth() = prms.arith_nl_grobner_eqs_growth();
            m_nla->settings().grobner_expr_size_growth() = prms.arith_nl_grobner_expr_size_growth();
            m_nla->settings().grobner_expr_degree_growth() = prms.arith_nl_grobner_expr_degree_growth();
            m_nla->settings().grobner_max_simplified() = prms.arith_nl_grobner_max_simplified();
            m_nla->settings().grobner_number_of_conflicts_to_report() = prms.arith_nl_grobner_cnfl_to_report();
            m_nla->settings().grobner_quota() = prms.arith_nl_gr_q();
            m_nla->settings().grobner_frequency() = prms.arith_nl_grobner_frequency();
            m_nla->settings().expensive_patching() = prms.arith_nl_expp();
        }
    }

    void solver::found_unsupported(expr* n) {
        ctx.push(value_trail<expr*>(m_not_handled));
        TRACE("arith", tout << "unsupported " << mk_pp(n, m) << "\n";);
        m_not_handled = n;
    }

    void solver::found_underspecified(expr* n) {
        if (a.is_underspecified(n)) {
            TRACE("arith", tout << "Unhandled: " << mk_pp(n, m) << "\n";);
            m_underspecified.push_back(to_app(n));
        }
        expr* e = nullptr, * x = nullptr, * y = nullptr;
        if (a.is_div(n, x, y)) {
            e = a.mk_div0(x, y);
        }
        else if (a.is_idiv(n, x, y)) {
            e = a.mk_idiv0(x, y);
        }
        else if (a.is_rem(n, x, y)) {
            e = a.mk_rem0(x, y);
        }
        else if (a.is_mod(n, x, y)) {
            e = a.mk_mod0(x, y);
        }
        else if (a.is_power(n, x, y)) {
            e = a.mk_power0(x, y);
        }
        if (e) {
            literal lit = eq_internalize(n, e);
            add_unit(lit);
        }
    }

    lpvar solver::add_const(int c, lpvar& var, bool is_int) {
        if (var != UINT_MAX) {
            return var;
        }
        ctx.push(value_trail<lpvar>(var));
        app_ref cnst(a.mk_numeral(rational(c), is_int), m);
        mk_enode(cnst);
        theory_var v = mk_evar(cnst);
        var = lp().add_var(v, is_int);
        add_def_constraint_and_equality(var, lp::GE, rational(c));
        add_def_constraint_and_equality(var, lp::LE, rational(c));
        TRACE("arith", tout << "add " << cnst << ", var = " << var << "\n";);
        return var;
    }

    lpvar solver::register_theory_var_in_lar_solver(theory_var v) {
        lpvar lpv = lp().external_to_local(v);
        if (lpv != lp::null_lpvar)
            return lpv;
        return lp().add_var(v, is_int(v));
    }

    void solver::linearize_term(expr* term, scoped_internalize_state& st) {
        st.push(term, rational::one());
        linearize(st);
    }

    void solver::linearize_ineq(expr* lhs, expr* rhs, scoped_internalize_state& st) {
        st.push(lhs, rational::one());
        st.push(rhs, rational::minus_one());
        linearize(st);
    }

    void solver::linearize(scoped_internalize_state& st) {
        expr_ref_vector& terms = st.terms();
        svector<theory_var>& vars = st.vars();
        vector<rational>& coeffs = st.coeffs();
        rational& offset = st.offset();
        rational r;
        expr* n1, * n2;
        unsigned index = 0;
        while (index < terms.size()) {
            SASSERT(index >= vars.size());
            expr* n = terms.get(index);
            st.to_ensure_enode().push_back(n);
            if (a.is_add(n)) {
                for (expr* arg : *to_app(n)) {
                    st.push(arg, coeffs[index]);
                }
                st.set_back(index);
            }
            else if (a.is_sub(n)) {
                unsigned sz = to_app(n)->get_num_args();
                terms[index] = to_app(n)->get_arg(0);
                for (unsigned i = 1; i < sz; ++i) {
                    st.push(to_app(n)->get_arg(i), -coeffs[index]);
                }
            }
            else if (a.is_mul(n, n1, n2) && a.is_extended_numeral(n1, r)) {
                coeffs[index] *= r;
                terms[index] = n2;
                st.to_ensure_enode().push_back(n1);
            }
            else if (a.is_mul(n, n1, n2) && a.is_extended_numeral(n2, r)) {
                coeffs[index] *= r;
                terms[index] = n1;
                st.to_ensure_enode().push_back(n2);
            }
            else if (a.is_mul(n)) {
                theory_var v = internalize_mul(to_app(n));
                coeffs[vars.size()] = coeffs[index];
                vars.push_back(v);
                ++index;
            }
            else if (a.is_power(n, n1, n2) && is_app(n1) && a.is_extended_numeral(n2, r) && r.is_unsigned() && r <= 10) {
                theory_var v = internalize_power(to_app(n), to_app(n1), r.get_unsigned());
                coeffs[vars.size()] = coeffs[index];
                vars.push_back(v);
                ++index;
            }
            else if (a.is_numeral(n, r)) {
                offset += coeffs[index] * r;
                ++index;
            }
            else if (a.is_uminus(n, n1)) {
                coeffs[index].neg();
                terms[index] = n1;
            }
            else if (a.is_to_real(n, n1)) {
                terms[index] = n1;
                if (!ctx.get_enode(n)) {
                    app* t = to_app(n);
                    VERIFY(internalize_term(to_app(n1)));
                    mk_enode(t);
                    theory_var v = mk_evar(n);
                    theory_var w = mk_evar(n1);
                    lpvar vj = register_theory_var_in_lar_solver(v);
                    lpvar wj = register_theory_var_in_lar_solver(w);
                    auto lu_constraints = lp().add_equality(vj, wj);
                    add_def_constraint(lu_constraints.first);
                    add_def_constraint(lu_constraints.second);
                }
            }
            else if (is_app(n) && a.get_family_id() == to_app(n)->get_family_id()) {
                bool is_first = nullptr == ctx.get_enode(n);
                app* t = to_app(n);
                internalize_args(t);
                mk_enode(t);
                theory_var v = mk_evar(n);
                coeffs[vars.size()] = coeffs[index];
                vars.push_back(v);
                ++index;
                if (!is_first) {
                    // skip recursive internalization
                }
                else if (a.is_to_int(n, n1)) {
                    mk_to_int_axiom(t);
                }
                else if (a.is_idiv(n, n1, n2)) {
                    if (!a.is_numeral(n2, r) || r.is_zero()) found_underspecified(n);
                    m_idiv_terms.push_back(n);
                    app_ref mod(a.mk_mod(n1, n2), m);
                    internalize(mod, m_is_redundant);
                    st.to_ensure_var().push_back(n1);
                    st.to_ensure_var().push_back(n2);
                }
                else if (a.is_mod(n, n1, n2)) {
                    if (!a.is_numeral(n2, r) || r.is_zero()) found_underspecified(n);
                    mk_idiv_mod_axioms(n1, n2);
                    st.to_ensure_var().push_back(n1);
                    st.to_ensure_var().push_back(n2);
                }
                else if (a.is_rem(n, n1, n2)) {
                    if (!a.is_numeral(n2, r) || r.is_zero()) found_underspecified(n);
                    mk_rem_axiom(n1, n2);
                    st.to_ensure_var().push_back(n1);
                    st.to_ensure_var().push_back(n2);
                }
                else if (a.is_div(n, n1, n2)) {
                    if (!a.is_numeral(n2, r) || r.is_zero()) found_underspecified(n);
                    mk_div_axiom(n1, n2);
                    st.to_ensure_var().push_back(n1);
                    st.to_ensure_var().push_back(n2);
                }
                else if (!a.is_div0(n) && !a.is_mod0(n) && !a.is_idiv0(n) && !a.is_rem0(n) && !a.is_power0(n)) {
                    found_unsupported(n);
                }
                else {
                    // no-op
                }
            }
            else {
                if (is_app(n)) {
                    internalize_args(to_app(n));
                    for (expr* arg : *to_app(n)) 
                        if (a.is_arith_expr(arg))
                            internalize_term(arg);
                }
                theory_var v = mk_evar(n);
                coeffs[vars.size()] = coeffs[index];
                vars.push_back(v);
                ++index;
            }
        }
        for (unsigned i = st.to_ensure_enode().size(); i-- > 0; ) {
            expr* n = st.to_ensure_enode()[i];
            if (is_app(n)) {
                mk_enode(to_app(n));
            }
        }
        st.to_ensure_enode().reset();
        for (unsigned i = st.to_ensure_var().size(); i-- > 0; ) {
            expr* n = st.to_ensure_var()[i];
            if (is_app(n)) 
                internalize_term(to_app(n));
        }
        st.to_ensure_var().reset();
    }

    void solver::eq_internalized(enode* n) {
        internalize_term(n->get_arg(0)->get_expr());
        internalize_term(n->get_arg(1)->get_expr());
    }

    bool solver::internalize_atom(expr* atom) {
        TRACE("arith", tout << mk_pp(atom, m) << "\n";);
        SASSERT(!ctx.get_enode(atom));
        expr* n1, *n2;
        rational r;
        lp_api::bound_kind k;
        theory_var v = euf::null_theory_var;
        bool_var bv = ctx.get_si().add_bool_var(atom);
        m_bool_var2bound.erase(bv);
        literal lit(bv, false);
        ctx.attach_lit(lit, atom);

        if (a.is_le(atom, n1, n2) && a.is_extended_numeral(n2, r)) {
            v = internalize_def(n1);
            k = lp_api::upper_t;
        }
        else if (a.is_ge(atom, n1, n2) && a.is_extended_numeral(n2, r)) {
            v = internalize_def(n1);
            k = lp_api::lower_t;
        }
        else if (a.is_le(atom, n1, n2) && a.is_extended_numeral(n1, r)) {
            v = internalize_def(n2);
            k = lp_api::lower_t;
        }
        else if (a.is_ge(atom, n1, n2) && a.is_extended_numeral(n1, r)) {
            v = internalize_def(n2);
            k = lp_api::upper_t;
        }
        else if (a.is_le(atom, n1, n2)) {
            expr_ref n3(a.mk_sub(n1, n2), m);
            rewrite(n3);
            v = internalize_def(n3);
            k = lp_api::upper_t;
            r = 0;
        }
        else if (a.is_ge(atom, n1, n2)) {
            expr_ref n3(a.mk_sub(n1, n2), m);
            rewrite(n3);
            v = internalize_def(n3);
            k = lp_api::lower_t;
            r = 0;
        }
        else if (a.is_lt(atom, n1, n2)) {
            expr_ref n3(a.mk_sub(n1, n2), m);
            rewrite(n3);
            v = internalize_def(n3);
            k = lp_api::lower_t;
            r = 0;
            lit.neg();
        }
        else if (a.is_gt(atom, n1, n2)) {
            expr_ref n3(a.mk_sub(n1, n2), m);
            rewrite(n3);
            v = internalize_def(n3);
            k = lp_api::upper_t;
            r = 0;
            lit.neg();
        }        
        else if (a.is_is_int(atom)) {
            mk_is_int_axiom(atom);
            return true;
        }
        else {
            TRACE("arith", tout << "Could not internalize " << mk_pp(atom, m) << "\n";);
            found_unsupported(atom);
            return true;
        }

        enode* n = ctx.get_enode(atom);
        theory_var w = mk_var(n);
        ctx.attach_th_var(n, this, w);
        ctx.get_egraph().set_merge_enabled(n, false);
        if (is_int(v) && !r.is_int()) 
            r = (k == lp_api::upper_t) ? floor(r) : ceil(r);        
        api_bound* b = mk_var_bound(lit, v, k, r);
        m_bounds[v].push_back(b);
        updt_unassigned_bounds(v, +1);
        m_bounds_trail.push_back(v);
        m_bool_var2bound.insert(bv, b);
        TRACE("arith_verbose", tout << "Internalized " << lit << ": " << mk_pp(atom, m) << " " << *b << "\n";);
        m_new_bounds.push_back(b);
        //add_use_lists(b);
        return true;
    }

    bool solver::internalize_term(expr* term) {
        if (!has_var(term))
            register_theory_var_in_lar_solver(internalize_def(term));
        return true;
    }

    theory_var solver::internalize_def(expr* term, scoped_internalize_state& st) {
        TRACE("arith", tout << expr_ref(term, m) << "\n";);
        if (ctx.get_enode(term))
            return mk_evar(term);

        linearize_term(term, st);
        if (is_unit_var(st))
            return st.vars()[0];

        theory_var v = mk_evar(term);
        SASSERT(euf::null_theory_var != v);
        st.coeffs().resize(st.vars().size() + 1);
        st.coeffs()[st.vars().size()] = rational::minus_one();
        st.vars().push_back(v);
        return v;
    }

    // term - v = 0
    theory_var solver::internalize_def(expr* term) {
        scoped_internalize_state st(*this);
        linearize_term(term, st);
        return internalize_linearized_def(term, st);
    }

    void solver::internalize_args(app* t, bool force) {
        SASSERT(!m.is_bool(t));
        TRACE("arith", tout << mk_pp(t, m) << " " << force << " " << reflect(t) << "\n";);
        if (!force && !reflect(t))
            return;
        for (expr* arg : *t) 
            e_internalize(arg);
    }

    theory_var solver::internalize_power(app* t, app* n, unsigned p) {
        internalize_args(t, true);
        bool _has_var = has_var(t);
        mk_enode(t);
        theory_var v = mk_evar(t);
        if (_has_var)
            return v;
        internalize_term(n);
        theory_var w = mk_evar(n);

        if (p == 0) {
            mk_power0_axioms(t, n);
        }
        else {
            svector<lpvar> vars;
            for (unsigned i = 0; i < p; ++i)
                vars.push_back(register_theory_var_in_lar_solver(w));
            ensure_nla();
            m_solver->register_existing_terms();
            m_nla->add_monic(register_theory_var_in_lar_solver(v), vars.size(), vars.data());
        }
        return v;
    }

    theory_var solver::internalize_mul(app* t) {
        SASSERT(a.is_mul(t));
        internalize_args(t, true);
        bool _has_var = has_var(t);
        mk_enode(t);
        theory_var v = mk_evar(t);

        if (!_has_var) {
            svector<lpvar> vars;
            for (expr* n : *t) {
                if (is_app(n)) VERIFY(internalize_term(to_app(n)));
                SASSERT(ctx.get_enode(n));
                theory_var v = mk_evar(n);
                vars.push_back(register_theory_var_in_lar_solver(v));
            }
            TRACE("arith", tout << "v" << v << " := " << mk_pp(t, m) << "\n" << vars << "\n";);
            m_solver->register_existing_terms();
            ensure_nla();
            m_nla->add_monic(register_theory_var_in_lar_solver(v), vars.size(), vars.data());
        }
        return v;
    }

    theory_var solver::internalize_linearized_def(expr* term, scoped_internalize_state& st) {
        theory_var v = mk_evar(term);
        TRACE("arith", tout << mk_bounded_pp(term, m) << " v" << v << "\n";);

        if (is_unit_var(st) && v == st.vars()[0]) {
            return st.vars()[0];
        }
        else if (is_one(st) && a.is_numeral(term)) {
            return get_one(a.is_int(term));
        }
        else if (is_zero(st) && a.is_numeral(term)) {
            return get_zero(a.is_int(term));
        }
        else {
            init_left_side(st);
            lpvar vi = get_lpvar(v);
            if (vi == UINT_MAX) {
                if (m_left_side.empty()) {
                    vi = lp().add_var(v, a.is_int(term));
                    add_def_constraint_and_equality(vi, lp::GE, st.offset());
                    add_def_constraint_and_equality(vi, lp::LE, st.offset());
                    register_fixed_var(v, st.offset());
                    return v;
                }
                if (!st.offset().is_zero()) {
                    m_left_side.push_back(std::make_pair(st.offset(), get_one(a.is_int(term))));
                }
                if (m_left_side.empty()) {
                    vi = lp().add_var(v, a.is_int(term));
                    add_def_constraint_and_equality(vi, lp::GE, rational(0));
                    add_def_constraint_and_equality(vi, lp::LE, rational(0));
                }
                else {
                    vi = lp().add_term(m_left_side, v);
                    SASSERT(lp::tv::is_term(vi));
                    TRACE("arith_verbose",
                        tout << "v" << v << " := " << mk_pp(term, m)
                        << " slack: " << vi << " scopes: " << m_scopes.size() << "\n";
                    lp().print_term(lp().get_term(lp::tv::raw(vi)), tout) << "\n";);
                }
            }
            return v;
        }
    }

    bool solver::is_unit_var(scoped_internalize_state& st) {
        return st.offset().is_zero() && st.vars().size() == 1 && st.coeffs()[0].is_one();
    }

    bool solver::is_one(scoped_internalize_state& st) {
        return st.offset().is_one() && st.vars().empty();
    }

    bool solver::is_zero(scoped_internalize_state& st) {
        return st.offset().is_zero() && st.vars().empty();
    }

    void solver::init_left_side(scoped_internalize_state& st) {
        SASSERT(all_zeros(m_columns));
        svector<theory_var> const& vars = st.vars();
        vector<rational> const& coeffs = st.coeffs();
        for (unsigned i = 0; i < vars.size(); ++i) {
            theory_var var = vars[i];
            rational const& coeff = coeffs[i];
            if (m_columns.size() <= static_cast<unsigned>(var)) {
                m_columns.setx(var, coeff, rational::zero());
            }
            else {
                m_columns[var] += coeff;
            }
        }
        m_left_side.clear();
        // reset the coefficients after they have been used.
        for (unsigned i = 0; i < vars.size(); ++i) {
            theory_var var = vars[i];
            rational const& r = m_columns[var];
            if (!r.is_zero()) {
                m_left_side.push_back(std::make_pair(r, register_theory_var_in_lar_solver(var)));
                m_columns[var].reset();
            }
        }
        SASSERT(all_zeros(m_columns));
    }


    enode* solver::mk_enode(expr* e) {
        TRACE("arith", tout << expr_ref(e, m) << "\n";);
        enode* n = ctx.get_enode(e);
        if (n)
            return n;
        if (!a.is_arith_expr(e))
            n = e_internalize(e);
        else {
            ptr_buffer<enode> args;
            if (reflect(e))
                for (expr* arg : *to_app(e))
                    args.push_back(e_internalize(arg));
            n = ctx.mk_enode(e, args.size(), args.data());
            ctx.attach_node(n);
        }
        return n;
    }

    theory_var solver::mk_evar(expr* n) {
        enode* e = mk_enode(n);
        if (e->is_attached_to(get_id()))
            return e->get_th_var(get_id());
        theory_var v = mk_var(e);
        TRACE("arith_verbose", tout << "v" << v << " " << mk_pp(n, m) << "\n";);
        SASSERT(m_bounds.size() <= static_cast<unsigned>(v) || m_bounds[v].empty());
        reserve_bounds(v);
        ctx.attach_th_var(e, this, v);
        SASSERT(euf::null_theory_var != v);
        return v;
    }

    bool solver::has_var(expr* e) {
        enode* n = ctx.get_enode(e);
        return n && n->is_attached_to(get_id());
    }

    void solver::add_eq_constraint(lp::constraint_index index, enode* n1, enode* n2) {
        m_constraint_sources.setx(index, equality_source, null_source);
        m_equalities.setx(index, enode_pair(n1, n2), enode_pair(nullptr, nullptr));
    }

    void solver::add_ineq_constraint(lp::constraint_index index, literal lit) {
        m_constraint_sources.setx(index, inequality_source, null_source);
        m_inequalities.setx(index, lit, sat::null_literal);
    }

    void solver::add_def_constraint(lp::constraint_index index) {
        m_constraint_sources.setx(index, definition_source, null_source);
        m_definitions.setx(index, euf::null_theory_var, euf::null_theory_var);
    }

    void solver::add_def_constraint(lp::constraint_index index, theory_var v) {
        m_constraint_sources.setx(index, definition_source, null_source);
        m_definitions.setx(index, v, euf::null_theory_var);
    }

    void solver::add_def_constraint_and_equality(lpvar vi, lp::lconstraint_kind kind,
        const rational& bound) {
        lpvar vi_equal;
        lp::constraint_index ci = lp().add_var_bound_check_on_equal(vi, kind, bound, vi_equal);
        add_def_constraint(ci);
        if (vi_equal != lp::null_lpvar)
            report_equality_of_fixed_vars(vi, vi_equal);
        m_new_eq = true;
    }

    bool solver::reflect(expr* n) const {
        return get_config().m_arith_reflect || a.is_underspecified(n) || !a.is_arith_expr(n);
    }

    lpvar solver::get_lpvar(theory_var v) const {
        return lp().external_to_local(v);
    }

    lp::tv solver::get_tv(theory_var v) const {
        return lp::tv::raw(get_lpvar(v));
    }

    /**
       \brief We must redefine this method, because theory of arithmetic contains
        underspecified operators such as division by 0.
        (/ a b) is essentially an uninterpreted function when b = 0.
        Thus, 'a' must be considered a shared var if it is the child of an underspecified operator.

        if merge(a / b, x + y) and a / b is root, then x + y become shared and all z + u in equivalence class of x + y.

        TBD: when the set of underspecified subterms is small, compute the shared variables below it.
        Recompute the set if there are merges that invalidate it.
        Use the set to determine if a variable is shared.
    */
    bool solver::is_shared(theory_var v) const {
        if (m_underspecified.empty()) {
            return false;
        }
        enode* n = var2enode(v);
        enode* r = n->get_root();
        unsigned usz = m_underspecified.size();
        if (r->num_parents() > 2 * usz) {
            for (unsigned i = 0; i < usz; ++i) {
                app* u = m_underspecified[i];
                unsigned sz = u->get_num_args();
                for (unsigned j = 0; j < sz; ++j)
                    if (expr2enode(u->get_arg(j))->get_root() == r)
                        return true;
            }
        }
        else {
            for (enode* parent : euf::enode_parents(r))
                if (a.is_underspecified(parent->get_expr()))
                    return true;
        }
        return false;
    }

    struct solver::undo_value : public trail {
        solver& s;
        undo_value(solver& s):s(s) {}
        void undo() override {
            s.m_value2var.erase(s.m_fixed_values.back());
            s.m_fixed_values.pop_back();
        }
    };


    void solver::register_fixed_var(theory_var v, rational const& value) {
        if (m_value2var.contains(value)) 
            return;
        m_fixed_values.push_back(value);
        m_value2var.insert(value, v);
        ctx.push(undo_value(*this));
    }


}

