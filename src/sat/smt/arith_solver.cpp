/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_solver.cpp

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_solver.h"


namespace arith {

    solver::solver(euf::solver& ctx, theory_id id) :
        th_euf_solver(ctx, symbol("arith"), id),
        m_model_eqs(DEFAULT_HASHTABLE_INITIAL_CAPACITY, var_value_hash(*this), var_value_eq(*this)),
        m_resource_limit(*this),
        m_bp(*this),
        a(m),
        m_bound_terms(m),
        m_bound_predicate(m)
    {
        reset_variable_values();
        m_solver = alloc(lp::lar_solver);
        // initialize 0, 1 variables:
        get_one(true);
        get_one(false);
        get_zero(true);
        get_zero(false);

        smt_params_helper lpar(ctx.s().params());
        lp().settings().set_resource_limit(m_resource_limit);
        lp().settings().simplex_strategy() = static_cast<lp::simplex_strategy_enum>(lpar.arith_simplex_strategy());
        lp().settings().bound_propagation() = bound_prop_mode::BP_NONE != propagation_mode();
        lp().settings().enable_hnf() = lpar.arith_enable_hnf();
        lp().settings().print_external_var_name() = lpar.arith_print_ext_var_names();
        lp().set_track_pivoted_rows(lpar.arith_bprop_on_pivoted_rows());
        lp().settings().report_frequency = lpar.arith_rep_freq();
        lp().settings().print_statistics = lpar.arith_print_stats();
        lp().settings().cheap_eqs() = lpar.arith_cheap_eqs();
        lp().set_cut_strategy(get_config().m_arith_branch_cut_ratio);
        lp().settings().int_run_gcd_test() = get_config().m_arith_gcd_test;
        lp().settings().set_random_seed(get_config().m_random_seed);

        m_lia = alloc(lp::int_solver, *m_solver.get());
    }

    solver::~solver() {}

    void solver::asserted(literal l) {
        m_asserted.push_back(l);
    }

    euf::th_solver* solver::clone(sat::solver* s, euf::solver& ctx) {
        arith::solver* result = alloc(arith::solver, ctx, get_id());
        ast_translation tr(m, ctx.get_manager());
        for (unsigned i = result->get_num_vars(); i < get_num_vars(); ++i) {
            expr* e1 = var2expr(i);
            expr* e2 = tr(e1);
            result->mk_evar(e2);
        }

        unsigned v = 0;
        result->m_bounds.resize(m_bounds.size());
        for (auto const& bounds : m_bounds) {            
            for (auto* b : bounds) {
                auto* b2 = result->mk_var_bound(b->get_bv(), v, b->get_bound_kind(), b->get_value());
                result->m_bounds[v].push_back(b2);
                result->m_bounds_trail.push_back(v);
                result->updt_unassigned_bounds(v, +1);
                result->m_bool_var2bound.insert(b->get_bv(), b2);
                result->m_new_bounds.push_back(b2);
            }
            ++v;
        }

        // clone rows into m_solver, m_nla, m_lia
        NOT_IMPLEMENTED_YET();

        return result;        
    }

    bool solver::unit_propagate() {
        if (m_new_bounds.empty() && m_asserted_qhead == m_asserted.size())
            return false;

        flush_bound_axioms();

        unsigned qhead = m_asserted_qhead;
        while (m_asserted_qhead < m_asserted.size() && !s().inconsistent() && m.inc()) {
            literal lit = m_asserted[m_asserted_qhead];
            lp_api::bound* b = nullptr;
            TRACE("arith", tout << "propagate: " << lit << "\n";);
            CTRACE("arith", !m_bool_var2bound.contains(lit.var()), tout << "not found " << lit << "\n";);
            if (m_bool_var2bound.find(lit.var(), b)) 
                assert_bound(!lit.sign(), *b);
            ++m_asserted_qhead;
        }
        if (s().inconsistent())
            return true;

        lbool lbl = make_feasible();
        if (!m.inc())
            return false;

        switch (lbl) {
        case l_false:
            TRACE("arith", tout << "propagation conflict\n";);
            get_infeasibility_explanation_and_set_conflict();
            break;
        case l_true:
            propagate_basic_bounds(qhead);
            propagate_bounds_with_lp_solver();
            break;
        case l_undef:
            break;
        }
        return true;
    }

    void solver::propagate_basic_bounds(unsigned qhead) {
        lp_api::bound* b = nullptr;
        for (; qhead < m_asserted_qhead && !s().inconsistent(); ++qhead) {
            literal lit = m_asserted[qhead];
            if (m_bool_var2bound.find(lit.var(), b)) 
                propagate_bound(lit, *b);            
        }
    }

    // for glb lo': lo' < lo:
    //   lo <= x -> lo' <= x 
    //   lo <= x -> ~(x <= lo')
    // for lub hi': hi' > hi
    //   x <= hi -> x <= hi'
    //   x <= hi -> ~(x >= hi')

    void solver::propagate_bound(literal lit1, lp_api::bound& b) {
        if (bound_prop_mode::BP_NONE == propagation_mode())
            return;

        bool is_true = !lit1.sign();
        lp_api::bound_kind k = b.get_bound_kind();
        theory_var v = b.get_var();
        inf_rational val = b.get_value(is_true);
        lp_bounds const& bounds = m_bounds[v];
        SASSERT(!bounds.empty());
        if (bounds.size() == 1) return;
        if (m_unassigned_bounds[v] == 0) return;
        bool v_is_int = b.is_int();
        literal lit2 = sat::null_literal;
        bool find_glb = (is_true == (k == lp_api::lower_t));
        TRACE("arith", tout << "v" << v << " find_glb: " << find_glb << " is_true: " << is_true << " k: " << k << " is_lower: " << (k == lp_api::lower_t) << "\n";);
        if (find_glb) {
            rational glb;
            lp_api::bound* lb = nullptr;
            for (lp_api::bound* b2 : bounds) {
                if (b2 == &b) continue;
                rational const& val2 = b2->get_value();
                if (((is_true || v_is_int) ? val2 < val : val2 <= val) && (!lb || glb < val2)) {
                    lb = b2;
                    glb = val2;
                }
            }
            if (!lb) return;
            bool sign = lb->get_bound_kind() != lp_api::lower_t;
            lit2 = literal(lb->get_bv(), sign);
        }
        else {
            rational lub;
            lp_api::bound* ub = nullptr;
            for (lp_api::bound* b2 : bounds) {
                if (b2 == &b) continue;
                rational const& val2 = b2->get_value();
                if (((is_true || v_is_int) ? val < val2 : val <= val2) && (!ub || val2 < lub)) {
                    ub = b2;
                    lub = val2;
                }
            }
            if (!ub) return;
            bool sign = ub->get_bound_kind() != lp_api::upper_t;
            lit2 = literal(ub->get_bv(), sign);
        }
        updt_unassigned_bounds(v, -1);
        ++m_stats.m_bound_propagations2;
        reset_evidence();
        m_core.push_back(lit1);
        m_params.push_back(parameter(m_farkas));
        m_params.push_back(parameter(rational(1)));
        m_params.push_back(parameter(rational(1)));
        assign(lit2, m_core, m_eqs, m_params);
        ++m_stats.m_bounds_propagations;
    }

    void solver::propagate_bounds_with_lp_solver() {
        if (!should_propagate())
            return;

        m_bp.init();
        lp().propagate_bounds_for_touched_rows(m_bp);

        if (!m.inc())
            return;

        if (is_infeasible())
            get_infeasibility_explanation_and_set_conflict();
        else
            for (auto& ib : m_bp.ibounds())
                if (m.inc() && !s().inconsistent())
                    propagate_lp_solver_bound(ib);
    }

    void solver::propagate_lp_solver_bound(const lp::implied_bound& be) {
        lpvar vi = be.m_j;
        theory_var v = lp().local_to_external(vi);

        if (v == euf::null_theory_var)
            return;

        TRACE("arith", tout << "v" << v << " " << be.kind() << " " << be.m_bound << "\n";);

        reserve_bounds(v);

        if (m_unassigned_bounds[v] == 0 && !should_refine_bounds()) {
            TRACE("arith", tout << "return\n";);
            return;
        }
        lp_bounds const& bounds = m_bounds[v];
        bool first = true;
        for (unsigned i = 0; i < bounds.size(); ++i) {
            lp_api::bound* b = bounds[i];
            if (s().value(b->get_bv()) != l_undef) {
                continue;
            }
            literal lit = is_bound_implied(be.kind(), be.m_bound, *b);
            if (lit == sat::null_literal) {
                continue;
            }
            TRACE("arith", tout << lit << " bound: " << *b << " first: " << first << "\n";);

            lp().settings().stats().m_num_of_implied_bounds++;
            if (first) {
                first = false;
                reset_evidence();
                m_explanation.clear();
                lp().explain_implied_bound(be, m_bp);
            }
            CTRACE("arith", m_unassigned_bounds[v] == 0, tout << "missed bound\n";);
            updt_unassigned_bounds(v, -1);
            DEBUG_CODE(for (auto& lit : m_core) { VERIFY(s().value(lit) == l_true); });
            ++m_stats.m_bound_propagations1;
            assign(lit, m_core, m_eqs, m_params);
        }

        if (should_refine_bounds() && first)
            refine_bound(v, be);
    }

    literal solver::is_bound_implied(lp::lconstraint_kind k, rational const& value, lp_api::bound const& b) const {
        if ((k == lp::LE || k == lp::LT) && b.get_bound_kind() == lp_api::upper_t && value <= b.get_value()) {
            TRACE("arith", tout << "v <= value <= b.get_value() => v <= b.get_value() \n";);
            return literal(b.get_bv(), false);
        }
        if ((k == lp::GE || k == lp::GT) && b.get_bound_kind() == lp_api::lower_t && b.get_value() <= value) {
            TRACE("arith", tout << "b.get_value() <= value <= v => b.get_value() <= v \n";);
            return literal(b.get_bv(), false);
        }
        if (k == lp::LE && b.get_bound_kind() == lp_api::lower_t && value < b.get_value()) {
            TRACE("arith", tout << "v <= value < b.get_value() => v < b.get_value()\n";);
            return literal(b.get_bv(), true);
        }
        if (k == lp::LT && b.get_bound_kind() == lp_api::lower_t && value <= b.get_value()) {
            TRACE("arith", tout << "v < value <= b.get_value() => v < b.get_value()\n";);
            return literal(b.get_bv(), true);
        }
        if (k == lp::GE && b.get_bound_kind() == lp_api::upper_t && b.get_value() < value) {
            TRACE("arith", tout << "b.get_value() < value <= v => b.get_value() < v\n";);
            return literal(b.get_bv(), true);
        }
        if (k == lp::GT && b.get_bound_kind() == lp_api::upper_t && b.get_value() <= value) {
            TRACE("arith", tout << "b.get_value() <= value < v => b.get_value() < v\n";);
            return literal(b.get_bv(), true);
        }
        return sat::null_literal;
    }


    void solver::consume(rational const& v, lp::constraint_index j) {
        set_evidence(j, m_core, m_eqs);
        m_explanation.add_pair(j, v);
    }

    void solver::add_eq(lpvar u, lpvar v, lp::explanation const& e) {
        if (s().inconsistent())
            return;
        theory_var uv = lp().local_to_external(u); // variables that are returned should have external representations
        theory_var vv = lp().local_to_external(v); // so maybe better to have them already transformed to external form
        if (is_equal(uv, vv))
            return;
        enode* n1 = var2enode(uv);
        enode* n2 = var2enode(vv);
        if (m.get_sort(n1->get_expr()) != m.get_sort(n2->get_expr()))
            return;
        reset_evidence();
        for (auto const& ev : e)
            set_evidence(ev.ci(), m_core, m_eqs);
        auto* jst = euf::th_propagation::mk(*this, m_core, m_eqs);
        ctx.propagate(n1, n2, jst->to_index());
    }

    bool solver::bound_is_interesting(unsigned vi, lp::lconstraint_kind kind, const rational& bval) const {
        theory_var v = lp().local_to_external(vi);
        if (v == euf::null_theory_var)
            return false;

        if (should_refine_bounds())
            return true;

        if (m_bounds.size() <= static_cast<unsigned>(v) || m_unassigned_bounds[v] == 0)
            return false;

        for (lp_api::bound* b : m_bounds[v])
            if (s().value(b->get_bv()) == l_undef && sat::null_literal != is_bound_implied(kind, bval, *b))
                return true;

        return false;
    }

    void solver::refine_bound(theory_var v, const lp::implied_bound& be) {
        lpvar vi = be.m_j;
        if (lp::tv::is_term(vi))
            return;
        expr_ref w(var2expr(v), m);
        if (a.is_add(w) || a.is_numeral(w) || m.is_ite(w))
            return;
        literal bound = sat::null_literal;
        switch (be.kind()) {
        case lp::LE:
            if (is_int(v) && (lp().column_has_lower_bound(vi) || !lp().column_has_upper_bound(vi)))
                bound = mk_literal(a.mk_le(w, a.mk_numeral(floor(be.m_bound), a.is_int(w))));
            if (is_real(v) && !lp().column_has_upper_bound(vi))
                bound = mk_literal(a.mk_le(w, a.mk_numeral(be.m_bound, a.is_int(w))));
            break;
        case lp::GE:
            if (is_int(v) && (lp().column_has_upper_bound(vi) || !lp().column_has_lower_bound(vi)))
                bound = mk_literal(a.mk_ge(w, a.mk_numeral(ceil(be.m_bound), a.is_int(w))));
            if (is_real(v) && !lp().column_has_lower_bound(vi))
                bound = mk_literal(a.mk_ge(w, a.mk_numeral(be.m_bound, a.is_int(w))));
            break;
        default:
            break;
        }
        if (bound == sat::null_literal)
            return;
        if (s().value(bound) == l_true)
            return;

        ++m_stats.m_bound_propagations1;
        reset_evidence();
        m_explanation.clear();
        lp().explain_implied_bound(be, m_bp);
        assign(bound, m_core, m_eqs, m_params);
    }


    void solver::assert_bound(bool is_true, lp_api::bound& b) {
        TRACE("arith", tout << b << "\n";);
        lp::constraint_index ci = b.get_constraint(is_true);
        lp().activate(ci);
        if (is_infeasible()) {
            return;
        }
        lp::lconstraint_kind k = bound2constraint_kind(b.is_int(), b.get_bound_kind(), is_true);
        if (k == lp::LT || k == lp::LE) {
            ++m_stats.m_assert_lower;
        }
        else {
            ++m_stats.m_assert_upper;
        }
        inf_rational value = b.get_value(is_true);
        if (propagate_eqs() && value.is_rational()) {
            propagate_eqs(b.tv(), ci, k, b, value.get_rational());
        }
#if 0
        if (propagation_mode() != BP_NONE)
            lp().mark_rows_for_bound_prop(b.tv().id());
#endif

    }

    void solver::propagate_eqs(lp::tv t, lp::constraint_index ci, lp::lconstraint_kind k, lp_api::bound& b, rational const& value) {
        if (k == lp::GE && set_lower_bound(t, ci, value) && has_upper_bound(t.index(), ci, value)) {
            fixed_var_eh(b.get_var(), value);
        }
        else if (k == lp::LE && set_upper_bound(t, ci, value) && has_lower_bound(t.index(), ci, value)) {
            fixed_var_eh(b.get_var(), value);
        }
    }


    bool solver::set_bound(lp::tv tv, lp::constraint_index ci, rational const& v, bool is_lower) {
        if (tv.is_term()) {
            lpvar ti = tv.id();
            auto& vec = is_lower ? m_lower_terms : m_upper_terms;
            if (vec.size() <= ti) {
                vec.resize(ti + 1, constraint_bound(UINT_MAX, rational()));
            }
            constraint_bound& b = vec[ti];
            if (b.first == UINT_MAX || (is_lower ? b.second < v : b.second > v)) {
                TRACE("arith", tout << "tighter bound " << tv.to_string() << "\n";);
                m_history.push_back(vec[ti]);
                ctx.push(history_trail<euf::solver, constraint_bound>(vec, ti, m_history));
                b.first = ci;
                b.second = v;
            }
            return true;
        }
        else {
            TRACE("arith", tout << "not a term " << tv.to_string() << "\n";);
            // m_solver already tracks bounds on proper variables, but not on terms.
            bool is_strict = false;
            rational b;
            if (is_lower) {
                return lp().has_lower_bound(tv.id(), ci, b, is_strict) && !is_strict && b == v;
            }
            else {
                return lp().has_upper_bound(tv.id(), ci, b, is_strict) && !is_strict && b == v;
            }
        }
    }

    void solver::flush_bound_axioms() {
        CTRACE("arith", !m_new_bounds.empty(), tout << "flush bound axioms\n";);

        while (!m_new_bounds.empty()) {
            lp_bounds atoms;
            atoms.push_back(m_new_bounds.back());
            m_new_bounds.pop_back();
            theory_var v = atoms.back()->get_var();
            for (unsigned i = 0; i < m_new_bounds.size(); ++i) {
                if (m_new_bounds[i]->get_var() == v) {
                    atoms.push_back(m_new_bounds[i]);
                    m_new_bounds[i] = m_new_bounds.back();
                    m_new_bounds.pop_back();
                    --i;
                }
            }
            CTRACE("arith_verbose", !atoms.empty(),
                for (unsigned i = 0; i < atoms.size(); ++i) {
                    atoms[i]->display(tout); tout << "\n";
                });
            lp_bounds occs(m_bounds[v]);

            std::sort(atoms.begin(), atoms.end(), compare_bounds());
            std::sort(occs.begin(), occs.end(), compare_bounds());

            iterator begin1 = occs.begin();
            iterator begin2 = occs.begin();
            iterator end = occs.end();
            begin1 = first(lp_api::lower_t, begin1, end);
            begin2 = first(lp_api::upper_t, begin2, end);

            iterator lo_inf = begin1, lo_sup = begin1;
            iterator hi_inf = begin2, hi_sup = begin2;
            bool flo_inf, fhi_inf, flo_sup, fhi_sup;
            ptr_addr_hashtable<lp_api::bound> visited;
            for (unsigned i = 0; i < atoms.size(); ++i) {
                lp_api::bound* a1 = atoms[i];
                iterator lo_inf1 = next_inf(a1, lp_api::lower_t, lo_inf, end, flo_inf);
                iterator hi_inf1 = next_inf(a1, lp_api::upper_t, hi_inf, end, fhi_inf);
                iterator lo_sup1 = next_sup(a1, lp_api::lower_t, lo_sup, end, flo_sup);
                iterator hi_sup1 = next_sup(a1, lp_api::upper_t, hi_sup, end, fhi_sup);
                if (lo_inf1 != end) lo_inf = lo_inf1;
                if (lo_sup1 != end) lo_sup = lo_sup1;
                if (hi_inf1 != end) hi_inf = hi_inf1;
                if (hi_sup1 != end) hi_sup = hi_sup1;
                if (!flo_inf) lo_inf = end;
                if (!fhi_inf) hi_inf = end;
                if (!flo_sup) lo_sup = end;
                if (!fhi_sup) hi_sup = end;
                visited.insert(a1);
                if (lo_inf1 != end && lo_inf != end && !visited.contains(*lo_inf)) mk_bound_axiom(*a1, **lo_inf);
                if (lo_sup1 != end && lo_sup != end && !visited.contains(*lo_sup)) mk_bound_axiom(*a1, **lo_sup);
                if (hi_inf1 != end && hi_inf != end && !visited.contains(*hi_inf)) mk_bound_axiom(*a1, **hi_inf);
                if (hi_sup1 != end && hi_sup != end && !visited.contains(*hi_sup)) mk_bound_axiom(*a1, **hi_sup);
            }
        }
    }

    lp_bounds::iterator solver::first(
        lp_api::bound_kind kind,
        iterator it,
        iterator end) {
        for (; it != end; ++it) {
            lp_api::bound* a = *it;
            if (a->get_bound_kind() == kind) return it;
        }
        return end;
    }

    lp_bounds::iterator solver::next_inf(
        lp_api::bound* a1,
        lp_api::bound_kind kind,
        iterator it,
        iterator end,
        bool& found_compatible) {
        rational const& k1(a1->get_value());
        iterator result = end;
        found_compatible = false;
        for (; it != end; ++it) {
            lp_api::bound* a2 = *it;
            if (a1 == a2) continue;
            if (a2->get_bound_kind() != kind) continue;
            rational const& k2(a2->get_value());
            found_compatible = true;
            if (k2 <= k1) {
                result = it;
            }
            else {
                break;
            }
        }
        return result;
    }

    lp_bounds::iterator solver::next_sup(
        lp_api::bound* a1,
        lp_api::bound_kind kind,
        iterator it,
        iterator end,
        bool& found_compatible) {
        rational const& k1(a1->get_value());
        found_compatible = false;
        for (; it != end; ++it) {
            lp_api::bound* a2 = *it;
            if (a1 == a2) continue;
            if (a2->get_bound_kind() != kind) continue;
            rational const& k2(a2->get_value());
            found_compatible = true;
            if (k1 < k2) {
                return it;
            }
        }
        return end;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        theory_var v = n->get_th_var(get_id());
        expr* o = n->get_expr();
        expr_ref value(m);
        if (use_nra_model() && lp().external_to_local(v) != lp::null_lpvar) {
            anum const& an = nl_value(v, *m_a1);
            if (a.is_int(o) && !m_nla->am().is_int(an))
                value = a.mk_numeral(rational::zero(), a.is_int(o));
            else
                value = a.mk_numeral(m_nla->am(), nl_value(v, *m_a1), a.is_int(o));
        }
        else {
            rational r = get_value(v);
            TRACE("arith", tout << mk_pp(o, m) << " v" << v << " := " << r << "\n";);
            SASSERT("integer variables should have integer values: " && (!a.is_int(o) || r.is_int() || m.limit().is_canceled()));
            if (a.is_int(o) && !r.is_int()) 
                r = floor(r);
            value = a.mk_numeral(r, m.get_sort(o));
        }
        values.set(n->get_root_id(), value);
    }

    void solver::push_core() {
        TRACE("arith", tout << "push\n";);
        m_scopes.push_back(scope());
        scope& sc = m_scopes.back();
        sc.m_bounds_lim = m_bounds_trail.size();
        sc.m_asserted_qhead = m_asserted_qhead;
        sc.m_idiv_lim = m_idiv_terms.size();
        sc.m_asserted_lim = m_asserted.size();
        sc.m_not_handled = m_not_handled;
        sc.m_underspecified_lim = m_underspecified.size();
        lp().push();
        if (m_nla)
            m_nla->push();

    }

    void solver::pop_core(unsigned num_scopes) {
        TRACE("arith", tout << "pop " << num_scopes << "\n";);
        unsigned old_size = m_scopes.size() - num_scopes;
        del_bounds(m_scopes[old_size].m_bounds_lim);
        m_idiv_terms.shrink(m_scopes[old_size].m_idiv_lim);
        m_asserted.shrink(m_scopes[old_size].m_asserted_lim);
        m_asserted_qhead = m_scopes[old_size].m_asserted_qhead;
        m_underspecified.shrink(m_scopes[old_size].m_underspecified_lim);
        m_not_handled = m_scopes[old_size].m_not_handled;
        m_scopes.resize(old_size);
        lp().pop(num_scopes);
        m_new_bounds.reset();
        if (m_nla)
            m_nla->pop(num_scopes);
        TRACE("arith", tout << "num scopes: " << num_scopes << " new scope level: " << m_scopes.size() << "\n";);
    }

    void solver::del_bounds(unsigned old_size) {
        for (unsigned i = m_bounds_trail.size(); i-- > old_size; ) {
            unsigned v = m_bounds_trail[i];
            lp_api::bound* b = m_bounds[v].back();
            // del_use_lists(b);
            dealloc(b);
            m_bounds[v].pop_back();
        }
        m_bounds_trail.shrink(old_size);
    }

    void solver::report_equality_of_fixed_vars(unsigned vi1, unsigned vi2) {
        rational bound;
        lp::constraint_index ci1, ci2, ci3, ci4;
        theory_var v1 = lp().local_to_external(vi1);
        theory_var v2 = lp().local_to_external(vi2);
        TRACE("arith", tout << "fixed: " << mk_pp(var2expr(v1), m) << " " << mk_pp(var2expr(v2), m) << "\n";);
        // we expect lp() to ensure that none of these returns happen.

        if (is_equal(v1, v2))
            return;
        if (is_int(v1) != is_int(v2))
            return;
        if (!has_lower_bound(vi1, ci1, bound))
            return;
        if (!has_upper_bound(vi1, ci2, bound))
            return;
        if (!has_lower_bound(vi2, ci3, bound))
            return;
        if (!has_upper_bound(vi2, ci4, bound))
            return;

        ++m_stats.m_fixed_eqs;
        reset_evidence();
        set_evidence(ci1, m_core, m_eqs);
        set_evidence(ci2, m_core, m_eqs);
        set_evidence(ci3, m_core, m_eqs);
        set_evidence(ci4, m_core, m_eqs);
        enode* x = var2enode(v1);
        enode* y = var2enode(v2);
        auto* jst = euf::th_propagation::mk(*this, m_core, m_eqs);
        ctx.propagate(x, y, jst->to_index());
    }

    bool solver::is_equal(theory_var x, theory_var y) const {
        return x == y || var2enode(x)->get_root() == var2enode(y)->get_root();
    }

    bool solver::has_upper_bound(lpvar vi, lp::constraint_index& ci, rational const& bound) { return has_bound(vi, ci, bound, false); }

    bool solver::has_lower_bound(lpvar vi, lp::constraint_index& ci, rational const& bound) { return has_bound(vi, ci, bound, true); }

    bool solver::has_bound(lpvar vi, lp::constraint_index& ci, rational const& bound, bool is_lower) {
        if (lp::tv::is_term(vi)) {
            theory_var v = lp().local_to_external(vi);
            rational val;
            TRACE("arith", tout << lp().get_variable_name(vi) << " " << v << "\n";);
            if (v != euf::null_theory_var && a.is_numeral(var2expr(v), val) && bound == val) {
                ci = UINT_MAX;
                return bound == val;
            }

            auto& vec = is_lower ? m_lower_terms : m_upper_terms;
            lpvar ti = lp::tv::unmask_term(vi);
            if (vec.size() > ti) {
                constraint_bound& b = vec[ti];
                ci = b.first;
                return ci != UINT_MAX && bound == b.second;
            }
            else {
                return false;
            }
        }
        else {
            bool is_strict = false;
            rational b;
            if (is_lower) {
                return lp().has_lower_bound(vi, ci, b, is_strict) && b == bound && !is_strict;
            }
            else {
                return lp().has_upper_bound(vi, ci, b, is_strict) && b == bound && !is_strict;
            }
        }
    }

    void solver::updt_unassigned_bounds(theory_var v, int inc) {
        TRACE("arith", tout << "v" << v << " " << m_unassigned_bounds[v] << " += " << inc << "\n";);
        ctx.push(vector_value_trail<euf::solver, unsigned, false>(m_unassigned_bounds, v));
        m_unassigned_bounds[v] += inc;
    }

    void solver::reserve_bounds(theory_var v) {
        while (m_bounds.size() <= static_cast<unsigned>(v)) {
            m_bounds.push_back(lp_bounds());
            m_unassigned_bounds.push_back(0);
        }
    }

    bool solver::all_zeros(vector<rational> const& v) const {
        for (rational const& r : v)
            if (!r.is_zero())
                return false;
        return true;
    }

    bound_prop_mode solver::propagation_mode() const {
        return m_num_conflicts < get_config().m_arith_propagation_threshold ?
            get_config().m_arith_bound_prop :
            bound_prop_mode::BP_NONE;
    }

    void solver::init_variable_values() {
        reset_variable_values();
        if (m.inc() && m_solver.get() && get_num_vars() > 0) {
            TRACE("arith", display(tout << "update variable values\n"););
            lp().get_model(m_variable_values);
        }
    }

    void solver::reset_variable_values() {
        m_variable_values.clear();
    }

    lbool solver::get_phase(bool_var v) {
        lp_api::bound* b;
        if (!m_bool_var2bound.find(v, b)) {
            return l_undef;
        }
        lp::lconstraint_kind k = lp::EQ;
        switch (b->get_bound_kind()) {
        case lp_api::lower_t:
            k = lp::GE;
            break;
        case lp_api::upper_t:
            k = lp::LE;
            break;
        default:
            break;
        }
        auto vi = register_theory_var_in_lar_solver(b->get_var());
        if (vi == lp::null_lpvar) {
            return l_undef;
        }
        return lp().compare_values(vi, k, b->get_value()) ? l_true : l_false;
    }

    bool solver::can_get_value(theory_var v) const {
        return can_get_bound(v) && !m_variable_values.empty();
    }

    bool solver::can_get_bound(theory_var v) const {
        return v != euf::null_theory_var && lp().external_is_used(v);
    }

    bool solver::can_get_ivalue(theory_var v) const {
        return can_get_bound(v);
    }

    void solver::ensure_column(theory_var v) {
        if (!lp().external_is_used(v))
            register_theory_var_in_lar_solver(v);
    }

    lp::impq solver::get_ivalue(theory_var v) const {
        SASSERT(can_get_ivalue(v));
        auto t = get_tv(v);
        if (!t.is_term())
            return lp().get_column_value(t.id());
        m_todo_terms.push_back(std::make_pair(t, rational::one()));
        lp::impq result(0);
        while (!m_todo_terms.empty()) {
            t = m_todo_terms.back().first;
            rational coeff = m_todo_terms.back().second;
            m_todo_terms.pop_back();
            if (t.is_term()) {
                const lp::lar_term& term = lp().get_term(t);
                for (const auto& i : term) {
                    m_todo_terms.push_back(std::make_pair(lp().column2tv(i.column()), coeff * i.coeff()));
                }
            }
            else {
                result += lp().get_column_value(t.id()) * coeff;
            }
        }
        return result;
    }

    rational solver::get_value(theory_var v) const {
        if (v == euf::null_theory_var || !lp().external_is_used(v)) {
            return rational::zero();
        }

        auto t = get_tv(v);
        if (m_variable_values.count(t.index()) > 0)
            return m_variable_values[t.index()];

        if (!t.is_term() && lp().is_fixed(t.id()))
            return lp().column_lower_bound(t.id()).x;

        if (!t.is_term())
            return rational::zero();

        m_todo_terms.push_back(std::make_pair(t, rational::one()));
        rational result(0);
        while (!m_todo_terms.empty()) {
            auto t2 = m_todo_terms.back().first;
            rational coeff = m_todo_terms.back().second;
            m_todo_terms.pop_back();
            if (t2.is_term()) {
                const lp::lar_term& term = lp().get_term(t2);
                for (const auto& i : term) {
                    auto tv = lp().column2tv(i.column());
                    if (m_variable_values.count(tv.index()) > 0) {
                        result += m_variable_values[tv.index()] * coeff * i.coeff();
                    }
                    else {
                        m_todo_terms.push_back(std::make_pair(tv, coeff * i.coeff()));
                    }
                }
            }
            else {
                result += m_variable_values[t2.index()] * coeff;
            }
        }
        m_variable_values[t.index()] = result;
        return result;
    }

    void solver::random_update() {
        if (m_nla)
            return;
        m_tmp_var_set.clear();
        m_tmp_var_set.resize(get_num_vars());
        m_model_eqs.reset();
        svector<lpvar> vars;
        theory_var sz = static_cast<theory_var>(get_num_vars());
        for (theory_var v = 0; v < sz; ++v) {
            ensure_column(v);
            lp::column_index vj = lp().to_column_index(v);
            SASSERT(!vj.is_null());
            theory_var other = m_model_eqs.insert_if_not_there(v);
            if (is_equal(v, other))
                continue;
            if (!lp().is_fixed(vj))
                vars.push_back(vj.index());
            else if (!m_tmp_var_set.contains(other)) {
                lp::column_index other_j = lp().to_column_index(other);
                if (!lp().is_fixed(other_j)) {
                    m_tmp_var_set.insert(other);
                    vars.push_back(other_j.index());
                }
            }
        }
        if (!vars.empty())
            lp().random_update(vars.size(), vars.c_ptr());
    }

    bool solver::assume_eqs() {
        TRACE("arith", display(tout););
        random_update();
        m_model_eqs.reset();
        theory_var sz = static_cast<theory_var>(get_num_vars());
        unsigned old_sz = m_assume_eq_candidates.size();
        int start = s().rand()();
        for (theory_var i = 0; i < sz; ++i) {
            theory_var v = (i + start) % sz;
            enode* n1 = var2enode(v);
            ensure_column(v);
            if (!can_get_ivalue(v))
                continue;
            theory_var other = m_model_eqs.insert_if_not_there(v);
            TRACE("arith", tout << "insert: v" << v << " := " << get_value(v) << " found: v" << other << "\n";);
            if (!is_equal(other, v))
                m_assume_eq_candidates.push_back(std::make_pair(v, other));
        }

        if (m_assume_eq_candidates.size() > old_sz)
            ctx.push(restore_size_trail<euf::solver, std::pair<theory_var, theory_var>, false>(m_assume_eq_candidates, old_sz));

        return delayed_assume_eqs();
    }

    bool solver::delayed_assume_eqs() {
        if (m_assume_eq_head == m_assume_eq_candidates.size())
            return false;

        ctx.push(value_trail<euf::solver, unsigned>(m_assume_eq_head));
        while (m_assume_eq_head < m_assume_eq_candidates.size()) {
            std::pair<theory_var, theory_var> const& p = m_assume_eq_candidates[m_assume_eq_head];
            theory_var v1 = p.first;
            theory_var v2 = p.second;
            enode* n1 = var2enode(v1);
            enode* n2 = var2enode(v2);
            m_assume_eq_head++;
            CTRACE("arith",
                is_eq(v1, v2) && n1->get_root() != n2->get_root(),
                tout << "assuming eq: v" << v1 << " = v" << v2 << "\n";);
            if (!is_eq(v1, v2))
                continue;
            if (n1->get_root() == n2->get_root())
                continue;
            literal eq = eq_internalize(n1->get_expr(), n2->get_expr());
            if (s().value(eq) != l_true)
                return true;
        }
        return false;
    }

    bool solver::use_nra_model() {
        if (m_nla && m_nla->use_nra_model()) {
            if (!m_a1) {
                m_a1 = alloc(scoped_anum, m_nla->am());
                m_a2 = alloc(scoped_anum, m_nla->am());
            }
            return true;
        }
        return false;
    }

    bool solver::is_eq(theory_var v1, theory_var v2) {
        if (use_nra_model()) {
            return m_nla->am().eq(nl_value(v1, *m_a1), nl_value(v2, *m_a2));
        }
        else {
            return get_ivalue(v1) == get_ivalue(v2);
        }
    }

    sat::check_result solver::check() {
        flet<bool> _is_learned(m_is_redundant, true);
        reset_variable_values();
        IF_VERBOSE(12, verbose_stream() << "final-check " << lp().get_status() << "\n");
        SASSERT(lp().ax_is_correct());

        if (lp().get_status() != lp::lp_status::OPTIMAL) {
            switch (make_feasible()) {
            case l_false:
                get_infeasibility_explanation_and_set_conflict();
                return sat::check_result::CR_CONTINUE;
            case l_undef:
                TRACE("arith", tout << "check feasiable is undef\n";);
                return m.inc() ? sat::check_result::CR_CONTINUE : sat::check_result::CR_GIVEUP;
            case l_true:
                break;
            default:
                UNREACHABLE();
            }
        }

        auto st = sat::check_result::CR_DONE;

        TRACE("arith", ctx.display(tout););

        switch (check_lia()) {
        case l_true:
            break;
        case l_false:
            return sat::check_result::CR_CONTINUE;
        case l_undef:
            TRACE("arith", tout << "check-lia giveup\n";);
            st = sat::check_result::CR_CONTINUE;
            break;
        }

        switch (check_nla()) {
        case l_true:
            break;
        case l_false:
            return sat::check_result::CR_CONTINUE;
        case l_undef:
            TRACE("arith", tout << "check-nra giveup\n";);
            st = sat::check_result::CR_GIVEUP;
            break;
        }

        if (delayed_assume_eqs()) {
            ++m_stats.m_assume_eqs;
            return sat::check_result::CR_CONTINUE;
        }
        if (assume_eqs()) {
            ++m_stats.m_assume_eqs;
            return sat::check_result::CR_CONTINUE;
        }
        if (m_not_handled != nullptr) {
            TRACE("arith", tout << "unhandled operator " << mk_pp(m_not_handled, m) << "\n";);
            st = sat::check_result::CR_GIVEUP;
        }
        return st;
    }

    nlsat::anum const& solver::nl_value(theory_var v, scoped_anum& r) const {
        SASSERT(m_nla);
        SASSERT(m_nla->use_nra_model());
        auto t = get_tv(v);
        if (t.is_term()) {

            m_todo_terms.push_back(std::make_pair(t, rational::one()));
            TRACE("nl_value", tout << "v" << v << " " << t.to_string() << "\n";);
            TRACE("nl_value", tout << "v" << v << " := w" << t.to_string() << "\n";
            lp().print_term(lp().get_term(t), tout) << "\n";);

            m_nla->am().set(r, 0);
            while (!m_todo_terms.empty()) {
                rational wcoeff = m_todo_terms.back().second;
                t = m_todo_terms.back().first;
                m_todo_terms.pop_back();
                lp::lar_term const& term = lp().get_term(t);
                TRACE("nl_value", lp().print_term(term, tout) << "\n";);
                scoped_anum r1(m_nla->am());
                rational c1(0);
                m_nla->am().set(r1, c1.to_mpq());
                m_nla->am().add(r, r1, r);
                for (auto const& arg : term) {
                    auto wi = lp().column2tv(arg.column());
                    c1 = arg.coeff() * wcoeff;
                    if (wi.is_term()) {
                        m_todo_terms.push_back(std::make_pair(wi, c1));
                    }
                    else {
                        m_nla->am().set(r1, c1.to_mpq());
                        m_nla->am().mul(m_nla->am_value(wi.id()), r1, r1);
                        m_nla->am().add(r1, r, r);
                    }
                }
            }
            return r;
        }
        else {
            return m_nla->am_value(t.id());
        }
    }

    lbool solver::make_feasible() {
        TRACE("pcs", tout << lp().constraints(););
        auto status = lp().find_feasible_solution();
        TRACE("arith_verbose", display(tout););
        switch (status) {
        case lp::lp_status::INFEASIBLE:
            return l_false;
        case lp::lp_status::FEASIBLE:
        case lp::lp_status::OPTIMAL:
            return l_true;
        case lp::lp_status::TIME_EXHAUSTED:
        default:
            TRACE("arith", tout << "status treated as inconclusive: " << status << "\n";);
            return l_undef;
        }
    }

    lbool solver::check_lia() {
        TRACE("arith", );
        if (!m.inc())
            return l_undef;
        lbool lia_check = l_undef;
        if (!check_idiv_bounds())
            return l_false;

        switch (m_lia->check(&m_explanation)) {
        case lp::lia_move::sat:
            lia_check = l_true;
            break;

        case lp::lia_move::branch: {
            TRACE("arith", tout << "branch\n";);
            app_ref b(m);
            bool u = m_lia->is_upper();
            auto const& k = m_lia->get_offset();
            rational offset;
            expr_ref t(m);
            b = mk_bound(m_lia->get_term(), k, !u, offset, t);
            IF_VERBOSE(4, verbose_stream() << "branch " << b << "\n";);
            // branch on term >= k + 1
            // branch on term <= k
            // TBD: ctx().force_phase(ctx().get_literal(b));
            // at this point we have a new unassigned atom that the 
            // SAT core assigns a value to
            lia_check = l_false;
            ++m_stats.m_branch;
            add_variable_bound(t, offset);
            break;
        }
        case lp::lia_move::cut: {
            TRACE("arith", tout << "cut\n";);
            ++m_stats.m_gomory_cuts;
            // m_explanation implies term <= k
            reset_evidence();
            for (auto const& ev : m_explanation)
                set_evidence(ev.ci(), m_core, m_eqs);
            // The call mk_bound() can set the m_infeasible_column in lar_solver
            // so the explanation is safer to take before this call.
            app_ref b = mk_bound(m_lia->get_term(), m_lia->get_offset(), !m_lia->is_upper());
            IF_VERBOSE(4, verbose_stream() << "cut " << b << "\n");
            literal lit = expr2literal(b);
            assign(lit, m_core, m_eqs, m_params);
            lia_check = l_false;
            break;
        }
        case lp::lia_move::conflict:
            TRACE("arith", tout << "conflict\n";);
            // ex contains unsat core
            set_conflict();
            return l_false;
        case lp::lia_move::undef:
            TRACE("arith", tout << "lia undef\n";);
            lia_check = l_undef;
            break;
        case lp::lia_move::continue_with_check:
            lia_check = l_undef;
            break;
        default:
            UNREACHABLE();
        }
        return lia_check;
    }

    void solver::assign(literal lit, literal_vector const& core, svector<enode_pair> const& eqs, vector<parameter> const& params) {
        if (core.size() < small_lemma_size() && eqs.empty()) {
            m_core2.reset();
            for (auto const& c : core)
                m_core2.push_back(~c);
            m_core2.push_back(lit);
            add_clause(m_core2);
        }
        else {
            auto* jst = euf::th_propagation::mk(*this, core, eqs);
            ctx.propagate(lit, jst->to_index());
        }
    }

    void solver::get_infeasibility_explanation_and_set_conflict() {
        m_explanation.clear();
        lp().get_infeasibility_explanation(m_explanation);
        set_conflict();
    }

    void solver::set_conflict() {
        literal_vector core;
        set_conflict_or_lemma(core, true);
    }

    void solver::set_conflict_or_lemma(literal_vector const& core, bool is_conflict) {
        reset_evidence();
        m_core.append(core);
        ++m_num_conflicts;
        ++m_stats.m_conflicts;
        TRACE("arith", display(tout << "is-conflict: " << is_conflict << "\n"););
        for (auto const& ev : m_explanation)
            set_evidence(ev.ci(), m_core, m_eqs);
        for (auto const& eq : m_eqs)
            m_core.push_back(eq_internalize(eq.first->get_expr(), eq.second->get_expr()));
        for (literal& c : m_core)
            c.neg();
        add_clause(m_core);
    }

    bool solver::is_infeasible() const {
        return lp().get_status() == lp::lp_status::INFEASIBLE;
    }

    void solver::set_evidence(lp::constraint_index idx, literal_vector& core, svector<enode_pair>& eqs) {
        if (idx == UINT_MAX) {
            return;
        }
        switch (m_constraint_sources[idx]) {
        case inequality_source: {
            literal lit = m_inequalities[idx];
            SASSERT(lit != sat::null_literal);
            core.push_back(lit);
            break;
        }
        case equality_source:
            SASSERT(m_equalities[idx].first != nullptr);
            SASSERT(m_equalities[idx].second != nullptr);
            m_eqs.push_back(m_equalities[idx]);
            break;
        case definition_source:
            // skip definitions (these are treated as hard constraints)
            break;
        default:
            UNREACHABLE();
            break;
        }
    }

    void solver::add_variable_bound(expr* t, rational const& offset) {
        if (!use_bounded_expansion())
            return;
        if (m_bounded_range_lit == sat::null_literal)
            return;
        // if term is not already bounded, add a range and assert max_bound => range
        bound_info bi(offset, init_range());
        if (m_term2bound_info.find(t, bi))
            return;
        expr_ref hi(a.mk_le(t, a.mk_int(offset + bi.m_range)), m);
        expr_ref lo(a.mk_ge(t, a.mk_int(offset - bi.m_range)), m);
        add_clause(~m_bounded_range_lit, mk_literal(hi));
        add_clause(~m_bounded_range_lit, mk_literal(lo));
        m_bound_terms.push_back(lo);
        m_bound_terms.push_back(hi);
        m_bound_terms.push_back(t);
        m_predicate2term.insert(lo, t);
        m_predicate2term.insert(hi, t);
        m_term2bound_info.insert(t, bi);
    }

    void solver::reset_evidence() {
        m_core.reset();
        m_eqs.reset();
        m_params.reset();
    }

    // create an eq atom representing "term = offset"
    literal solver::mk_eq(lp::lar_term const& term, rational const& offset) {
        u_map<rational> coeffs;
        term2coeffs(term, coeffs);
        bool isint = offset.is_int();
        for (auto const& kv : coeffs) isint &= is_int(kv.m_key) && kv.m_value.is_int();
        app_ref t = coeffs2app(coeffs, rational::zero(), isint);
        app_ref s(a.mk_numeral(offset, isint), m);
        return eq_internalize(t, s);
    }
    // create a bound atom representing term >= k is lower_bound is true, and term <= k if it is false
    app_ref solver::mk_bound(lp::lar_term const& term, rational const& k, bool lower_bound) {
        rational offset;
        expr_ref t(m);
        return mk_bound(term, k, lower_bound, offset, t);
    }

    app_ref solver::mk_bound(lp::lar_term const& term, rational const& k, bool lower_bound, rational& offset, expr_ref& t) {
        offset = k;
        u_map<rational> coeffs;
        term2coeffs(term, coeffs);
        bool is_int = true;
        rational lc = denominator(k);
        for (auto const& kv : coeffs) {
            theory_var w = kv.m_key;
            expr* o = var2expr(w);
            is_int = a.is_int(o);
            if (!is_int) break;
            lc = lcm(lc, denominator(kv.m_value));
        }

        // ensure that coefficients are integers when all variables are integers as well.
        if (is_int && !lc.is_one()) {
            SASSERT(lc.is_pos());
            offset *= lc;
            for (auto& kv : coeffs) kv.m_value *= lc;
        }

        if (is_int) {
            // 3x + 6y >= 5 -> x + 3y >= 5/3, then x + 3y >= 2
            // 3x + 6y <= 5 -> x + 3y <= 1
            rational g = gcd_reduce(coeffs);
            if (!g.is_one()) {
                if (lower_bound) {
                    TRACE("arith", tout << "lower: " << offset << " / " << g << " = " << offset / g << " >= " << ceil(offset / g) << "\n";);
                    offset = ceil(offset / g);
                }
                else {
                    TRACE("arith", tout << "upper: " << offset << " / " << g << " = " << offset / g << " <= " << floor(offset / g) << "\n";);
                    offset = floor(offset / g);
                }
            }
        }
        if (!coeffs.empty() && coeffs.begin()->m_value.is_neg()) {
            offset.neg();
            lower_bound = !lower_bound;
            for (auto& kv : coeffs) kv.m_value.neg();
        }

        // CTRACE("arith", is_int,
        //        lp().print_term(term, tout << "term: ") << "\n";
        //        tout << "offset: " << offset << " gcd: " << g << "\n";);

        app_ref atom(m);
        t = coeffs2app(coeffs, rational::zero(), is_int);
        if (lower_bound) {
            atom = a.mk_ge(t, a.mk_numeral(offset, is_int));
        }
        else {
            atom = a.mk_le(t, a.mk_numeral(offset, is_int));
        }

        TRACE("arith", tout << t << ": " << atom << "\n";
        lp().print_term(term, tout << "bound atom: ") << (lower_bound ? " >= " : " <= ") << k << "\n";);
        b_internalize(atom);
        return atom;
    }

    void solver::term2coeffs(lp::lar_term const& term, u_map<rational>& coeffs) {
        term2coeffs(term, coeffs, rational::one());
    }

    void solver::term2coeffs(lp::lar_term const& term, u_map<rational>& coeffs, rational const& coeff) {
        TRACE("arith", lp().print_term(term, tout) << "\n";);
        for (const auto& ti : term) {
            theory_var w;
            auto tv = lp().column2tv(ti.column());
            if (tv.is_term()) {
                lp::lar_term const& term1 = lp().get_term(tv);
                rational coeff2 = coeff * ti.coeff();
                term2coeffs(term1, coeffs, coeff2);
                continue;
            }
            else {
                w = lp().local_to_external(tv.id());
                SASSERT(w >= 0);
                TRACE("arith", tout << (tv.id()) << ": " << w << "\n";);
            }
            rational c0(0);
            coeffs.find(w, c0);
            coeffs.insert(w, c0 + ti.coeff() * coeff);
        }
    }

    app_ref solver::coeffs2app(u_map<rational> const& coeffs, rational const& offset, bool is_int) {
        expr_ref_vector args(m);
        for (auto const& kv : coeffs) {
            theory_var w = kv.m_key;
            expr* o = var2expr(w);
            if (kv.m_value.is_zero())
                continue;
            else if (kv.m_value.is_one())
                args.push_back(o);
            else
                args.push_back(a.mk_mul(a.mk_numeral(kv.m_value, is_int), o));
        }

        if (!offset.is_zero() || args.empty()) 
            args.push_back(a.mk_numeral(offset, is_int));

        if (args.size() == 1)
            return app_ref(to_app(args[0].get()), m);

        return app_ref(a.mk_add(args.size(), args.c_ptr()), m);        
    }

    app_ref solver::mk_term(lp::lar_term const& term, bool is_int) {
        u_map<rational> coeffs;
        term2coeffs(term, coeffs);
        return coeffs2app(coeffs, rational::zero(), is_int);
    }

    rational solver::gcd_reduce(u_map<rational>& coeffs) {
        rational g(0);
        for (auto const& kv : coeffs) 
            g = gcd(g, kv.m_value);        
        if (g.is_zero())
            return rational::one();
        if (!g.is_one()) 
            for (auto& kv : coeffs) 
                kv.m_value /= g;                    
        return g;
    }

    void solver::false_case_of_check_nla(const nla::lemma& l) {
        m_lemma = l; //todo avoid the copy
        m_explanation = l.expl();
        literal_vector core;
        for (auto const& ineq : m_lemma.ineqs()) {
            bool is_lower = true, pos = true, is_eq = false;
            switch (ineq.cmp()) {
            case lp::LE: is_lower = false; pos = false;  break;
            case lp::LT: is_lower = true;  pos = true; break;
            case lp::GE: is_lower = true;  pos = false;  break;
            case lp::GT: is_lower = false; pos = true; break;
            case lp::EQ: is_eq = true; pos = false; break;
            case lp::NE: is_eq = true; pos = true; break;
            default: UNREACHABLE();
            }
            TRACE("arith", tout << "is_lower: " << is_lower << " pos " << pos << "\n";);
            app_ref atom(m);
            // TBD utility: lp::lar_term term = mk_term(ineq.m_poly);
            // then term is used instead of ineq.m_term
            if (is_eq) {
                core.push_back(~mk_eq(ineq.term(), ineq.rs()));
            }
            else {
                // create term >= 0 (or term <= 0)
                core.push_back(~ctx.expr2literal(mk_bound(ineq.term(), ineq.rs(), is_lower)));
            }
        }
        set_conflict_or_lemma(core, false);
    }

    lbool solver::check_nla() {
        if (!m.inc()) {
            TRACE("arith", tout << "canceled\n";);
            return l_undef;
        }
        if (!m_nla) {
            TRACE("arith", tout << "no nla\n";);
            return l_true;
        }
        if (!m_nla->need_check())
            return l_true;

        m_a1 = nullptr; m_a2 = nullptr;
        lbool r = m_nla->check(m_nla_lemma_vector);
        switch (r) {
        case l_false: {
            for (const nla::lemma& l : m_nla_lemma_vector)
                false_case_of_check_nla(l);
            break;
        }
        case l_true:
            if (assume_eqs())
                return l_false;
            break;
        case l_undef:
            break;
        }
        return r;
    }

    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) {
        auto& jst = euf::th_propagation::from_index(idx);
        for (auto lit : euf::th_propagation::lits(jst))
            r.push_back(lit);
        for (auto eq : euf::th_propagation::eqs(jst))
            ctx.add_antecedent(eq.first, eq.second);

        if (!probing && ctx.use_drat()) {
            literal_vector lits;
            for (auto lit : euf::th_propagation::lits(jst))
                lits.push_back(~lit);
            lits.push_back(l);
            ctx.get_drat().add(lits, status());
            for (auto eq : euf::th_propagation::eqs(jst))
                IF_VERBOSE(0, verbose_stream() << "drat-log with equalities is TBD " << eq.first->get_expr_id() << "\n");
        }
    }
}
