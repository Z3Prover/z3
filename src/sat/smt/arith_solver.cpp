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
        m_bp(*this, m_implied_bounds),
        a(m),
        m_bound_terms(m),
        m_bound_predicate(m)
    {
        m_solver = alloc(lp::lar_solver);

        lp().updt_params(ctx.s().params());
        lp().settings().set_resource_limit(m_resource_limit);
        lp().settings().bound_propagation() = bound_prop_mode::BP_NONE != propagation_mode();
        lp().settings().set_run_gcd_test(get_config().m_arith_gcd_test);
        lp().settings().set_random_seed(get_config().m_random_seed);
        
        m_lia = alloc(lp::int_solver, *m_solver.get());
    }

    solver::~solver() {
        del_bounds(0);
    }

    void solver::asserted(literal l) {
        force_push();
        m_asserted.push_back(l);
    }

    euf::th_solver* solver::clone(euf::solver& dst_ctx) {
        arith::solver* result = alloc(arith::solver, dst_ctx, get_id());
        unsigned_vector var2var;
        for (unsigned i = 0; i < result->get_num_vars(); ++i) 
            var2var.push_back(i);
        
        for (unsigned i = result->get_num_vars(); i < get_num_vars(); ++i) 
            var2var.push_back(result->mk_evar(ctx.copy(dst_ctx, var2enode(i))->get_expr()));

        result->m_bounds.resize(get_num_vars());
        unsigned nv = std::min(m_bounds.size(), get_num_vars());
        for (unsigned v = 0; v < nv; ++v) {
            auto w = var2var[v];
            for (auto* b : m_bounds[v]) {
                auto* b2 = result->mk_var_bound(b->get_lit(), w, b->get_bound_kind(), b->get_value());
                result->m_bounds[w].push_back(b2);
                result->m_bounds_trail.push_back(w);
                result->updt_unassigned_bounds(w, +1);
                result->m_bool_var2bound.insert(b->get_lit().var(), b2);
                result->m_new_bounds.push_back(b2);
            }
        }

        // clone rows into m_solver, m_nla, m_lia
        // NOT_IMPLEMENTED_YET();

        return result;        
    }

    bool solver::unit_propagate() {
        m_model_is_initialized = false;
        if (!m_solver->has_changed_columns() && !m_new_eq && m_new_bounds.empty() && m_asserted_qhead == m_asserted.size())
            return false;

        m_new_eq = false;
        flush_bound_axioms();
        propagate_nla();

        unsigned qhead = m_asserted_qhead;
        while (m_asserted_qhead < m_asserted.size() && !s().inconsistent() && m.inc()) {
            literal lit = m_asserted[m_asserted_qhead];
            api_bound* b = nullptr;
            CTRACE("arith", !m_bool_var2bound.contains(lit.var()), tout << "not found " << lit << "\n";);
            if (m_bool_var2bound.find(lit.var(), b)) 
                assert_bound(lit.sign() == b->get_lit().sign(), *b);
            ++m_asserted_qhead;
        }
        if (s().inconsistent())
            return true;

        lbool lbl = make_feasible();
        if (!m.inc())
            return false;

        switch (lbl) {
        case l_false:            
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
        api_bound* b = nullptr;
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

    void solver::propagate_bound(literal lit1, api_bound& b) {
        if (bound_prop_mode::BP_NONE == propagation_mode())
            return;

        bool is_true = !lit1.sign();
        lp_api::bound_kind k = b.get_bound_kind();
        theory_var v = b.get_var();
        inf_rational val = b.get_value(is_true);
        bool same_polarity = b.get_lit().sign() == lit1.sign();
        lp_bounds const& bounds = m_bounds[v];
        SASSERT(!bounds.empty());
        if (bounds.size() == 1) return;
        if (m_unassigned_bounds[v] == 0) return;
        bool v_is_int = b.is_int();
        literal lit2 = sat::null_literal;
        bool find_glb = (same_polarity == (k == lp_api::lower_t));
        TRACE("arith", tout << lit1 << " v" << v << " val " << val << " find_glb: " << find_glb << " is_true: " << is_true << " k: " << k << " is_lower: " << (k == lp_api::lower_t) << "\n";);
        if (find_glb) {
            rational glb;
            api_bound* lb = nullptr;
            for (api_bound* b2 : bounds) {
                if (b2 == &b) 
                    continue;
                rational const& val2 = b2->get_value();
                if (lb && glb >= val2)
                    continue;
                if (((same_polarity || v_is_int) ? val2 < val : val2 <= val)) {
                    lb = b2;
                    glb = val2;
                }
            }
            if (!lb) 
                return;
            bool sign = lb->get_bound_kind() != lp_api::lower_t;
            lit2 = lb->get_lit();
            if (sign)
                lit2.neg();
        }
        else {
            rational lub;
            api_bound* ub = nullptr;
            for (api_bound* b2 : bounds) {
                if (b2 == &b) 
                    continue;
                rational const& val2 = b2->get_value();
                if (ub && val2 >= lub)
                    continue;
                if (((same_polarity || v_is_int) ? val < val2 : val <= val2)) {
                    ub = b2;
                    lub = val2;
                }
            }
            if (!ub) 
                return;
            bool sign = ub->get_bound_kind() != lp_api::upper_t;
            lit2 = ub->get_lit();
            if (sign)
                lit2.neg();
        }
        updt_unassigned_bounds(v, -1);
        ++m_stats.m_bound_propagations2;
        reset_evidence();
        m_core.push_back(lit1);
        TRACE("arith", tout << lit2 << " <- " << m_core << "\n";);
        arith_proof_hint* ph = nullptr;
        if (ctx.use_drat()) {
            m_arith_hint.set_type(ctx, hint_type::farkas_h);
            m_arith_hint.add_lit(rational(1), lit1);
            m_arith_hint.add_lit(rational(1), ~lit2);
            ph = m_arith_hint.mk(ctx);
        }
        assign(lit2, m_core, m_eqs, ph); 
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

        reserve_bounds(v);

        if (m_unassigned_bounds[v] == 0 && !should_refine_bounds()) 
            return;

        TRACE("arith", tout << "lp bound v" << v << " " << be.kind() << " " << be.m_bound << "\n";);

        lp_bounds const& bounds = m_bounds[v];
        bool first = true;
        for (unsigned i = 0; i < bounds.size(); ++i) {
            api_bound* b = bounds[i];
            if (s().value(b->get_lit()) != l_undef) 
                continue;
            literal lit = is_bound_implied(be.kind(), be.m_bound, *b);
            if (lit == sat::null_literal) 
                continue;
            TRACE("arith", tout << "lp bound " << lit << " bound: " << *b << " first: " << first << "\n";);

            lp().settings().stats().m_num_of_implied_bounds++;
            if (first) {
                first = false;
                reset_evidence();
                m_explanation.clear();
                lp().explain_implied_bound(be, m_bp);
            }
            CTRACE("arith", m_unassigned_bounds[v] == 0, tout << "missed bound\n";);
            updt_unassigned_bounds(v, -1);
            TRACE("arith", for (auto lit : m_core) tout << lit << ": " << s().value(lit) << "\n";);
            DEBUG_CODE(for (auto lit : m_core) { VERIFY(s().value(lit) == l_true); });
            ++m_stats.m_bound_propagations1;
            assign(lit, m_core, m_eqs, explain(hint_type::bound_h, lit));
        }

        if (should_refine_bounds() && first)
            refine_bound(v, be);
    }

    literal solver::is_bound_implied(lp::lconstraint_kind k, rational const& value, api_bound const& b) const {
        if ((k == lp::LE || k == lp::LT) && b.get_bound_kind() == lp_api::upper_t && value <= b.get_value()) {
            TRACE("arith", tout << "v <= value <= b.get_value() => v <= b.get_value() \n";);
            return b.get_lit();  
        }
        if ((k == lp::GE || k == lp::GT) && b.get_bound_kind() == lp_api::lower_t && b.get_value() <= value) {
            TRACE("arith", tout << "b.get_value() <= value <= v => b.get_value() <= v \n";);
            return b.get_lit();
        }
        if (k == lp::LE && b.get_bound_kind() == lp_api::lower_t && value < b.get_value()) {
            TRACE("arith", tout << "v <= value < b.get_value() => v < b.get_value()\n";);
            return ~b.get_lit();
        }
        if (k == lp::LT && b.get_bound_kind() == lp_api::lower_t && value <= b.get_value()) {
            TRACE("arith", tout << "v < value <= b.get_value() => v < b.get_value()\n";);
            return ~b.get_lit();
        }
        if (k == lp::GE && b.get_bound_kind() == lp_api::upper_t && b.get_value() < value) {
            TRACE("arith", tout << "b.get_value() < value <= v => b.get_value() < v\n";);
            return ~b.get_lit();
        }
        if (k == lp::GT && b.get_bound_kind() == lp_api::upper_t && b.get_value() <= value) {
            TRACE("arith", tout << "b.get_value() <= value < v => b.get_value() < v\n";);
            return ~b.get_lit();
        }
        return sat::null_literal;
    }


    void solver::consume(rational const& v, lp::constraint_index j) {
        set_evidence(j);
        m_explanation.add_pair(j, v);
    }

    void solver::add_equality(lpvar j, rational const& k, lp::explanation const& exp) {
        TRACE("arith", tout << "equality " << j << " " << k << "\n");
        theory_var v;
        if (k == 1)
            v = m_one_var;
        else if (k == 0)
            v = m_zero_var;
        else if (!m_value2var.find(k, v))
            return;
        theory_var w = lp().local_to_external(j);
        if (w < 0)
            return;
        lpvar i = register_theory_var_in_lar_solver(v);
        add_eq(i, j, exp, true);
    }

    bool solver::add_eq(lpvar u, lpvar v, lp::explanation const& e, bool is_fixed) {
        if (s().inconsistent())
            return false;
        theory_var uv = lp().local_to_external(u); // variables that are returned should have external representations
        theory_var vv = lp().local_to_external(v); // so maybe better to have them already transformed to external form
        if (uv == euf::null_theory_var)
            return false;
        if (vv == euf::null_theory_var)
            return false;
        if (is_equal(uv, vv))
            return false;
        enode* n1 = var2enode(uv);
        enode* n2 = var2enode(vv);
        expr* e1 = n1->get_expr();
        expr* e2 = n2->get_expr();
        if (!is_fixed && !a.is_numeral(e1) && !a.is_numeral(e2) && (m.is_ite(e1) || m.is_ite(e2)))
            return false;
        if (e1->get_sort() != e2->get_sort())
            return false;
        reset_evidence();
        for (auto ev : e)
            set_evidence(ev.ci());
        auto* ex = explain_implied_eq(e, n1, n2);
        auto* jst = euf::th_explain::propagate(*this, m_core, m_eqs, n1, n2, ex); 
        ctx.propagate(n1, n2, jst->to_index());
        return true;
    }

    bool solver::bound_is_interesting(unsigned vi, lp::lconstraint_kind kind, const rational& bval) const {
        theory_var v = lp().local_to_external(vi);
        if (v == euf::null_theory_var)
            return false;

        if (should_refine_bounds())
            return true;

        if (m_bounds.size() <= static_cast<unsigned>(v) || m_unassigned_bounds[v] == 0)
            return false;

        for (api_bound* b : m_bounds[v])
            if (s().value(b->get_lit()) == l_undef && sat::null_literal != is_bound_implied(kind, bval, *b))
                return true;

        return false;
    }

    void solver::refine_bound(theory_var v, const lp::implied_bound& be) {
        lpvar vi = be.m_j;
        if (lp().column_has_term(vi))
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
        assign(bound, m_core, m_eqs, explain(hint_type::farkas_h, bound));
    }


    void solver::assert_bound(bool is_true, api_bound& b) {
        lp::constraint_index ci = b.get_constraint(is_true);
        lp().activate(ci);
        TRACE("arith", tout << b << " " << is_infeasible() << "\n";);
        if (is_infeasible()) 
            return;
        lp::lconstraint_kind k = bound2constraint_kind(b.is_int(), b.get_bound_kind(), is_true);
        if (k == lp::LT || k == lp::LE) 
            ++m_stats.m_assert_lower;
        else 
            ++m_stats.m_assert_upper;
        inf_rational value = b.get_value(is_true);
        if (propagate_eqs() && value.is_rational()) 
            propagate_eqs(b.column_index(), ci, k, b, value.get_rational());
#if 0
        if (propagation_mode() != BP_NONE)
            lp().add_column_rows_to_touched_rows(b.tv().id());
#endif

    }

    void solver::propagate_eqs(lp::lpvar t, lp::constraint_index ci1, lp::lconstraint_kind k, api_bound& b, rational const& value) {
        u_dependency* dep;
        auto& dm = lp().dep_manager();
        if (k == lp::GE && set_lower_bound(t, ci1, value) && has_upper_bound(t, dep, value)) {
            fixed_var_eh(b.get_var(), dm.mk_join(dm.mk_leaf(ci1), dep), value);
        }
        else if (k == lp::LE && set_upper_bound(t, ci1, value) && has_lower_bound(t, dep, value)) {
            fixed_var_eh(b.get_var(), dm.mk_join(dm.mk_leaf(ci1), dep), value);
        }
    }


    bool solver::set_bound(lp::lpvar tv, lp::constraint_index ci, rational const& v, bool is_lower) {
        if (lp().column_has_term(tv)) {
            auto& vec = is_lower ? m_lower_terms : m_upper_terms;
            if (vec.size() <= tv) {
                vec.resize(tv + 1, constraint_bound(UINT_MAX, rational()));
            }
            constraint_bound& b = vec[tv];
            if (b.first == UINT_MAX || (is_lower ? b.second < v : b.second > v)) {
                TRACE("arith", tout << "tighter bound " << tv << "\n";);
                m_history.push_back(vec[tv]);
                ctx.push(history_trail<constraint_bound>(vec, tv, m_history));
                b.first = ci;
                b.second = v;
            }
            return true;
        }
        else {
            // m_solver already tracks bounds on proper variables, but not on terms.
            bool is_strict = false;
            rational b;
            u_dependency* dep = nullptr;
            if (is_lower) {
                return lp().has_lower_bound(tv, dep, b, is_strict) && !is_strict && b == v;
            }
            else {
                return lp().has_upper_bound(tv, dep, b, is_strict) && !is_strict && b == v;
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
            ptr_addr_hashtable<api_bound> visited;
            for (unsigned i = 0; i < atoms.size(); ++i) {
                api_bound* a1 = atoms[i];
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
            api_bound* a = *it;
            if (a->get_bound_kind() == kind) return it;
        }
        return end;
    }

    lp_bounds::iterator solver::next_inf(
        api_bound* a1,
        lp_api::bound_kind kind,
        iterator it,
        iterator end,
        bool& found_compatible) {
        rational const& k1(a1->get_value());
        iterator result = end;
        found_compatible = false;
        for (; it != end; ++it) {
            api_bound* a2 = *it;
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
        api_bound* a1,
        lp_api::bound_kind kind,
        iterator it,
        iterator end,
        bool& found_compatible) {
        rational const& k1(a1->get_value());
        found_compatible = false;
        for (; it != end; ++it) {
            api_bound* a2 = *it;
            if (a1 == a2)
                continue;
            if (a2->get_bound_kind() != kind)
                continue;
            rational const& k2(a2->get_value());
            found_compatible = true;
            if (k1 < k2) 
                return it;
        }
        return end;
    }

    void solver::dbg_finalize_model(model& mdl) {
        if (m_not_handled)
            return;

        // this is already handled in general in euf_model.cpp
        return;
        bool found_bad = false;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            if (!is_bool(v))
                continue;
            euf::enode* n = var2enode(v);
            api_bound* b = nullptr;
            if (!m_bool_var2bound.find(n->bool_var(), b)) {
                IF_VERBOSE(0, verbose_stream() << "no boolean variable\n";);
                continue;
            }
            lbool value = n->value();
            expr_ref eval = mdl(var2expr(v));
            if (m.is_true(eval) && l_false == value)
                found_bad = true;
            if (m.is_false(eval) && l_true == value)
                found_bad = true;

            if (b->get_lit().sign())
                value = ~value;
            if (!found_bad && value == get_phase(n->bool_var()))
                continue;

            TRACE("arith", ctx.display_validation_failure(tout << *b << "\n", mdl, n));
            IF_VERBOSE(0, ctx.display_validation_failure(verbose_stream() << *b << "\n", mdl, n));
            UNREACHABLE();
        }
    }

    bool solver::get_value(euf::enode* n, expr_ref& value) {
        theory_var v = n->get_th_var(get_id());
        expr* o = n->get_expr();

        if (m.is_value(n->get_root()->get_expr())) {
            value = n->get_root()->get_expr();
        }
        else if (use_nra_model() && lp().external_to_local(v) != lp::null_lpvar) {
            anum const& an = nl_value(v, m_nla->tmp1());
            if (a.is_int(o) && !m_nla->am().is_int(an))
                value = a.mk_numeral(rational::zero(), a.is_int(o));
            else
                value = a.mk_numeral(m_nla->am(), nl_value(v, m_nla->tmp1()), a.is_int(o));
        }
        else if (v != euf::null_theory_var) {
            rational r = get_value(v);
            TRACE("arith", tout << mk_pp(o, m) << " v" << v << " := " << r << "\n";);
            SASSERT("integer variables should have integer values: " && (ctx.get_config().m_arith_ignore_int || !a.is_int(o) || r.is_int() || m_not_handled != nullptr || m.limit().is_canceled()));
            if (a.is_int(o) && !r.is_int())
                r = floor(r);
            value = a.mk_numeral(r, o->get_sort());
        }
        else
            return false;

        return true;
    }


    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        expr_ref value(m);
        expr* o = n->get_expr();
        if (get_value(n, value))
            ;
        else if (a.is_arith_expr(o) && reflect(o)) {
            expr_ref_vector args(m);
            for (auto* arg : *to_app(o)) {
                if (m.is_value(arg))
                    args.push_back(arg);
                else
                    args.push_back(values.get(ctx.get_enode(arg)->get_root_id()));
            }
            value = m.mk_app(to_app(o)->get_decl(), args.size(), args.data());
            ctx.get_rewriter()(value);
        }
        else
            value = mdl.get_fresh_value(n->get_sort());
        mdl.register_value(value);
        values.set(n->get_root_id(), value);
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        theory_var v = n->get_th_var(get_id());
        if (v == euf::null_theory_var && !a.is_arith_expr(n->get_expr()))
            return false;
        expr* e = n->get_expr();
        if (a.is_arith_expr(e) && to_app(e)->get_num_args() > 0) {
            for (auto* arg : *to_app(e)) {
                auto* earg = expr2enode(arg);
                if (earg)
                    dep.add(n, earg);
            }
        }
        else {
            dep.insert(n, nullptr); 
        }
        return true;
    }

    void solver::push_core() {
        TRACE("arith_verbose", tout << "push\n";);
        m_scopes.push_back(scope());
        scope& sc = m_scopes.back();
        sc.m_bounds_lim = m_bounds_trail.size();
        sc.m_asserted_qhead = m_asserted_qhead;
        sc.m_asserted_lim = m_asserted.size();
        lp().push();
        if (m_nla)
            m_nla->push();
        th_euf_solver::push_core();
    }

    void solver::pop_core(unsigned num_scopes) {
        TRACE("arith", tout << "pop " << num_scopes << "\n";);
        unsigned old_size = m_scopes.size() - num_scopes;
        del_bounds(m_scopes[old_size].m_bounds_lim);
        m_asserted.shrink(m_scopes[old_size].m_asserted_lim);
        m_asserted_qhead = m_scopes[old_size].m_asserted_qhead;
        m_scopes.resize(old_size);
        lp().pop(num_scopes);
        m_new_bounds.reset();
        if (m_nla)
            m_nla->pop(num_scopes);
        TRACE("arith_verbose", tout << "num scopes: " << num_scopes << " new scope level: " << m_scopes.size() << "\n";);
        th_euf_solver::pop_core(num_scopes);
    }

    void solver::del_bounds(unsigned old_size) {
        for (unsigned i = m_bounds_trail.size(); i-- > old_size; ) {
            unsigned v = m_bounds_trail[i];
            api_bound* b = m_bounds[v].back();
            m_bool_var2bound.erase(b->get_lit().var());
            // del_use_lists(b);
            dealloc(b);
            m_bounds[v].pop_back();
        }
        m_bounds_trail.shrink(old_size);
    }

    void solver::report_equality_of_fixed_vars(unsigned vi1, unsigned vi2) {
        rational bound;
        u_dependency* ci1 = nullptr, *ci2 = nullptr, *ci3 = nullptr, *ci4 = nullptr;
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
        m_explanation.clear();
        auto& dm = lp().dep_manager();
        auto* d = dm.mk_join(dm.mk_join(ci1, ci2), dm.mk_join(ci3, ci4));
        for (auto ci : lp().flatten(d))
            consume(rational::one(), ci);
        enode* x = var2enode(v1);
        enode* y = var2enode(v2);
        auto* ex = explain_implied_eq(m_explanation, x, y);
        auto* jst = euf::th_explain::propagate(*this, m_core, m_eqs, x, y, ex);
        ctx.propagate(x, y, jst->to_index());
    }

    bool solver::is_equal(theory_var x, theory_var y) const {
        return x == y || var2enode(x)->get_root() == var2enode(y)->get_root();
    }

    bool solver::has_upper_bound(lpvar vi, u_dependency*& ci, rational const& bound) { return has_bound(vi, ci, bound, false); }

    bool solver::has_lower_bound(lpvar vi, u_dependency*& ci, rational const& bound) { return has_bound(vi, ci, bound, true); }

    bool solver::has_bound(lpvar vi, u_dependency*& dep, rational const& bound, bool is_lower) {
        if (lp().column_has_term(vi)) {
            theory_var v = lp().local_to_external(vi);
            rational val;
            TRACE("arith", tout << lp().get_variable_name(vi) << " " << v << "\n";);
            if (v != euf::null_theory_var && a.is_numeral(var2expr(v), val) && bound == val) {
                dep = nullptr;
                return bound == val;
            }

            auto& vec = is_lower ? m_lower_terms : m_upper_terms;
            if (vec.size() > vi) {
                auto& [ci, coeff] = vec[vi];
                if (ci == UINT_MAX)
                    return false;
                dep = lp().dep_manager().mk_leaf(ci);
                return bound == coeff;
            }
            else {
                return false;
            }
        }
        else {
            bool is_strict = false;
            rational b;
            if (is_lower) {
                return lp().has_lower_bound(vi, dep, b, is_strict) && b == bound && !is_strict;
            }
            else {
                return lp().has_upper_bound(vi, dep, b, is_strict) && b == bound && !is_strict;
            }
        }
    }

    void solver::updt_unassigned_bounds(theory_var v, int inc) {
        TRACE("arith_verbose", tout << "v" << v << " " << m_unassigned_bounds[v] << " += " << inc << "\n";);
        ctx.push(vector_value_trail<unsigned, false>(m_unassigned_bounds, v));
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

    void solver::init_model() {
        if (m.inc() && m_solver.get() && get_num_vars() > 0) {
            TRACE("arith", display(tout << "update variable values\n"););
            ctx.push(value_trail<bool>(m_model_is_initialized));
            m_model_is_initialized = true;
            lp().init_model();
        }
    }

    lbool solver::get_phase(bool_var v) {
        api_bound* b;
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

    bool solver::is_registered_var(theory_var v) const {
        return v != euf::null_theory_var && lp().external_is_used(v);
    }

    void solver::ensure_column(theory_var v) {
        SASSERT(!is_bool(v));
        if (!lp().external_is_used(v))
            register_theory_var_in_lar_solver(v);
    }

    lp::impq solver::get_ivalue(theory_var v) const {
        SASSERT(is_registered_var(v));
        return m_solver->get_column_value(get_column(v));
    }

    lp::lpvar solver::get_column(theory_var v) const {
        SASSERT(is_registered_var(v));
        return m_solver->external_to_local(v);
   }

    rational solver::get_value(theory_var v) const {
        return is_registered_var(v) ? m_solver->get_value(get_column(v)) : rational::zero();      
    }

    void solver::random_update() {
        if (m_nla)
            return;
        TRACE("arith", tout << s().scope_lvl() << "\n"; tout.flush(););
        m_tmp_var_set.reset();
        m_model_eqs.reset();
        svector<lpvar> vars;
        theory_var sz = static_cast<theory_var>(get_num_vars());
        for (theory_var v = 0; v < sz; ++v) {
            if (is_bool(v))
                continue;
            ensure_column(v);
            lp::lpvar  vj = lp().external_to_local(v);
            SASSERT(vj != lp::null_lpvar);
            theory_var other = m_model_eqs.insert_if_not_there(v);
            if (is_equal(v, other))
                continue;
            if (!lp().column_is_fixed(vj))
                vars.push_back(vj);
            else if (!m_tmp_var_set.contains(other)) {
                lp::lpvar other_j = lp().external_to_local(other);
                if (!lp().column_is_fixed(other_j)) {
                    m_tmp_var_set.insert(other);
                    vars.push_back(other_j);
                }
            }
        }
        if (!vars.empty())
            lp().random_update(vars.size(), vars.data());
    }

    bool solver::include_func_interp(enode* n) const {
        func_decl* d = n->get_decl();
        return d && include_func_interp(d);
    }

    bool solver::assume_eqs() {
        if (delayed_assume_eqs())
            return true;

        TRACE("arith", display(tout););
        random_update();
        m_model_eqs.reset();
        theory_var sz = static_cast<theory_var>(get_num_vars());
        unsigned old_sz = m_assume_eq_candidates.size();
        int start = s().rand()();
        for (theory_var i = 0; i < sz; ++i) {
            theory_var v = (i + start) % sz;
            if (is_bool(v))
                continue;
            if (!ctx.is_shared(var2enode(v)))
                continue;
            ensure_column(v);
            if (!is_registered_var(v))
                continue;
            theory_var other = m_model_eqs.insert_if_not_there(v);
            TRACE("arith", tout << "insert: v" << v << " := " << get_value(v) << " found: v" << other << "\n";);
            if (!is_equal(other, v))
                m_assume_eq_candidates.push_back({ v, other });
        }

        if (m_assume_eq_candidates.size() > old_sz)
            ctx.push(restore_vector(m_assume_eq_candidates, old_sz));

        return delayed_assume_eqs();
    }

    bool solver::delayed_assume_eqs() {
        if (m_assume_eq_head == m_assume_eq_candidates.size())
            return false;

        ctx.push(value_trail<unsigned>(m_assume_eq_head));
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
            literal eq = eq_internalize(n1, n2);
            ctx.mark_relevant(eq);
            switch (s().value(eq)) {
            case l_true:
                break;
            case l_undef:
                return true;
            case l_false:
                mk_diseq_axiom(v1, v2);
                return true;
            }
        }
        return false;
    }

    bool solver::use_nra_model() {
        return m_nla && m_use_nra_model && m_nla->use_nra_model();
    }

    bool solver::is_eq(theory_var v1, theory_var v2) {        
        if (use_nra_model()) {
            return m_nla->am().eq(nl_value(v1, m_nla->tmp1()), nl_value(v2, m_nla->tmp2()));
        }
        else {
            return get_ivalue(v1) == get_ivalue(v2);
        }
    }

    sat::check_result solver::check() {
        force_push();
        m_model_is_initialized = false;
        IF_VERBOSE(12, verbose_stream() << "final-check " << lp().get_status() << "\n");
        SASSERT(lp().ax_is_correct());

        m_use_nra_model = false;

        if (!lp().is_feasible() || lp().has_changed_columns()) {
            switch (make_feasible()) {
            case l_false:
                get_infeasibility_explanation_and_set_conflict();
                return sat::check_result::CR_CONTINUE;
            case l_undef:
                TRACE("arith", tout << "check feasible is undef\n";);
                return sat::check_result::CR_CONTINUE;
            case l_true:
                break;
            default:
                UNREACHABLE();
            }
        }

        auto st = sat::check_result::CR_DONE;
        bool int_undef = false;

        TRACE("arith", ctx.display(tout););

        switch (check_lia()) {
        case l_true:
            break;
        case l_false:
            return sat::check_result::CR_CONTINUE;
        case l_undef:
            TRACE("arith", tout << "check-lia giveup\n";);
            int_undef = true;            
            st = sat::check_result::CR_CONTINUE;
            break;
        }

        if (!check_delayed_eqs())
            return sat::check_result::CR_CONTINUE;

        switch (check_nla()) {
        case l_true:
            m_use_nra_model = true;
            break;
        case l_false:
            return sat::check_result::CR_CONTINUE;
        case l_undef:
            TRACE("arith", tout << "check-nra giveup\n";);
            st = sat::check_result::CR_GIVEUP;
            break;
        }
            
        if (assume_eqs()) {
            ++m_stats.m_assume_eqs;
            return sat::check_result::CR_CONTINUE;
        }

        if (!check_delayed_eqs())
            return sat::check_result::CR_CONTINUE;

        if (!int_undef && !check_bv_terms())
            return sat::check_result::CR_CONTINUE;

        if (ctx.get_config().m_arith_ignore_int && int_undef)
            return sat::check_result::CR_GIVEUP;
        if (m_not_handled != nullptr) {
            TRACE("arith", tout << "unhandled operator " << mk_pp(m_not_handled, m) << "\n";);
            return sat::check_result::CR_GIVEUP;
        }
        return st;
    }

    nlsat::anum const& solver::nl_value(theory_var v, scoped_anum& r) const {
        SASSERT(m_nla);
        SASSERT(m_nla->use_nra_model());
        auto t = get_column(v);
        if (!lp().column_has_term(t)) {
            m_nla->am().set(r, m_nla->am_value(t));
        }
        else {
            m_todo_terms.push_back(std::make_pair(t, rational::one()));
            TRACE("nl_value", tout << "v" << v << " " << t << "\n";);
            TRACE("nl_value", tout << "v" << v << " := w" << t << "\n";
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
                for (lp::lar_term::ival arg : term) {
                    auto wi = arg.j();
                    c1 = arg.coeff() * wcoeff;
                    if (lp().column_has_term(wi)) {
                        m_todo_terms.push_back(std::make_pair(wi, c1));
                    }
                    else {
                        m_nla->am().set(r1, c1.to_mpq());
                        m_nla->am().mul(m_nla->am_value(wi), r1, r1);
                        m_nla->am().add(r1, r, r);
                    }
                }
            }
        }
        return r;
    }

    lbool solver::make_feasible() {
        TRACE("pcs", tout << lp().constraints(););
        auto status = lp().find_feasible_solution();
        TRACE("arith_verbose", display(tout););
        TRACE("arith", tout << status << "\n");
        switch (status) {
        case lp::lp_status::INFEASIBLE:
            return l_false;
        case lp::lp_status::FEASIBLE:
        case lp::lp_status::OPTIMAL:
        case lp::lp_status::UNBOUNDED:
            SASSERT(!lp().has_changed_columns());
            return l_true;
        case lp::lp_status::TIME_EXHAUSTED:
        default:
            TRACE("arith", tout << "status treated as inconclusive: " << status << "\n";);
            return l_undef;
        }
    }

    bool solver::check_delayed_eqs() {
        bool found_diseq = false;
        if (m_delayed_eqs.empty())
            return true;
        force_push();
        for (unsigned i = 0; i < m_delayed_eqs.size(); ++i) {
            auto p = m_delayed_eqs[i];
            auto const& e = p.first;
            if (p.second)
                new_eq_eh(e);
            else if (is_eq(e.v1(), e.v2())) {
                mk_diseq_axiom(e.v1(), e.v2());
                TRACE("arith", tout << mk_bounded_pp(e.eq(), m) << " " << use_nra_model() << "\n");
                found_diseq = true;
                break;
            }
        }        
        return !found_diseq;
    }

    lbool solver::check_lia() {
        TRACE("arith", );
        if (!m.inc())
            return l_undef;
        lbool lia_check = l_undef;
        if (!check_idiv_bounds())
            return l_false;

        auto cr = m_lia->check(&m_explanation);
        if (cr != lp::lia_move::sat && ctx.get_config().m_arith_ignore_int) 
            return l_undef;

        switch (cr) {
        case lp::lia_move::sat:
            lia_check = l_true;
            break;

        case lp::lia_move::branch: {
            TRACE("arith", tout << "branch\n";);
            app_ref b(m);
            bool u = m_lia->is_upper();
            auto const& k = m_lia->offset();
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
            break;
        }
        case lp::lia_move::cut: {
            TRACE("arith", tout << "cut\n";);
            ++m_stats.m_cuts;
            // m_explanation implies term <= k
            reset_evidence();
            for (auto ev : m_explanation)
                set_evidence(ev.ci());
            // The call mk_bound() can set the m_infeasible_column in lar_solver
            // so the explanation is safer to take before this call.
            app_ref b = mk_bound(m_lia->get_term(), m_lia->offset(), !m_lia->is_upper());
            IF_VERBOSE(4, verbose_stream() << "cut " << b << "\n");
            literal lit = expr2literal(b);
            assign(lit, m_core, m_eqs, explain(hint_type::cut_h, lit));
            lia_check = l_false;
            break;
        }
        case lp::lia_move::conflict:
            TRACE("arith", tout << "conflict\n";);
            // ex contains unsat core
            set_conflict(hint_type::cut_h);
            return l_false;
        case lp::lia_move::undef:
            TRACE("arith", tout << "lia undef\n";);
            lia_check = l_undef;
            break;
        case lp::lia_move::continue_with_check:
            TRACE("arith", tout << "continue-with-check\n");
            lia_check = l_false;
            break;
        default:
            UNREACHABLE();
        }
        return lia_check;
    }

    void solver::assign(literal lit, literal_vector const& core, svector<enode_pair> const& eqs, euf::th_proof_hint const* pma) {        
        if (core.size() < small_lemma_size() && eqs.empty()) {
            m_core2.reset();
            for (auto const& c : core)
                m_core2.push_back(~c);
            m_core2.push_back(lit);
            add_redundant(m_core2, pma);
        }
        else {
            auto* jst = euf::th_explain::propagate(*this, core, eqs, lit, pma);
            ctx.propagate(lit, jst->to_index());
        }
    }

    void solver::get_infeasibility_explanation_and_set_conflict() {
        m_explanation.clear();
        lp().get_infeasibility_explanation(m_explanation);
        set_conflict(hint_type::farkas_h);
    }

    void solver::set_conflict(hint_type ty) {
        literal_vector core;
        set_conflict_or_lemma(ty, core, true);
    }

    void solver::set_conflict_or_lemma(hint_type ty, literal_vector const& core, bool is_conflict) {
        reset_evidence();
        m_core.append(core);
        for (auto ev : m_explanation)
            set_evidence(ev.ci());
        
        TRACE("arith_conflict",
            tout << "Lemma - " << (is_conflict ? "conflict" : "propagation") << "\n";
            for (literal c : m_core) tout << c << ": " << literal2expr(c) << " := " << s().value(c) << "\n";
            for (auto p : m_eqs) tout << ctx.bpp(p.first) << " == " << ctx.bpp(p.second) << "\n";);

        if (ctx.get_config().m_arith_validate)
            VERIFY(validate_conflict());

        if (is_conflict) {
            DEBUG_CODE(
                for (literal c : m_core) VERIFY(s().value(c) == l_true);
                for (auto p : m_eqs) VERIFY(p.first->get_root() == p.second->get_root()));                       
            ++m_num_conflicts;
            ++m_stats.m_conflicts;
            auto* hint = explain_conflict(ty, m_core, m_eqs);
            ctx.set_conflict(euf::th_explain::conflict(*this, m_core, m_eqs, hint));
        }
        else {
            for (auto const& eq : m_eqs)
                m_core.push_back(ctx.mk_literal(m.mk_eq(eq.first->get_expr(), eq.second->get_expr())));
            for (literal& c : m_core)
                c.neg();

            // it is possible if multiple lemmas are added at the same time.
            if (any_of(m_core, [&](literal c) { return s().value(c) == l_true; }))
                return;
            
            add_redundant(m_core, explain(ty));
        }
    }

    bool solver::is_infeasible() const {
        return lp().get_status() == lp::lp_status::INFEASIBLE;
    }

    void solver::set_evidence(lp::constraint_index idx) {
        if (idx == UINT_MAX) {
            return;
        }
        switch (m_constraint_sources[idx]) {
        case inequality_source: {
            literal lit = m_inequalities[idx];
            SASSERT(lit != sat::null_literal);
            m_core.push_back(lit);
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
        if (lower_bound) 
            atom = a.mk_ge(t, a.mk_numeral(offset, is_int));        
        else 
            atom = a.mk_le(t, a.mk_numeral(offset, is_int));        

        TRACE("arith", tout << t << ": " << atom << "\n";
        lp().print_term(term, tout << "bound atom: ") << (lower_bound ? " >= " : " <= ") << k << "\n";);
        mk_literal(atom);
        return atom;
    }

    void solver::term2coeffs(lp::lar_term const& term, u_map<rational>& coeffs) {
        term2coeffs(term, coeffs, rational::one());
    }

    void solver::term2coeffs(lp::lar_term const& term, u_map<rational>& coeffs, rational const& coeff) {
        TRACE("arith", lp().print_term(term, tout) << "\n";);
        for (lp::lar_term::ival ti : term) {
            theory_var w;
            auto tv = ti.j();
            if (lp().column_has_term(tv)) {
                lp::lar_term const& term1 = lp().get_term(tv);
                rational coeff2 = coeff * ti.coeff();
                term2coeffs(term1, coeffs, coeff2);
                continue;
            }
            else {
                w = lp().local_to_external(tv);
                SASSERT(w >= 0);
                TRACE("arith", tout << tv << ": " << w << "\n";);
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

        return app_ref(a.mk_add(args.size(), args.data()), m);        
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
        for (auto const& ineq : m_lemma.ineqs()) 
            core.push_back(~mk_ineq_literal(ineq));
        set_conflict_or_lemma(hint_type::nla_h, core, false);
    }
    
    sat::literal solver::mk_ineq_literal(nla::ineq const& ineq) {
        bool is_lower = true, sign = true, is_eq = false;
        switch (ineq.cmp()) {
        case lp::LE: is_lower = false; sign = false; break;
        case lp::LT: is_lower = true;  sign = true;  break;
        case lp::GE: is_lower = true;  sign = false; break;
        case lp::GT: is_lower = false; sign = true;  break;
        case lp::EQ: is_eq = true;     sign = false; break;
        case lp::NE: is_eq = true;     sign = true;  break;
        default: UNREACHABLE();
        }
        // TBD utility: lp::lar_term term = mk_term(ineq.m_poly);
        // then term is used instead of ineq.m_term
        sat::literal lit;
        if (is_eq) 
            lit = mk_eq(ineq.term(), ineq.rs());
        else 
            lit = ctx.expr2literal(mk_bound(ineq.term(), ineq.rs(), is_lower));

        TRACE("arith", tout << "is_lower: " << is_lower << " sign " << sign << " " << ctx.literal2expr(lit) << "\n";);
        return sign ? ~lit : lit;                                            
    }


    lbool solver::check_nla() {
        if (!m.inc()) {
            TRACE("arith", tout << "canceled\n";);
            return l_undef;
        }
        CTRACE("arith", !m_nla, tout << "no nla\n";);
        if (!m_nla) 
            return l_true;
        if (!m_nla->need_check())
            return l_true;

        lbool r = m_nla->check();
        switch (r) {
        case l_false:
            add_lemmas();
            break;
        case l_true:
            break;
        case l_undef:
            break;
        }
        TRACE("arith", tout << "nla " << r << "\n");
        return r;
    }

    void solver::add_lemmas() {
        if (m_nla->should_check_feasible()) {
            auto is_sat = make_feasible();
            if (l_false == is_sat) {
                get_infeasibility_explanation_and_set_conflict();
                return;
            }
        }
        for (auto const& ineq : m_nla->literals()) {
            auto lit = mk_ineq_literal(ineq);
            if (s().value(lit) == l_true)
                continue;
            ctx.mark_relevant(lit);
            s().set_phase(lit);
            // verbose_stream() << lit << ":= " << s().value(lit) << "\n";
            // force trichotomy axiom for equality literals
            if (ineq.cmp() == lp::EQ && false) {
                nla::lemma l;
                l.push_back(ineq);
                l.push_back(nla::ineq(lp::LT, ineq.term(), ineq.rs()));
                l.push_back(nla::ineq(lp::GT, ineq.term(), ineq.rs()));
                false_case_of_check_nla(l);
            }
        }
        for (const nla::lemma& l : m_nla->lemmas())
            false_case_of_check_nla(l);
        if (!propagate_eqs()) 
            return;
        for (auto const& [v,k,e] : m_nla->fixed_equalities())
            add_equality(v, k, e);
        for (auto const& [i,j,e] : m_nla->equalities())
            add_eq(i,j,e,false);
    }

    void solver::propagate_nla() {
        if (m_nla) {
            m_nla->propagate();
            add_lemmas();
            lp().collect_more_rows_for_lp_propagation();
        }
    }

    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) {
        auto& jst = euf::th_explain::from_index(idx);
        ctx.get_th_antecedents(l, jst, r, probing);
    }

    bool solver::include_func_interp(func_decl* f) const {
        SASSERT(f->get_family_id() == get_id());
        switch (f->get_decl_kind()) {
        case OP_ADD:
        case OP_SUB:
        case OP_UMINUS:
        case OP_MUL:
        case OP_LE:
        case OP_LT:
        case OP_GE:
        case OP_GT:
        case OP_MOD:
        case OP_REM:
        case OP_DIV:
        case OP_IDIV:
        case OP_POWER:
        case OP_IS_INT:
        case OP_TO_INT:
        case OP_TO_REAL:
        case OP_NUM:
            return false;
        default:
            return true;            
        }
    }
}
