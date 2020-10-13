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

    solver::solver(euf::solver& ctx, theory_id id):
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

        smt_params_helper lpar(s().params());
        lp().settings().set_resource_limit(m_resource_limit);
        lp().settings().simplex_strategy() = static_cast<lp::simplex_strategy_enum>(lpar.arith_simplex_strategy());
        lp().settings().bound_propagation() = bound_prop_mode::BP_NONE != propagation_mode();
        lp().settings().enable_hnf() = lpar.arith_enable_hnf();
        lp().settings().print_external_var_name() = lpar.arith_print_ext_var_names();
        lp().set_track_pivoted_rows(lpar.arith_bprop_on_pivoted_rows());
        lp().settings().report_frequency = lpar.arith_rep_freq();
        lp().settings().print_statistics = lpar.arith_print_stats();
        lp().settings().cheap_eqs() = lpar.arith_cheap_eqs();

        // todo : do not use m_arith_branch_cut_ratio for deciding on cheap cuts
        unsigned branch_cut_ratio = get_config().m_arith_branch_cut_ratio;
        lp().set_cut_strategy(branch_cut_ratio);

        lp().settings().int_run_gcd_test() = get_config().m_arith_gcd_test;
        lp().settings().set_random_seed(get_config().m_random_seed);
        m_lia = alloc(lp::int_solver, *m_solver.get());
    }

    solver::~solver() {}

    void solver::asserted(literal l) {}
    
    euf::th_solver* solver::clone(sat::solver* s, euf::solver& ctx) { return nullptr;}
    bool solver::unit_propagate() { return false; }
    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {}
    void solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {}



    void solver::push_core() {
        TRACE("arith", tout << "push\n";);
        m_scopes.push_back(scope());
        scope& sc = m_scopes.back();
        sc.m_bounds_lim = m_bounds_trail.size();
        sc.m_asserted_qhead = m_asserted_qhead;
        sc.m_idiv_lim = m_idiv_terms.size();
        sc.m_asserted_atoms_lim = m_asserted_atoms.size();
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
        m_asserted_atoms.shrink(m_scopes[old_size].m_asserted_atoms_lim);
        m_asserted_qhead = m_scopes[old_size].m_asserted_qhead;
        m_underspecified.shrink(m_scopes[old_size].m_underspecified_lim);
        m_not_handled = m_scopes[old_size].m_not_handled;
        m_scopes.resize(old_size);
        lp().pop(num_scopes);
        // VERIFY(l_false != make_feasible());
        m_new_bounds.reset();
        m_to_check.reset();
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
#if 0
        rational bound;
        lp::constraint_index ci1, ci2, ci3, ci4;
        theory_var v1 = lp().local_to_external(vi1);
        theory_var v2 = lp().local_to_external(vi2);
        TRACE("arith", tout << "fixed: " << mk_pp(get_owner(v1), m) << " " << mk_pp(get_owner(v2), m) << "\n";);
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
        enode* x = get_enode(v1);
        enode* y = get_enode(v2);
        justification* js =
            ctx().mk_justification(
                ext_theory_eq_propagation_justification(
                    get_id(), ctx().get_region(), m_core.size(), m_core.c_ptr(), m_eqs.size(), m_eqs.c_ptr(), x, y, 0, nullptr));

        TRACE("arith",
            tout << "bound " << bound << "\n";
        for (auto c : m_core)
            ctx().display_detailed_literal(tout, c) << "\n";
        for (auto e : m_eqs)
            tout << mk_pp(e.first->get_owner(), m) << " = " << mk_pp(e.second->get_owner(), m) << "\n";
        tout << " ==> ";
        tout << mk_pp(x->get_owner(), m) << " = " << mk_pp(y->get_owner(), m) << "\n";
        );

        // parameters are TBD.
        //                    SASSERT(validate_eq(x, y));
        ctx().assign_eq(x, y, eq_justification(js));

#endif
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
        if (!lp().external_is_used(v)) {
            register_theory_var_in_lar_solver(v);
        }
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
            enode* n1 = var2enode(v);
            ensure_column(v);
            lp::column_index vj = lp().to_column_index(v);
            SASSERT(!vj.is_null());
            theory_var other = m_model_eqs.insert_if_not_there(v);
            if (other == v) {
                continue;
            }
            enode* n2 = var2enode(other);
            if (n1->get_root() == n2->get_root())
                continue;
            if (!lp().is_fixed(vj)) {
                vars.push_back(vj.index());
            }
            else if (!m_tmp_var_set.contains(other)) {
                lp::column_index other_j = lp().to_column_index(other);
                if (!lp().is_fixed(other_j)) {
                    m_tmp_var_set.insert(other);
                    vars.push_back(other_j.index());
                }
            }
        }
        if (!vars.empty()) {
            lp().random_update(vars.size(), vars.c_ptr());
        }
    }

    bool solver::assume_eqs() {
        TRACE("arith", display(tout););
        random_update();
        m_model_eqs.reset();
        theory_var sz = static_cast<theory_var>(get_num_vars());
        unsigned old_sz = m_assume_eq_candidates.size();
        unsigned num_candidates = 0;
        int start = s().rand()();
        for (theory_var i = 0; i < sz; ++i) {
            theory_var v = (i + start) % sz;
            enode* n1 = var2enode(v);
            ensure_column(v);
            if (!can_get_ivalue(v))
                continue;
            theory_var other = m_model_eqs.insert_if_not_there(v);
            TRACE("arith", tout << "insert: v" << v << " := " << get_value(v) << " found: v" << other << "\n";);
            if (other == v) {
                continue;
            }
            enode* n2 = var2enode(other);
            if (n1->get_root() != n2->get_root()) {
                TRACE("arith", tout << mk_pp(n1->get_expr(), m) << " = " << mk_pp(n2->get_expr(), m) << "\n";
                tout << mk_pp(n1->get_expr(), m) << " = " << mk_pp(n2->get_expr(), m) << "\n";
                tout << "v" << v << " = " << "v" << other << "\n";);
                m_assume_eq_candidates.push_back(std::make_pair(v, other));
                num_candidates++;
            }
        }

        if (num_candidates > 0) 
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
#if 0
            NOT_IMPLEMENTED_YET
            if (is_eq(v1, v2) && n1->get_root() != n2->get_root() && th.assume_eq(n1, n2)) {
                return true;
            }
#endif
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

    bool solver::has_delayed_constraints() const {
        return !m_asserted_atoms.empty();
    }

    sat::check_result solver::check() {
        reset_variable_values();
        IF_VERBOSE(12, verbose_stream() << "final-check " << lp().get_status() << "\n");
        lbool is_sat = l_true;
        SASSERT(lp().ax_is_correct());
        if (lp().get_status() != lp::lp_status::OPTIMAL) {
            is_sat = make_feasible();
        }
        auto st = sat::check_result::CR_DONE;

        switch (is_sat) {
        case l_true:
            TRACE("arith", /*display(tout);*/
                ctx.display(tout);
            );

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
        case l_false:
            get_infeasibility_explanation_and_set_conflict();
            return sat::check_result::CR_CONTINUE;
        case l_undef:
            TRACE("arith", tout << "check feasiable is undef\n";);
            return m.inc() ? sat::check_result::CR_CONTINUE : sat::check_result::CR_GIVEUP;;
        default:
            UNREACHABLE();
            break;
        }
        TRACE("arith", tout << "default giveup\n";);
        return sat::check_result::CR_GIVEUP;
    }

    nlsat::anum const& solver::nl_value(theory_var v, scoped_anum& r) {
        SASSERT(use_nra_model());
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
            //            SASSERT(lp().all_constraints_hold());
            return l_true;
        case lp::lp_status::TIME_EXHAUSTED:

        default:
            TRACE("arith", tout << "status treated as inconclusive: " << status << "\n";);
            // TENTATIVE_UNBOUNDED, UNBOUNDED, TENTATIVE_DUAL_UNBOUNDED, DUAL_UNBOUNDED, 
            // FLOATING_POINT_ERROR, TIME_EXAUSTED, ITERATIONS_EXHAUSTED, EMPTY, UNSTABLE
            return l_undef;
        }
    }

    lbool solver::check_lia() {
        TRACE("arith", );
        if (!m.inc()) {
            TRACE("arith", tout << "canceled\n";);
            return l_undef;
        }
        lbool lia_check = l_undef;
        if (!check_idiv_bounds()) {
            return l_false;
        }
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
#if 0
        if (core.size() < small_lemma_size() && eqs.empty()) {
            m_core2.reset();
            for (auto const& c : core) {
                m_core2.push_back(~c);
            }
            m_core2.push_back(lit);
            justification* js = nullptr;
            if (proofs_enabled()) {
                js = alloc(theory_lemma_justification, get_id(), ctx(), m_core2.size(), m_core2.c_ptr(),
                    params.size(), params.c_ptr());
            }
            ctx().mk_clause(m_core2.size(), m_core2.c_ptr(), js, CLS_TH_LEMMA, nullptr);
        }
        else {
            ctx().assign(
                lit, ctx().mk_justification(
                    ext_theory_propagation_justification(
                        get_id(), ctx().get_region(), core.size(), core.c_ptr(),
                        eqs.size(), eqs.c_ptr(), lit, params.size(), params.c_ptr())));
        }
#endif
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

        // lp().shrink_explanation_to_minimum(m_explanation); // todo, enable when perf is fixed
        ++m_num_conflicts;
        ++m_stats.m_conflicts;
        TRACE("arith", display(tout << "is-conflict: " << is_conflict << "\n"););
        for (auto const& ev : m_explanation) 
            set_evidence(ev.ci(), m_core, m_eqs);
        
        NOT_IMPLEMENTED_YET();
#if 0
        
        // SASSERT(validate_conflict(m_core, m_eqs));
        if (is_conflict) {
            ctx().set_conflict(
                ctx().mk_justification(
                    ext_theory_conflict_justification(
                        get_id(), ctx().get_region(),
                        m_core.size(), m_core.c_ptr(),
                        m_eqs.size(), m_eqs.c_ptr(), m_params.size(), m_params.c_ptr())));
        }
        else {
            for (auto const& eq : m_eqs) {
                m_core.push_back(th.mk_eq(eq.first->get_owner(), eq.second->get_owner(), false));
            }
            for (literal& c : m_core) {
                c.neg();
                ctx().mark_as_relevant(c);
            }
            TRACE("arith", ctx().display_literals_verbose(tout, m_core) << "\n";);
            // DEBUG_CODE(
            //     for (literal const& c : m_core) {
            //         if (ctx().get_assignment(c) == l_true) {
            //             TRACE("arith", ctx().display_literal_verbose(tout, c) << " is true\n";);
            //             SASSERT(false);
            //         }
            //     });   // TODO: this check seems to be too strict.
            // The lemmas can come in batches
            // and the same literal can appear in several lemmas in a batch: it becomes l_true
            // in earlier processing, but it was not so when the lemma was produced
            ctx().mk_th_axiom(get_id(), m_core.size(), m_core.c_ptr());
        }
#endif
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
        case equality_source: {
            SASSERT(m_equalities[idx].first != nullptr);
            SASSERT(m_equalities[idx].second != nullptr);
            m_eqs.push_back(m_equalities[idx]);
            break;
        }
        case definition_source: {
            // skip definitions (these are treated as hard constraints)
            break;
        }
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
            if (kv.m_value.is_zero()) {
                // continue
            }
            else if (kv.m_value.is_one()) {
                args.push_back(o);
            }
            else {
                args.push_back(a.mk_mul(a.mk_numeral(kv.m_value, is_int), o));
            }
        }
        if (!offset.is_zero()) {
            args.push_back(a.mk_numeral(offset, is_int));
        }
        switch (args.size()) {
        case 0:
            return app_ref(a.mk_numeral(rational::zero(), is_int), m);
        case 1:
            return app_ref(to_app(args[0].get()), m);
        default:
            return app_ref(a.mk_add(args.size(), args.c_ptr()), m);
        }
    }

    app_ref solver::mk_term(lp::lar_term const& term, bool is_int) {
        u_map<rational> coeffs;
        term2coeffs(term, coeffs);
        return coeffs2app(coeffs, rational::zero(), is_int);
    }

    rational solver::gcd_reduce(u_map<rational>& coeffs) {
        rational g(0);
        for (auto const& kv : coeffs) {
            g = gcd(g, kv.m_value);
        }
        if (g.is_zero())
            return rational::one();
        if (!g.is_one()) {
            for (auto& kv : coeffs) {
                kv.m_value /= g;
            }
        }
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
            for (const nla::lemma& l : m_nla_lemma_vector) {
                false_case_of_check_nla(l);
            }
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

}
