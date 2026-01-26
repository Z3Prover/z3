/*++
  Copyright (c) 2025 Microsoft Corporation


  vanishing(v, p) = (q, r) with q = 0, r >= 0 if p := q*v + r, M(q) = 0

  --*/

#include <algorithm>
#include <ostream>
#include <unordered_map>
#include <utility>
#include <variant>
#include "util/debug.h"
#include "util/dependency.h"
#include "util/lbool.h"
#include "util/memory_manager.h"
#include "util/params.h"
#include "util/rational.h"
#include "util/trace.h"
#include "util/uint_set.h"
#include "util/util.h"
#include "util/vector.h"
#include "params/smt_params_helper.hpp"
#include "math/dd/pdd_eval.h"
#include "math/lp/nla_core.h"
#include "math/lp/nla_coi.h"
#include "math/lp/nla_stellensatz2.h"
#include "math/dd/dd_pdd.h"
#include "math/lp/explanation.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lia_move.h"
#include "math/lp/lp_settings.h"
#include "math/lp/lp_types.h"
#include "math/lp/nla_common.h"
#include "math/lp/nla_defs.h"
#include "math/lp/nla_types.h"


namespace nla {
    
    lpvar stellensatz2::monomial_factory::mk_monomial(lp::lar_solver &lra, svector<lpvar> const &vars) {
        lpvar v = lp::null_lpvar;
        if (vars.empty())
            return v;
        if (vars.size() == 1)
            return vars[0];
        svector<lpvar> _vars(vars);
        std::sort(_vars.begin(), _vars.end());
        if (m_vars2mon.find(_vars, v))
            return v;
        auto is_int = all_of(vars, [&](lpvar v) { return lra.var_is_int(v); });
        auto nv = lra.number_of_vars();
        v = lra.add_var(nv, is_int);
        m_vars2mon.insert(_vars, v);
        m_mon2vars.insert(v, _vars);
        return v;
    }

    lpvar stellensatz2::monomial_factory::get_monomial(svector<lpvar> const &vars) {
        lpvar v = lp::null_lpvar;
        if (vars.empty())
            return v;
        if (vars.size() == 1)
            return vars[0];
        svector<lpvar> _vars(vars);
        std::sort(_vars.begin(), _vars.end());
        if (m_vars2mon.find(_vars, v))
            return v;
        return lp::null_lpvar;
    }

    void stellensatz2::monomial_factory::init(lpvar v, svector<lpvar> const &_vars) {
        svector<lpvar> vars(_vars);
        std::sort(vars.begin(), vars.end());
        m_vars2mon.insert(vars, v);
        m_mon2vars.insert(v, vars);
    }

    stellensatz2::stellensatz2(core* core) : 
        common(core), 
        m_solver(*this), 
        m_coi(*core), 
        pddm(core->lra_solver().number_of_vars()), 
        m_di(m_dm, core->reslim()) {
    }

    stellensatz2::~stellensatz2() { 
        reset();
    }

    lbool stellensatz2::saturate() {
        init_solver();
        TRACE(arith, display(tout << "stellensatz before saturation\n"));
        lbool r = search();

        TRACE(arith, tout << "search " << r << ": " << m_core << "\n");

        switch (r) {
        case l_false:
            ++c().lp_settings().stats().m_stellensatz.m_num_conflicts;
            conflict(m_core);
            return l_false;
        case l_true:
            if (set_model())
                return l_true;
            r = l_undef;
            break;
        default: 
            break;
        }
        IF_VERBOSE(2, display(verbose_stream()));        
        return r;
    }

    void stellensatz2::reset() {
        m_num_scopes = 0;
        m_monomial_factory.reset();
        m_values.reset();
        while (!m_constraints.empty()) {
            m_constraints.pop_back();
            m_justifications.pop_back();
            m_levels.pop_back();
            pop_bound();
            pop_propagation(m_bounds.size());
        }
        m_constraint_index.reset();
        for (auto & ivs : m_intervals) {
            for (auto iv : ivs) {
                m_di.del(*iv);
                dealloc(iv);
            }
            ivs.reset();
        }
    }

    void stellensatz2::init_solver() {
        reset();        
        m_coi.init();
        init_vars();
        simplify();
        m_stats.reset();
    }

    void stellensatz2::init_vars() {
        auto const& src = c().lra_solver();
        auto sz = src.number_of_vars();
        m_idx2bound.reset();
        m_split_count.reset();
        m_split_count.reserve(sz, 0);
        for (unsigned v = 0; v < sz; ++v) {
            m_values.push_back(c().val(v));
            if (!m_coi.vars().contains(v))
                continue;
            if (c().is_monic_var(v))
                init_monomial(v);
            // assert bounds on v in the new solver.
            if (src.column_has_lower_bound(v)) {
                auto lo_bound = src.get_lower_bound(v);
                SASSERT(lo_bound.y >= 0);
                auto k   = lo_bound.y > 0 ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE;
                auto rhs = lo_bound.x;
                auto dep = src.get_column_lower_bound_witness(v);
                add_var_bound(v, k, rhs, external_justification(dep));
            }
            if (src.column_has_upper_bound(v)) {
                auto hi_bound = src.get_upper_bound(v);
                SASSERT(hi_bound.y <= 0);
                auto k   = hi_bound.y < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                auto rhs = hi_bound.x;
                auto dep = src.get_column_upper_bound_witness(v);
                add_var_bound(v, k, rhs, external_justification(dep));
            }
        }
    }

    // set the model based on m_values computed by the solver
    bool stellensatz2::set_model() {
        if (!is_feasible())
            return false;
        auto &src = c().lra_solver();
        c().m_use_nra_model = true;
        m_values.reserve(src.number_of_vars());
        for (unsigned v = 0; v < src.number_of_vars(); ++v) {
            if (c().is_monic_var(v)) {
                auto& mon = c().emons()[v];
                rational val(1);
                for (auto w : mon.vars())
                    val *= m_values[w];
                m_values[v] = val;
            }
            else if (src.column_has_term(v)) {
                auto const& t = src.get_term(v);
                rational val(0);
                for (auto cv : t) 
                    val += m_values[cv.j()] * cv.coeff();
                m_values[v] = val;
            }
            else if (m_coi.vars().contains(v)) {
                // variable is in coi, m_values[v] is set.
            }
            else {
                m_values[v] = c().val(v);
            }
            c().m_nra.set_value(v, m_values[v]);
        }          
        return true;
    }

    dd::pdd stellensatz2::to_pdd(lpvar v) {
        if (m_coi.mons().contains(v)) {
            auto& mon = c().emons()[v];
            dd::pdd prod(pddm);
            prod = 1;
            for (auto w : mon.vars())
                prod *= to_pdd(w);
            return prod;
        }
        if (m_coi.terms().contains(v)) {
            auto const& t = c().lra_solver().get_term(v);
            dd::pdd sum(pddm);
            sum = 0;
            for (auto cv : t) 
                sum += to_pdd(cv.j())*cv.coeff();
            return sum;
        }
        return pddm.mk_var(v);
    }

    stellensatz2::term_offset stellensatz2::to_term_offset(dd::pdd const &p) {
        term_offset to;
        for (auto const &[coeff, vars] : p) {
            if (vars.empty())
                to.second += coeff;
            else
                to.first.add_monomial(coeff, m_monomial_factory.get_monomial(vars));                
        }        
        return to;
    }

    bool stellensatz2::has_term_offset(dd::pdd const &p) {
        for (auto const &[coeff, vars] : p) 
            if (!vars.empty() && lp::null_lpvar == m_monomial_factory.get_monomial(vars))
                return false;
        return true;
    }

    void stellensatz2::init_monomial(unsigned mon_var) {
        auto &mon = c().emons()[mon_var];
        m_monomial_factory.init(mon_var, mon.vars());
    }

    lp::constraint_index stellensatz2::add_var_bound(lp::lpvar v, lp::lconstraint_kind k, rational const& rhs, justification j) {
        auto p = to_pdd(v) - rhs;
        rational d(1);
        for (auto const& [c, is_constant] : p.coefficients()) 
            d = lcm(d, denominator(c));
        if (d != 1)
            p *= d;        
        return gcd_normalize(add_constraint(p, k, j));
    }

    lp::constraint_index stellensatz2::add_constraint(dd::pdd p, lp::lconstraint_kind k, justification j) {
        if (k == lp::lconstraint_kind::LE) {
            k = lp::lconstraint_kind::GE;
            p = -p;
        }
        if (k == lp::lconstraint_kind::LT) {
            k = lp::lconstraint_kind::GT;
            p = -p;
        }
        if (k == lp::lconstraint_kind::GT && is_int(p)) {
            k = lp::lconstraint_kind::GE;
            p -= rational(1);
        }
        lp::constraint_index ci = lp::null_ci;
        
        if (m_constraint_index.find({p.index(), k}, ci))
            return ci;
        ci = m_constraints.size();

        unsigned level = get_level(j);
        if (is_decision(j)) {
            ++m_num_scopes;    
            level = m_num_scopes;       
        }

        SASSERT(m_constraints.size() == m_justifications.size());
        m_constraints.push_back({p, k});
        m_levels.push_back(level);
        m_justifications.push_back(j);        
        m_constraint_index.insert({p.index(), k}, ci);
        push_bound(ci);
        push_propagation(ci);
        ++c().lp_settings().stats().m_stellensatz.m_num_constraints;    
        TRACE(arith, tout << "add constraint "; display_constraint(tout, ci));
        return ci;
    }

    void stellensatz2::push_bound(lp::constraint_index ci) {
        SASSERT(ci == m_bounds.size());
        auto [p, k] = m_constraints[ci];
        auto bound = -(p.offset());
        auto q = p + bound;
        auto mq = -q;
        m_dm.push_scope(); 
        auto q_index = q.index();
        auto last_index = q_index < m_idx2bound.size() ? m_idx2bound[q_index] : UINT_MAX;
        m_idx2bound.reserve(std::max(mq.index(), q_index) + 1, UINT_MAX);
        m_idx2bound[q_index] = ci;
        m_bounds.push_back(bound_info{k, bound, last_index, m_dm.mk_leaf(ci), q, mq});
    }

    void stellensatz2::pop_bound() {
        auto const &[k, bound, last_bound, d, q, mq] = m_bounds.back();
        m_idx2bound[q.index()] = last_bound;
        m_dm.pop_scope(1);
        m_bounds.pop_back();
    }

    lp::constraint_index stellensatz2::resolve(lp::constraint_index conflict, lp::constraint_index ci) {
        SASSERT(ci != lp::null_ci);
        if (conflict == lp::null_ci)
            return lp::null_ci;
        auto const &[p, k] = m_constraints[ci];
        if (p.is_var()) 
            return resolve_variable(p.var(), ci, conflict);
        if (p.is_minus())
            return resolve_variable((-p).var(), ci, conflict);
        return lp::null_ci;
    }

    lbool stellensatz2::sign(dd::pdd const &p) { 
        if (p.is_val()) {
            if (p.val() > 0)
                return l_false;
            if (p.val() < 0)
                return l_true;
            return l_undef;
        }
        auto val = value(p);
        if (p.is_var()) {
            if (val > 0)
                return l_false;
            if (val < 0)
                return l_true;
            return l_undef;
        }

        auto offset = p.offset();
        auto q = p - offset;
        if (has_lo(q)) {
            auto lo_bound = lo_val(q);
            // q >= lo_bound
            // q + offset >= lo_bound + offset
            if (lo_bound + offset > 0)
                return l_false;
            if (lo_bound + offset == 0 && lo_is_strict(q))
                return l_false;
        }
        if (has_hi(q)) {
            auto hi_bound = hi_val(q);
            // q <= hi_bound
            // q + offset <= hi_bound + offset
            if (hi_bound + offset < 0)
                return l_true;
            if (hi_bound + offset == 0 && hi_is_strict(q))
                return l_true;
        }
        if (val > 0)
            return l_false;
        if (val < 0)
            return l_true;
        return l_undef;
    }

    lp::constraint_index stellensatz2::resolve_variable(lpvar x, lp::constraint_index ci, lp::constraint_index other_ci) {
        TRACE(arith, tout << "resolve v" << x << "\n"; display_constraint(tout, ci);
              display_constraint(tout, other_ci));
        if (ci == lp::null_ci || other_ci == lp::null_ci)
            return lp::null_ci;
        auto f = factor(x, ci);
        auto g = factor(x, other_ci);
        if (f.degree != 1)
            return lp::null_ci;  // future - could handle this
        if (g.degree != 1)
            return lp::null_ci;  // not handling degree > 1

        //
        // check that p_value1 and p_value2 have different signs
        // check that other_p is disjoint from tabu
        // compute overlaps extending x
        //
        // need to allow for sign being 0
        
        auto f_sign = sign(f.p);
        auto g_sign = sign(g.p);
        if (f_sign == l_undef)
            return lp::null_ci;
        if (g_sign == l_undef)
            return lp::null_ci;
        if (f_sign == g_sign)
            return lp::null_ci;

        for (unsigned i = 0; i < f.degree; ++i)
            f.p *= to_pdd(x);
        for (unsigned i = 0; i < g.degree; ++i)
            g.p *= to_pdd(x);

        auto [m1, f_p] = f.p.var_factors();
        auto [m2, g_p] = g.p.var_factors();
        unsigned_vector m1m2;
        dd::pdd::merge(m1, m2, m1m2);
        SASSERT(m1m2.contains(x));
        f_p = f_p.mul(m1);
        g_p = g_p.mul(m2);

        // TRACE(arith, tout << "m1 " << m1 << " m2 " << m2 << " m1m2: " << m1m2 << "\n");

        // m1m2 * f_p + f.q >= 0
        // m1m2 * g_p + g.q >= 0
        //
        lp::constraint_index ci_a, ci_b;
        auto const &[other_p, other_k] = m_constraints[other_ci];
        auto const &[p, k] = m_constraints[ci];

        bool g_strict = other_k == lp::lconstraint_kind::GT;
        bool f_strict = k == lp::lconstraint_kind::GT;
        if (g_p.is_val() && f_p.is_val() && g_p.val() == -f_p.val())
            ci_a = ci;
        else if (g_p.is_val())
            ci_a = multiply(ci, pddm.mk_val(g_p.val()));
        else if (g_sign == l_true)
            ci_a = multiply(ci, assume(g_p, f_strict ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE));
        else
            ci_a = multiply(ci, assume(g_p, f_strict ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE));

        if (g_p.is_val() && f_p.is_val() && g_p.val() == -f_p.val())
            ci_b = other_ci;
        else if (f_p.is_val())
            ci_b = multiply(other_ci, pddm.mk_val(f_p.val()));
        else if (f_sign == l_true)
            ci_b = multiply(other_ci, assume(f_p, g_strict ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE));
        else
            ci_b = multiply(other_ci, assume(f_p, g_strict ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE));

        auto new_ci = add(ci_a, ci_b);
        
        ++c().lp_settings().stats().m_stellensatz.m_num_resolutions;

        TRACE(arith, tout << "eliminate j" << x << ":\n"; display_constraint(tout, ci);
              display_constraint(tout, other_ci); display_constraint(tout, ci_a);
              display_constraint(tout, ci_b); display_constraint(tout, new_ci));

        new_ci = factor(new_ci);

        return new_ci;
    }

    void stellensatz2::conflict(svector<lp::constraint_index> const& core) {
        lp::explanation ex;
        lemma_builder new_lemma(c(), "stellensatz");
        m_constraints_in_conflict.reset();
        for (auto ci : core)
            explain_constraint(new_lemma, ci, ex);
        new_lemma &= ex;
        IF_VERBOSE(2, verbose_stream() << "stellensatz unsat \n" << new_lemma << "\n");
        TRACE(arith, tout << "unsat\n" << new_lemma << "\n");
        c().lra_solver().settings().stats().m_nla_stellensatz++;
    }

    bool stellensatz2::is_feasible() {
        if (any_of(m_constraints, [&](auto const &c) { return !constraint_is_true(c); }))
            return false;
        for (auto v : m_var2level) {
            if (var_is_int(v) && !value(v).is_int())
                return false;
        }
        return true;
    }

    bool stellensatz2::is_linear_conflict() {
        lbool r = m_solver.solve(m_core);
        TRACE(arith, display(tout << "stellensatz after saturation " << r << "\n"));
        if (r != l_false) {
            m_solver.update_values(m_values);
            return false;
        }
        while (backtrack(m_core)) {            
            r = m_solver.solve(m_core);
            TRACE(arith, tout << "backtrack search " << r << ": " << m_core << "\n");
            if (r == l_false)
                continue;
            m_solver.update_values(m_values);
            return false;
        }        
        return true;
    }


    //
    // for px + q >= 0 
    // If M(p) = 0, then 
    // derive the constraint q >= 0 using the inference
    // 
    //  px + q >= 0    p = 0
    //  --------------------
    //        q >= 0
    // 
    // The equality p = 0 is tracked as an assumption.
    // 
    lp::constraint_index stellensatz2::vanishing(lpvar x, factorization const &f, lp::constraint_index ci) { 
        if (f.p.is_zero())
            return lp::null_ci;
        auto p_value = value(f.p);
        if (p_value != 0)
            return lp::null_ci;        
        ++c().lp_settings().stats().m_stellensatz.m_num_vanishings;
        // add p = 0 as assumption and reduce to q.
        auto p_is_0 = assume(f.p, lp::lconstraint_kind::EQ);
        // ci & -p_is_0*x^f.degree  => new_ci
        dd::pdd r = pddm.mk_val(rational(-1));
        for (unsigned i = 0; i < f.degree; ++i)
            r = r * pddm.mk_var(x);
        p_is_0 = multiply(p_is_0, r);
        auto new_ci = add(ci, p_is_0);
        TRACE(arith, display_constraint(tout << "j" << x << " ", ci);
                     display_constraint(tout << "reduced ", new_ci);
                     display_constraint(tout, p_is_0));  
        return factor(new_ci);
    }

    //
    // reduce x * y * p >= 0
    // to    
    // p >= 0 based on assumptions x > 0, y > 0 or x < 0, y < 0
    // -p >= 0 based on assumptions x > 0, y < 0 or x < 0, y > 0
    // 
    // reduce x * y * p > 0
    // to
    // p > 0 based on assumptions x >= 0, y >= 0 or x <= 0, y <= 0
    // -p > 0 based on assumptions x >= 0, y <= 0 or x <= 0, y >= 0
    //
    lp::constraint_index stellensatz2::factor(lp::constraint_index ci) {
        auto const &[p, k] = m_constraints[ci];
        auto [vars, q] = p.var_factors(); // p = vars * q
   
        bool is_gt = k == lp::lconstraint_kind::GT;
        unsigned i = 0;
        for (auto v : vars)
            if (is_gt || value(v) != 0)
                vars[i++] = v;
            else
                q *= pddm.mk_var(v);
        vars.shrink(i);
        if (vars.empty())
            return ci;         
        if (vars.size() == 1 && q.is_val())
            return ci;
        if (q.is_val()) {
            q *= pddm.mk_var(vars.back());
            vars.pop_back();
        }
        
        vector<dd::pdd> muls;
        muls.push_back(q);
        for (auto v : vars)
            muls.push_back(muls.back() * pddm.mk_var(v));
        auto new_ci = ci;
        SASSERT(muls.back() == p);
        int sign = 1;
        for (unsigned i = vars.size(); i-- > 0;) {
            auto pv = pddm.mk_var(vars[i]);
            auto val = value(vars[i]);
            auto k1 = val == 0 ? lp::lconstraint_kind::GE : (val > 0 ? lp::lconstraint_kind::GT : lp::lconstraint_kind::LT);
            if (val < 0)
                sign = -sign;
            new_ci = divide(new_ci, assume(pv, k1), sign * muls[i]);
            TRACE(arith_verbose, display_constraint(tout, new_ci); display_constraint(tout, assume(pv, k1)););
        }
        TRACE(arith, display_constraint(tout << "factor ", new_ci));
        return new_ci;
    }

    unsigned stellensatz2::degree_of_var_in_constraint(lpvar var, lp::constraint_index ci) const {
        return m_constraints[ci].p.degree(var);
    }

    stellensatz2::factorization stellensatz2::factor(lpvar v, lp::constraint_index ci) {
        auto const& [p, k] = m_constraints[ci];
        auto degree = degree_of_var_in_constraint(v, ci);
        dd::pdd lc(pddm), rest(pddm);
        p.factor(v, degree, lc, rest);
        return {degree, lc, rest};
    }

    //
    // check if core depends on an assumption
    // identify the maximal assumption
    // undo m_constraints down to max_ci.
    // negate max_ci
    // propagate it using remaining external and assumptions.
    // find a new satisfying assignment (if any) before continuing.
    // 
    bool stellensatz2::backtrack(svector<lp::constraint_index> const &core) {
        ++c().lp_settings().stats().m_stellensatz.m_num_backtracks;
        ++m_stats.m_num_backtracks;
        SASSERT(well_formed());
        m_constraints_in_conflict.reset();
        svector<lp::constraint_index> external, assumptions;
        for (auto ci : core)
            explain_constraint(ci, external, assumptions);
        TRACE(arith, display(tout << "backtrack core " << core << "external " << external << " assumptions "
                                  << assumptions << "\n");
              for (auto a : assumptions) display_constraint(tout, a););
        if (assumptions.empty())
            return false;
        lp::constraint_index max_ci = 0;
        for (auto ci : assumptions) 
            max_ci = std::max(ci, max_ci);

        assumptions.erase(max_ci);
        SASSERT(all_of(assumptions, [&](lp::constraint_index ci) { return m_levels[ci] < m_levels[max_ci]; }));
        external.append(assumptions);
        backtrack(max_ci, external);
        SASSERT(well_formed());
        return true;
    }

    bool stellensatz2::core_is_linear(svector<lp::constraint_index> const &core) {
        m_constraints_in_conflict.reset();
        svector<lp::constraint_index> external, assumptions;
        for (auto ci : core)
            explain_constraint(ci, external, assumptions);
        return all_of(assumptions, [&](auto ci) { return has_term_offset(m_constraints[ci].p); });
    }

    void stellensatz2::explain_constraint(lp::constraint_index ci, svector<lp::constraint_index> &external,
                                         svector<lp::constraint_index> &assumptions) {
        if (m_constraints_in_conflict.contains(ci))
            return;
        m_constraints_in_conflict.insert(ci);

        auto &j = m_justifications[ci];
        if (std::holds_alternative<external_justification>(j)) {
            external.push_back(ci);
        }
        else if (is_decision(j)) {
            assumptions.push_back(ci);
        }
        else {
            for (auto cij : justification_range(*this, j))
                explain_constraint(cij, external, assumptions);
        }
    }

    //
    // a constraint can be explained by a set of bounds used as justifications
    // and by an original constraint.
    // 
    void stellensatz2::explain_constraint(lemma_builder &new_lemma, lp::constraint_index ci, lp::explanation &ex) {
        svector<lp::constraint_index> external, assumptions;
        explain_constraint(ci, external, assumptions);
        for (auto ci : external) {
            auto &j = m_justifications[ci];
            auto dep = std::get<external_justification>(j);
            c().lra_solver().push_explanation(dep.dep, ex);
        }
        for (auto ci : assumptions) {
            auto &[p, k] = m_constraints[ci];
            auto [t, coeff] = to_term_offset(p);
            new_lemma |= ineq(t, negate(k), -coeff);
        }
    }
 
    rational stellensatz2::value(dd::pdd const& p) const {
        dd::pdd_eval eval;
        eval.var2val() = [&](unsigned v) -> rational { return value(v); };
        return eval(p);
    }

    //
    // normalize constraint by dividing by gcd of coefficients
    //
    lp::constraint_index stellensatz2::gcd_normalize(lp::constraint_index ci) {
        auto [p, k] = m_constraints[ci];
        rational g(0);
        bool _is_int = is_int(p);
        for (auto const& [c, is_constant] : p.coefficients()) 
            if (!is_constant || !_is_int)
                g = gcd(g, c);
        if (g == 0 || g == 1)
            return ci;
        // g := gcd of non-constant coefficients, or all coefficients if not integer
        switch (k) {
        case lp::lconstraint_kind::GE: {
            // p + k >= 0
            // -> (p + k) / g >= 0
            // -> p / g + k/g + floor(k/g) - k/g >= 0
            // -> p / g + floor(k/g) >= 0
            auto q = p * (1/ g);
            q += (floor(q.offset()) - q.offset());
            return add_constraint(q, k, gcd_justification(ci));
        }
        case lp::lconstraint_kind::GT: {
            // p + k > 0
            // p / g + floor(k/g) >= 0 if k/g is not integer
            // p / q + k/g - 1 >= 0 if k/g is integer
            auto q = p * (1 / g);   
            auto offset = q.offset();
            q += (floor(offset) - offset);
            if (_is_int) {
                k = lp::lconstraint_kind::GE;
                if (offset.is_int())
                    q -= rational(1);
            }
            return add_constraint(q, k, gcd_justification(ci));
        }
        case lp::lconstraint_kind::LT:
        case lp::lconstraint_kind::LE:            
            UNREACHABLE();
        case lp::lconstraint_kind::EQ:
        case lp::lconstraint_kind::NE:
            if (!divides(g, p.offset()))
                return ci;
            return add_constraint(p * (1/g), k, gcd_justification(ci));
        default:
            UNREACHABLE(); 
            return ci;
        }        
    }
    
    lp::constraint_index stellensatz2::assume(dd::pdd const& p, lp::lconstraint_kind k) {
        if (k == lp::lconstraint_kind::EQ) {
            auto left = assume(p, lp::lconstraint_kind::GE);
            auto right = assume(-p, lp::lconstraint_kind::GE);
            return add_constraint(p, k, eq_justification{left, right});
        }
        if (k == lp::lconstraint_kind::LE)            
            return assume(-p, lp::lconstraint_kind::GE);
        if (k == lp::lconstraint_kind::LT)
            return assume(-p, lp::lconstraint_kind::GT);
        
        u_dependency *d = nullptr;
        auto has_bound = [&](rational const& a, lpvar x, rational const& b) {
            rational bound;
            bool is_strict = false;
            if (a == 1 && k == lp::lconstraint_kind::GE && c().lra_solver().has_lower_bound(x, d, bound, is_strict) &&
                bound >= -b) {
                return true;
            }
            if (a == 1 && k == lp::lconstraint_kind::GT && c().lra_solver().has_lower_bound(x, d, bound, is_strict) &&
                (bound > -b || (is_strict && bound >= -b))) {
                return true;
            }
            if (a == -1 && k == lp::lconstraint_kind::GE && c().lra_solver().has_upper_bound(x, d, bound, is_strict) &&
                bound <= -b) {
                return true;
            }
            if (a == -1 && k == lp::lconstraint_kind::GT && c().lra_solver().has_upper_bound(x, d, bound, is_strict) &&
                (bound < -b || (is_strict && bound <= -b))) {
                return true;
            }
            return false;
        };

        if (p.is_unilinear() && has_bound(p.hi().val(), p.var(), p.lo().val()))
            // ax + b ~k~ 0
            return add_constraint(p, k, external_justification(d));  
        TRACE(arith, tout << m_constraints.size() << " assume " << p << " " << k << " 0\n");
        return add_constraint(p, k, assumption_justification());
    }
    
    // p1 >= lo1, p2 >= lo2 => p1 + p2 >= lo1 + lo2
    lp::constraint_index stellensatz2::add(lp::constraint_index left, lp::constraint_index right) {
        auto const &[p, k1] = m_constraints[left];
        auto const &[q, k2] = m_constraints[right];
        lp::lconstraint_kind k = join(k1, k2);
        return gcd_normalize(add_constraint(p + q, k, addition_justification{left, right}));
    }

    // p >= 0  =>  a * p >= 0 if a > 0,
    // p = 0   => p * q = 0  no matter what q
    lp::constraint_index stellensatz2::multiply(lp::constraint_index ci, dd::pdd q) {
        auto const& [p, k] = m_constraints[ci];
        auto k1 = k;
        if (q.is_val() && q.val() < 0)
            k1 = swap_side(k1);
        SASSERT(q.is_val() || k1 == lp::lconstraint_kind::EQ);
        return add_constraint(p * q, k1, multiplication_poly_justification{ci, q});
    }

    lp::constraint_index stellensatz2::multiply(lp::constraint_index left, lp::constraint_index right) {
        auto const &[p, k1] = m_constraints[left];
        auto const &[q, k2] = m_constraints[right];
        lp::lconstraint_kind k = meet(k1, k2);
        return add_constraint(p*q, k, multiplication_justification{left, right});
    }

    // p k 0, d > 0 -> p/d k 0, where q := d / d
    // q is the quotient obtained by dividing the divisor constraint, which is of the form d - 1 >= 0 or d > 0
    lp::constraint_index stellensatz2::divide(lp::constraint_index ci, lp::constraint_index divisor, dd::pdd q) {
        auto const &[p, k] = m_constraints[ci];
        return add_constraint(q, k, division_justification{ci, divisor});
    }

    lp::constraint_index stellensatz2::substitute(lp::constraint_index ci, lp::constraint_index ci_eq, lpvar v,
                                                  dd::pdd p) {
        auto const &[p1, k1] = m_constraints[ci];
        auto const &[p2, k2] = m_constraints[ci_eq];
        SASSERT(k2 == lp::lconstraint_kind::EQ);
        auto q = p1.subst_pdd(v, p);
        return add_constraint(q, k1, substitute_justification{ci, ci_eq, v, p});
    }

    bool stellensatz2::is_int(svector<lp::lpvar> const& vars) const {
        return all_of(vars, [&](lpvar v) { return var_is_int(v); });
    }

    bool stellensatz2::is_int(dd::pdd const &p) const {
        return is_int(p.free_vars());
    }

    bool stellensatz2::var_is_int(lp::lpvar v) const {
        return c().lra_solver().var_is_int(v);
    }

    bool stellensatz2::constraint_is_true(lp::constraint_index ci) const {
        return ci != lp::null_ci && constraint_is_true(m_constraints[ci]);
    }

    bool stellensatz2::constraint_is_false(lp::constraint_index ci) const {
        return ci != lp::null_ci && constraint_is_false(m_constraints[ci]);
    }

    bool stellensatz2::constraint_is_true(constraint const &c) const {
        auto const& [p, k] = c;
        auto lhs = value(p);
        switch (k) {
        case lp::lconstraint_kind::GT: return lhs > 0;
        case lp::lconstraint_kind::GE: return lhs >= 0;
        case lp::lconstraint_kind::LE: return lhs <= 0;
        case lp::lconstraint_kind::LT: return lhs < 0;
        case lp::lconstraint_kind::EQ: return lhs == 0;
        case lp::lconstraint_kind::NE: return lhs != 0;
        default: UNREACHABLE();  return false;
        }
    }

    bool stellensatz2::constraint_is_trivial(lp::constraint_index ci) const {
        return ci != lp::null_ci && constraint_is_trivial(m_constraints[ci]);
    }

    bool stellensatz2::constraint_is_trivial(constraint const &c) const {
        auto const &[p, k] = c;
        if (!p.is_val())
            return false;
        if (p.val() > 0)
            return k == lp::lconstraint_kind::GE || k == lp::lconstraint_kind::GT || k == lp::lconstraint_kind::NE;
        else if (p.val() == 0)
            return k == lp::lconstraint_kind::EQ || k == lp::lconstraint_kind::GE || k == lp::lconstraint_kind::LE;
        else // p.val() < 0
            return k == lp::lconstraint_kind::LE || k == lp::lconstraint_kind::LT || k == lp::lconstraint_kind::NE;
    }

    bool stellensatz2::constraint_is_conflict(lp::constraint_index ci) const {
        return ci != lp::null_ci && constraint_is_conflict(m_constraints[ci]);
    }

    bool stellensatz2::constraint_is_conflict(constraint const& c) const {
        auto const &[p, k] = c;
        return p.is_val() &&
               ((p.val() < 0 && k == lp::lconstraint_kind::GE) 
                   || (p.val() <= 0 && k == lp::lconstraint_kind::GT));
    }

    bool stellensatz2::constraint_is_bound_conflict(lp::constraint_index ci) {
        auto const &c = m_constraints[ci];
        auto const &[p, k] = c;
        auto const &iv = get_interval(p);
        return constraint_is_bound_conflict(ci, iv);
    }

    bool stellensatz2::constraint_is_bound_conflict(lp::constraint_index ci, dep_interval const &iv) {
        auto const &[p, k] = m_constraints[ci];
        if (iv.m_upper_inf)
            return false;
        if (iv.m_upper > 0)
            return false;
        bool is_negative = iv.m_upper < 0 || iv.m_upper_open;
        SASSERT(is_negative || iv.m_upper == 0);
        bool is_conflict = k == lp::lconstraint_kind::GT || (k == lp::lconstraint_kind::GE && is_negative);
        if (!is_conflict)
            return false;
        m_conflict_dep.reset();
        m_dm.linearize(iv.m_lower_dep, m_conflict_dep);
        TRACE(arith, tout << "constraint is bound conflict: "; display_constraint(tout, ci);
        m_di.display(tout, iv) << "\n");                    
        return true;
    }

    bool stellensatz2::var_is_bound_conflict(lpvar v) {
        return is_bound_conflict(pddm.mk_var(v));
    }

    bool stellensatz2::is_bound_conflict(dd::pdd const &p) {
        if (!has_lo(p) || !has_hi(p))
            return false;
        if (lo_val(p) < hi_val(p))
            return false;
        if (lo_val(p) == hi_val(p) && !lo_is_strict(p) && !hi_is_strict(p))
            return false;
        m_conflict_dep.reset();
        m_conflict_dep.push_back(lo_constraint(p));
        m_conflict_dep.push_back(hi_constraint(p));
        return true;
    }

    void stellensatz2::calculate_interval(scoped_dep_interval& out, dep_interval const& x, dep_interval const& lo, dep_interval const& hi) {
        auto &m = out.m();
        scoped_dep_interval tmp(m);
        m.mul<dep_intervals::with_deps>(x, hi, tmp);
        m.add<dep_intervals::with_deps>(lo, tmp, out);
    }

    //
    // Main search loop.
    // Resolve conflicts, propagate and case split on bounds.
    // 
    lbool stellensatz2::search() { 
        init_search();   
        lbool is_sat = l_undef;
        while (is_sat == l_undef && can_continue_search()) {
            if (is_conflict())
                is_sat = resolve_conflict();
            else if (should_propagate())
                propagate();
            else if (primal_saturate())
                continue;
            else if (is_feasible())
                is_sat = l_true;
            else if (is_linear_conflict())
                is_sat = l_false;
            else if (should_dual_saturate())
                dual_saturate();
            else if (!decide())
                is_sat = l_true;
        }
        if (is_sat == l_true) 
            return is_feasible() ? l_true : l_undef;        
        return is_sat;
    }

    bool stellensatz2::can_continue_search() {
        return c().reslim().inc() && m_stats.m_num_backtracks < m_config.max_conflicts;
    }

    void stellensatz2::init_search() {
        m_prop_qhead = 0;
        m_level2var.reset();
        m_var2level.reset();
        for (unsigned v = 0; v < m_values.size(); ++v)
            m_level2var.push_back(v);
        init_levels();
    }

    void stellensatz2::init_levels() {
        random_gen rand(c().random());
        shuffle(m_level2var.size(), m_level2var.begin(), rand);
           
        m_var2level.resize(m_values.size(), m_level2var.size());
        for (unsigned i = 0; i < m_level2var.size(); ++i)
            m_var2level[m_level2var[i]] = i;        
        for (auto const &c : m_constraints)
            if (constraint_is_false(c))
                for (auto v : c.p.free_vars())
                    move_up(v); 

        for (auto &v : m_max_occurs)
            v.reset();
        m_max_occurs.reserve(num_vars());
        for (unsigned ci = 0; ci < m_constraints.size(); ++ci) 
            insert_max_var(ci);
    }

    void stellensatz2::insert_max_var(lp::constraint_index ci) {
        auto const &c = m_constraints[ci];
        if (c.p.degree() > m_config.max_degree)
            return;
        unsigned level = 0;
        lpvar max_var = lp::null_lpvar;
        for (auto v : c.p.free_vars()) {
            if (m_var2level[v] > level) {
                level = m_var2level[v];
                max_var = v;
            }
        }
        if (max_var != lp::null_lpvar)
            m_max_occurs[max_var].push_back(ci);    
    }

    //
    // Conflict resolution is similar to CDCL
    // walk m_bounds based on the propagated bounds
    // flip the last decision and backjump to the UIP.
    //     
    lbool stellensatz2::resolve_conflict() {
        SASSERT(is_conflict());
        TRACE(arith, tout << "resolving conflict: " << m_conflict_dep << "\n"; display_constraint(tout, m_conflict);
              display(tout););

        m_conflict_marked_ci.reset();
        unsigned conflict_level = 0;
        for (auto ci : m_conflict_dep) {
            m_conflict_marked_ci.insert(ci);
            conflict_level = std::max(conflict_level, m_levels[ci]);
        }

        bool found_decision = false;
        TRACE(arith, tout << "conflict level " << conflict_level << " constraints: " << m_conflict_marked_ci << "\n");
        unsigned ci = m_constraints.size();
        unsigned sz = ci;
        m_core.reset();
        while (!found_decision && ci > 0 && !m_conflict_marked_ci.empty() && conflict_level > 0) {
            --ci;
            if (!m_conflict_marked_ci.contains(ci))
                continue;

            mark_dependencies(ci);
            m_conflict_marked_ci.remove(ci);
            //m_conflict = resolve(m_conflict, ci);
            if (conflict_level == 0)
                m_core.push_back(ci);

            found_decision = is_decision(ci);

            TRACE(arith, tout << "num constraints: " << m_constraints.size() << "\n";
                  tout << "is_decision: " << found_decision << "\n"; display_constraint(tout, ci);
                  tout << "new conflict: "; display_constraint(tout, m_conflict););
        }
        #if 0
        if (constraint_is_conflict(m_conflict)) {
            TRACE(arith, tout << "Conflict " << m_conflict << "\n");
            m_core.push_back(m_conflict);
            reset_conflict();
            return l_false;
        }
        #endif
        SASSERT(found_decision == (conflict_level != 0));
        if (!found_decision) {
            for (auto ci : m_conflict_marked_ci)
                m_core.push_back(ci);            
            reset_conflict();
            TRACE(arith, tout << "conflict " << m_core << "\n");
            return l_false;
        }

        SASSERT(is_decision(ci));

        svector<lp::constraint_index> deps;
        for (auto ci : m_conflict_marked_ci) 
            deps.push_back(ci);
        
        backtrack(ci, deps);        
        return l_undef;
    }

    // ~(x >= k) == -x > -k == -x >= -k + 1 if k integer
    // ~(x > k)  == -x >= -k
    // ~(x <= k) == -x < -k == -x <= -k - 1 if k integer

    stellensatz2::constraint stellensatz2::negate_constraint(constraint const &c) { 
        auto [p, k] = c; 
        p = -p;
        switch (k) {            
        case lp::lconstraint_kind::GE:
            if (is_int(p)) 
                p += rational(1);            
            else 
                k = lp::lconstraint_kind::GT;            
            break;
        case lp::lconstraint_kind::GT: k = lp::lconstraint_kind::GE; break;
        case lp::lconstraint_kind::LT: k = lp::lconstraint_kind::LE; break;
        case lp::lconstraint_kind::LE:
            if (is_int(p)) 
                p -= rational(1);            
            else
                k = lp::lconstraint_kind::LT;
            break;
        }
        return {p, k};
    }

    void stellensatz2::backtrack(unsigned ci, svector<lp::constraint_index> const &deps) {
        SASSERT(is_decision(ci));
        auto &[p, k] = m_constraints[ci];
        unsigned propagation_level = 0;
        for (auto ci : deps)
            propagation_level = std::max(propagation_level, m_levels[ci]);
        m_constraint_index.erase({p.index(), k});
        
        TRACE(arith, display_constraint(tout, ci) << "deps: " << deps << " level " << propagation_level << "\n");    
        TRACE(arith, for (auto d : deps) display_constraint(tout << "  dep: ", d););
        SASSERT(propagation_level <= m_levels[ci]);
        // propagate negated constraint
        m_constraints[ci] = negate_constraint(m_constraints[ci]);
        m_justifications[ci] = propagation_justification(deps);
        m_num_scopes = m_levels[ci] - 1;        
        m_levels[ci] = propagation_level;
        lp::constraint_index head = ci + 1, tail = ci + 1;
        // replay other constraints
        unsigned sz = m_constraints.size();
        // non-chronological backtracking breaks several assumptions that hold for chronological
        // The last decision 
        svector<lp::constraint_index> tail2head;
        tail2head.resize(sz - ci);
        auto translate_ci = [&](lp::constraint_index old_ci) -> lp::constraint_index {
            SASSERT(old_ci != ci);
            return old_ci < ci ? old_ci : tail2head[sz - old_ci];
        };
        for (; tail < m_constraints.size(); ++tail) {
            auto [p, k] = m_constraints[tail];
            auto level = m_levels[tail];
            m_constraint_index.erase({p.index(), k});
            if (level > m_num_scopes) 
                continue;            
            TRACE(arith, display_constraint(tout << "replaying " << tail << " " << m_num_scopes << "\n", tail));
            SASSERT(!is_decision(tail));
            m_constraints[head] = m_constraints[tail];
            m_justifications[head] = translate_j(translate_ci, m_justifications[tail]);
            m_levels[head] = get_level(m_justifications[head]); 
            SASSERT(well_formed_constraint(head));
            tail2head[sz - tail] = head;

            m_constraint_index.insert({p.index(), k}, head);
            ++head;
        }
        m_constraints.shrink(head);
        m_justifications.shrink(head);
        m_levels.shrink(head);
        // re-insert bounds
        for (; m_bounds.size() >= ci;) {
            pop_bound();
            pop_propagation(m_bounds.size());
        }
        for (; m_bounds.size() < head;) {
            push_bound(m_bounds.size());
            push_propagation(m_bounds.size() - 1);
        }

        SASSERT(well_formed_last_constraint());
        SASSERT(well_formed());
        reset_conflict();        
    }

    stellensatz2::justification stellensatz2::translate_j(std::function<lp::constraint_index(lp::constraint_index)> const& f,
        justification const& j) const {
        return std::visit([&](auto const& arg) -> justification {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_same_v<T, bound_propagation_justification>) {
                svector<lp::constraint_index> cs;
                for (auto ci : arg.cs)
                    cs.push_back(f(ci));
                return bound_propagation_justification{f(arg.ci), cs};
            }
            else if constexpr (std::is_same_v<T, propagation_justification>) {
                svector<lp::constraint_index> cs;
                for (auto ci : arg.cs)
                    cs.push_back(f(ci));
                return propagation_justification{cs};
            }
            else if constexpr (std::is_same_v<T, assumption_justification>) {
                return assumption_justification{};
            }
            else if constexpr (std::is_same_v<T, external_justification>) {
                return external_justification{arg.dep};
            }
            else if constexpr (std::is_same_v<T, gcd_justification>) {
                return gcd_justification{f(arg.ci)};
            }
            else if constexpr (std::is_same_v<T, substitute_justification>) {
                return substitute_justification{f(arg.ci), f(arg.ci_eq), arg.v, arg.p};
            }
            else if constexpr (std::is_same_v<T, addition_justification>) {
                return addition_justification{f(arg.left), f(arg.right)};
            }
            else if constexpr (std::is_same_v<T, division_justification>) {
                return division_justification{f(arg.ci), f(arg.divisor)};
            }
            else if constexpr (std::is_same_v<T, eq_justification>) {
                return eq_justification{f(arg.left), f(arg.right)};
            }
            else if constexpr (std::is_same_v<T, multiplication_justification>) {
                return multiplication_justification{f(arg.left), f(arg.right)};
            }
            else if constexpr (std::is_same_v<T, multiplication_poly_justification>) {
                return multiplication_poly_justification{f(arg.ci), arg.p};
            }
            else {
                UNREACHABLE();
                return arg;
            }
        }, j);
    }

    void stellensatz2::mark_dependencies(u_dependency* d) { 
        auto cdeps = antecedents(d);
        for (auto a : cdeps)
            m_conflict_marked_ci.insert(a);
    }

    void stellensatz2::mark_dependencies(lp::constraint_index ci) {
        for (auto cij : justification_range(*this, m_justifications[ci]))
            m_conflict_marked_ci.insert(cij);
    }

    lp::constraint_index stellensatz2::get_constraint_index(justification const& j, unsigned index) {
        if (std::holds_alternative<bound_propagation_justification>(j)) {
            auto const &bpj = std::get<bound_propagation_justification>(j);
            return index == 0 ? bpj.ci : bpj.cs[index - 1];
        }
        if (std::holds_alternative<propagation_justification>(j)) {
            auto const &bpj = std::get<propagation_justification>(j);
            return bpj.cs[index];
        }
        if (std::holds_alternative<assumption_justification>(j)) {
            UNREACHABLE();
        }
        if (std::holds_alternative<external_justification>(j)) {
            UNREACHABLE();
        }
        if (std::holds_alternative<gcd_justification>(j)) {
            SASSERT(index == 0);
            return std::get<gcd_justification>(j).ci;
        }
        if (std::holds_alternative<substitute_justification>(j)) {
            SASSERT(index < 2);
            auto const &sj = std::get<substitute_justification>(j);
            return index == 0 ? sj.ci : sj.ci_eq;
        }
        if (std::holds_alternative<addition_justification>(j)) {
            SASSERT(index < 2);
            auto const &aj = std::get<addition_justification>(j);
            return index == 0 ? aj.left : aj.right;
        }
        if (std::holds_alternative<division_justification>(j)) {
            SASSERT(index < 2);
            auto const &dj = std::get<division_justification>(j);
            return index == 0 ? dj.ci : dj.divisor;
        }
        if (std::holds_alternative<eq_justification>(j)) {
            SASSERT(index < 2);
            auto const &ej = std::get<eq_justification>(j);
            return index == 0 ? ej.left : ej.right;
        }
        if (std::holds_alternative<multiplication_justification>(j)) {
            SASSERT(index < 2);
            auto const &mj = std::get<multiplication_justification>(j);
            return index == 0 ? mj.left : mj.right;
        }
        if (std::holds_alternative<multiplication_poly_justification>(j)) {
            SASSERT(index == 0);
            return std::get<multiplication_poly_justification>(j).ci;
        }
        UNREACHABLE();
        return lp::null_ci;    
    }

    unsigned stellensatz2::num_constraints(justification const &j) {
        if (std::holds_alternative<bound_propagation_justification>(j)) 
            return 1 + std::get<bound_propagation_justification>(j).cs.size();
        if (std::holds_alternative<propagation_justification>(j)) 
            return std::get<propagation_justification>(j).cs.size();
        if (std::holds_alternative<assumption_justification>(j))
            return 0;
        if (std::holds_alternative<external_justification>(j))
            return 0;
        if (std::holds_alternative<gcd_justification>(j)) 
            return 1;
        if (std::holds_alternative<substitute_justification>(j)) 
            return 2;
        if (std::holds_alternative<addition_justification>(j))
            return 2;
        if (std::holds_alternative<division_justification>(j))
            return 2;
        if (std::holds_alternative<eq_justification>(j))
            return 2;
        if (std::holds_alternative<multiplication_justification>(j))
            return 2;
        if (std::holds_alternative<multiplication_poly_justification>(j))
            return 1;
        UNREACHABLE();
        return 0;
    }

    void stellensatz2::propagate_constraint(lpvar x, lp::lconstraint_kind k, rational const& value,
        lp::constraint_index ci, svector<lp::constraint_index>& cs) {
        TRACE(arith, display_constraint(tout << "constraint is propagating ", ci);
              tout << "v" << x << " " << k << " " << value << "\n";);

        // block repeated bounds propagation
        if (propagation_cycle(x, value, k, ci, cs))
            return;

        ci = add_constraint(pddm.mk_var(x) - value, k, bound_propagation_justification{ci, cs});

        if (constraint_is_bound_conflict(ci))
            return;

        set_in_bounds(x);

        CTRACE(arith, !well_formed_last_constraint(), display(tout));
        SASSERT(well_formed_last_constraint());
        SASSERT(well_formed_var(x));
    }

    bool stellensatz2::propagation_cycle(lpvar v, rational const &value, lp::lconstraint_kind k, lp::constraint_index ci, svector<lp::constraint_index>& cs) const {
        if (!in_bounds(v, value))
            return false;
        auto level = m_levels[ci];
        for (auto a : cs)
            level = std::max(level, m_levels[a]);
        SASSERT(level <= m_num_scopes);
        bool is_upper = k == lp::lconstraint_kind::LE || k == lp::lconstraint_kind::LT;
        auto last_bound = is_upper ? get_upper(v) : get_lower(v);
        while (last_bound != UINT_MAX && m_levels[last_bound] == level) {
            auto const &j = m_justifications[last_bound];
            if (std::holds_alternative<bound_propagation_justification>(j) &&
                ci == std::get<bound_propagation_justification>(j).ci)
                return true;            
            last_bound = m_bounds[last_bound].m_last_bound;
        }
        return false;
    }
   
    // Dual saturation solves a dual satisfiability problem to determine if there is a proof.
    // It augments the set of inequalities by adding polynomials that produce monomials that 
    // belong to a satisfying subset.

    void stellensatz2::dual_saturate() {

    }

    //
    // Attempt to repair variables in some order
    // 
    
    bool stellensatz2::primal_saturate() {

        init_levels();
        unsigned num_fixed = 0;
        unsigned num_levels = m_level2var.size();
        unsigned num_rounds = 0;
        unsigned max_rounds = num_levels * 5;
        unsigned constraint_lim = m_constraints.size();
        unsigned constraint_size = m_constraints.size();
        m_tabu.reset();
        // m_vanishing_constraints.reset();
        for (unsigned level = 0; level < num_levels && c().reslim().inc() && num_rounds < max_rounds; ++level) {
            lpvar w = m_level2var[level];
            ++num_rounds;
            lp::constraint_index conflict = repair_variable(w);
            TRACE(arith, display_constraint(tout << "repair lvl:" << level << " v" << w << ": ", conflict)
                             << " in bounds " << in_bounds(w) << " is tabu " << m_tabu.contains(conflict) << "\n");
            if (conflict == lp::null_ci)
                continue;
            SASSERT(constraint_is_false(conflict));
            if (constraint_is_conflict(conflict)) {
                SASSERT(m_conflict_dep.empty());
                m_conflict_dep.push_back(conflict);
                return true;
            }

            if (m_tabu.contains(conflict))  // already attempted to repair this constraint without success
                continue;

            m_tabu.insert(conflict);
            for (lp::constraint_index ci = constraint_lim; ci < m_constraints.size(); ++ci)
                insert_max_var(ci);
            constraint_lim = m_constraints.size();

            auto p = m_constraints[conflict].p;
            SASSERT(!p.free_vars().empty());
            if (!p.free_vars().contains(w))
                // backtrack decision to max variable in ci
                level = std::min(max_level(m_constraints[conflict]) - 1, level);
        }
        if (num_rounds >= max_rounds)
            return false;
        if (constraint_size < m_constraints.size()) {
            // TODO check sat wrt linear constraints
            return true;
        }
        return false;
    }
    // If hitting a variable that cannot be repaired, create a decision based on the value conflict.
    // Attempts to repair a variable can result in a new conflict obtained from vanishing polynomials
    // or conflicting bounds. The conflicts are assumed to contain variables of lower levels and
    // repair of those constraints are re-attempted.
    // If a variable is in a false constraint that cannot be repaired, pick a non-fixed
    // variable from the constraint and tighten its bound.
    // 
    bool stellensatz2::decide() {

        rational value;
        lp::lconstraint_kind k;
        lpvar w;
        if (!find_split(w, value, k))
            return false;

        SASSERT(k == lp::lconstraint_kind::LE || k == lp::lconstraint_kind::GE);
        bool is_upper = k == lp::lconstraint_kind::LE;
        SASSERT(!is_upper || !has_lo(w) || lo_val(w) <= value);
        SASSERT(is_upper || !has_hi(w) || hi_val(w) >= value);
        add_constraint(pddm.mk_var(w) - value, k, assumption_justification());
        m_values[w] = value;
        TRACE(arith, tout << "decide v" << w << " " << k << " " << value << "\n");
        IF_VERBOSE(3, verbose_stream() << "decide v" << w << " " << k << " " << value << "\n");
        SASSERT(in_bounds(w));
        SASSERT(well_formed_var(w));
        SASSERT(well_formed_last_constraint());
        ++c().lp_settings().stats().m_stellensatz.m_num_decisions;
        // verbose_stream() << "split " << m_num_scopes << "\n";
        return true;
    }

    unsigned stellensatz2::max_level(constraint const &c) const {
        unsigned level = 0;
        for (auto v : c.p.free_vars())
            level = std::max(level, m_var2level[v]);
        return level;
    }

    unsigned stellensatz2::get_level(justification const& j) const {
        unsigned level = 0;
        for (auto cij : justification_range(*this, j))
            level = std::max(level, m_levels[cij]);
        return level;
    }

    bool stellensatz2::constraint_is_propagating(dep_interval const &ivp, dep_interval const &ivq, lpvar x,
                                                 svector<lp::constraint_index> &cs, lp::lconstraint_kind &k,
                                                 rational &value) {

        auto const &ivx = get_interval(pddm.mk_var(x));
        auto above_lower_bound = [&](rational const &r, bool is_strict) {
            if (ivx.m_lower_inf)
                return true;
            if (ivx.m_lower < r)
                return true;
            if (ivx.m_lower == r && !ivx.m_lower_open && is_strict)
                return true;
            return false;
        };
        auto below_upper_bound = [&](rational const &r, bool is_strict) {
            if (ivx.m_upper_inf)
                return true;
            if (ivx.m_upper > r)
                return true;
            if (ivx.m_upper == r && !ivx.m_upper_open && is_strict)
                return true;
            return false;
        };
        // hi_p > 0
        // 0 <= lo_q <= -q
        // => x >= lo_q / hi_p
        //
        if (!ivp.m_upper_inf && ivp.m_upper > 0 && !ivq.m_lower_inf && ivq.m_lower >= 0) {
            // v >= -q / p
            auto quot = ivq.m_lower / ivp.m_upper;
            if (var_is_int(x))
                quot = ceil(quot);
            bool is_strict =
                !var_is_int(x) && (k == lp::lconstraint_kind::GT || ivq.m_lower_open || ivp.m_lower_open);
            if (above_lower_bound(quot, is_strict)) {
                TRACE(arith, tout << "new lower bound v" << x << " " << quot << "\n");
                auto d = m_dm.mk_join(ivq.m_lower_dep, ivp.m_upper_dep);
                m_dm.linearize(d, cs);
                k = is_strict ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE;
                value = quot;
                TRACE(arith, m_di.display(tout, ivp) << "\n"; m_di.display(tout, ivq) << "\n";
                      tout << "v" << x << " " << k << " " << value << " " << cs << "\n");
                return true;
            }
        }

        // hi_p >= p >= lo_p > 0
        // 0 > hi_q >= -q >= lo_q
        // => x >= lo_q / lo_p
        if (!ivp.m_lower_inf && ivp.m_lower > 0 && !ivq.m_lower_inf && ivq.m_lower <= 0) {
            auto quot = ivq.m_lower / ivp.m_lower;
            if (var_is_int(x))
                quot = ceil(quot);
            bool is_strict =
                !var_is_int(x) && (k == lp::lconstraint_kind::GT || ivq.m_lower_open || ivp.m_lower_open);
            if (above_lower_bound(quot, is_strict)) {
                TRACE(arith, tout << "new lower bound v" << x << " " << quot << "\n");
                auto d = m_dm.mk_join(ivp.m_lower_dep, ivq.m_lower_dep);
                m_dm.linearize(d, cs);
                k = is_strict ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE;
                value = quot;
                TRACE(arith, m_di.display(tout, ivp) << "\n"; m_di.display(tout, ivq) << "\n";
                      tout << "v" << x << " " << k << " " << value << " " << cs << "\n");
                return true;
            }
        }

        // p <= hi_p < 0
        // lo_q <= q <= hi_q < 0
        // => x <= lo_q / hi_p
        if (!ivp.m_upper_inf && ivp.m_upper < 0 && !ivq.m_upper_inf && !ivq.m_lower_inf && ivq.m_upper <= 0) {
            // v <= -q / p
            auto quot = ivq.m_lower / ivp.m_upper;
            if (var_is_int(x))
                quot = floor(quot);
            bool is_strict =
                !var_is_int(x) && (k == lp::lconstraint_kind::GT || ivq.m_lower_open || ivp.m_upper_open);
            if (below_upper_bound(quot, is_strict)) {
                TRACE(arith, tout << "new upper bound v" << x << " " << quot << "\n");
                auto d = m_dm.mk_join(ivq.m_upper_dep, m_dm.mk_join(ivq.m_lower_dep, ivp.m_upper_dep));
                m_dm.linearize(d, cs);
                k = is_strict ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                value = quot;
                TRACE(arith, m_di.display(tout, ivp) << "\n"; m_di.display(tout, ivq) << "\n";
                      tout << "v" << x << " " << k << " " << value << " " << cs << "\n");
                return true;
            }
        }
        // lo_p <= p < 0
        // 0 <= lo_q <= -q
        // => x <= lo_q / lo_p
        //
        if (!ivp.m_upper_inf && ivp.m_upper < 0 && !ivp.m_lower_inf && !ivq.m_lower_inf && ivq.m_lower >= 0) {
            auto quot = ivq.m_lower / ivp.m_lower;
            if (var_is_int(x))
                quot = floor(quot);
            bool is_strict =
                !var_is_int(x) && (k == lp::lconstraint_kind::GT || ivq.m_lower_open || ivp.m_lower_open);
            if (below_upper_bound(quot, is_strict)) {
                TRACE(arith, tout << "new upper bound v" << x << " " << quot << "\n");
                auto d = m_dm.mk_join(ivp.m_upper_dep, m_dm.mk_join(ivp.m_lower_dep, ivq.m_lower_dep));
                m_dm.linearize(d, cs);
                k = is_strict ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                value = quot;
                TRACE(arith, m_di.display(tout, ivp) << "\n"; m_di.display(tout, ivq) << "\n";
                      tout << "v" << x << " " << k << " " << value << " " << cs << "\n");
                return true;
            }
        }
        return false;
    }

    bool stellensatz2::well_formed() {        
        for (unsigned v = 0; v < num_vars(); ++v) 
            if (!well_formed_var(v))
                return false;    
        for (unsigned i = 0; i < m_constraints.size(); ++i)
            if (!well_formed_constraint(i))
                return false;
        unsigned level = 1;
        for (lp::constraint_index i = 0; i < m_constraints.size(); ++i) {
            if (is_decision(i)) {
                CTRACE(arith, level != m_levels[i], tout << "level of " << i << " should be " << level << "\n";
                       display_constraint(tout, i));
                if (level != m_levels[i])
                    return false;
                ++level;
            }                       
        }
        if (m_num_scopes + 1 != level) {
            TRACE(arith, tout << "num scopes set to " << m_num_scopes << " but there are " << level -1 << " decisions\n");
            return false;
        }
        return true;
    }

    //
    // integer variables have only non-strict bounds
    // bounds are assigned at monotonically increasing levels
    // previous bounds are the same sign (lower or upper bounds)
    // previous bounds are weaker
    // previous bounds are for the same variable
    // 
    bool stellensatz2::well_formed_constraint(unsigned ci) const { 
        if (is_decision(ci))
            return true;
        auto j = m_justifications[ci];
        auto correct_level = get_level(j) == m_levels[ci];
        CTRACE(arith, !correct_level, display_constraint(tout << "bad level ", ci));
        if (!correct_level)
            return false;
        return true;
    }

    //
    // values of variables are within bounds unless the bounds are conflicting
    // m_lower[v], m_upper[v] are annotated by the same variable v.
    //
    bool stellensatz2::well_formed_var(lpvar v) {
        // bounds of variables are never empty
        auto const &i = get_interval(pddm.mk_var(v));
        if (m_di.is_empty(i)) {
            TRACE(arith, display_verbose(tout << "empty interval for v" << v << "\n"));
            return false;
        }
        return true;
    }

    unsigned_vector stellensatz2::antecedents(u_dependency *d) const { 
        unsigned_vector cs;
        m_dm.linearize(d, cs);
        return cs;
    }


    void stellensatz2::updt_params(params_ref const& p) {
        smt_params_helper sp(p);
        m_config.max_degree = sp.arith_nl_stellensatz_max_degree();
        m_config.max_conflicts = sp.arith_nl_stellensatz_max_conflicts();
        m_config.max_constraints = sp.arith_nl_stellensatz_max_constraints();
        m_config.strategy = sp.arith_nl_stellensatz_strategy();
    }


    // Solver component
    // check LRA feasibilty
    // (partial) check LIA feasibility
    // try patch LIA model
    // option: iterate by continuing saturation based on partial results
    // option: add incremental linearization axioms
    // option: detect squares and add axioms for violated squares
    // option: add NIA filters (non-linear divisbility axioms)    


    void stellensatz2::solver::init() {
        lra_solver = alloc(lp::lar_solver);
        int_solver = alloc(lp::int_solver, *lra_solver);
        m_ex.clear();
        m_internal2external_constraints.reset();
        m_monomial_factory.reset();
        auto &src = s.c().lra_solver();
        auto &dst = *lra_solver;
        for (unsigned v = 0; v < src.number_of_vars(); ++v)
            dst.add_var(v, src.var_is_int(v));                   
        
        for (lp::constraint_index ci = 0; ci < s.m_constraints.size(); ++ci) {
            auto const &[p, k] = s.m_constraints[ci];
            auto [t, offset] = to_term_offset(p);
            auto coeffs = t.coeffs_as_vector();
            if (coeffs.empty())
                continue;
            SASSERT(!coeffs.empty());
            auto ti = dst.add_term(coeffs, dst.number_of_vars());
            auto new_ci = dst.add_var_bound(ti, k, -offset);
            m_internal2external_constraints.setx(new_ci, ci, ci);
        }
    }

    stellensatz2::term_offset stellensatz2::solver::to_term_offset(dd::pdd const &p) {
        term_offset to;
        for (auto const &[coeff, vars] : p) {
            if (vars.empty())
                to.second += coeff;
            else
                to.first.add_monomial(coeff, m_monomial_factory.mk_monomial(*lra_solver, vars));
        }
        return to;
    }

    lbool stellensatz2::solver::solve(svector<lp::constraint_index> &core) {
        init();
        lbool r = solve_lra();
        if (r == l_true) 
            r = solve_lia();        
        if (r == l_false) { 
            core.reset();
            for (auto p : m_ex)
                core.push_back(m_internal2external_constraints[p.ci()]);
        }
        return r;
    }

    lbool stellensatz2::solver::solve_lra() {
        auto status = lra_solver->find_feasible_solution();;
        if (lra_solver->is_feasible())
            return l_true;
        if (status == lp::lp_status::INFEASIBLE) {
            lra_solver->get_infeasibility_explanation(m_ex);
            return l_false;
        }
        return l_undef;
    }

    lbool stellensatz2::solver::solve_lia() {
        switch (int_solver->check(&m_ex)) {
        case lp::lia_move::sat: 
            return l_true;
        case lp::lia_move::conflict: 
            return l_false;
        default:  // TODO: an option is to perform (bounded) search here to get an LIA verdict.
            return l_undef;
        }
        return l_undef;
    }

    // update values using the model
    void stellensatz2::solver::update_values(vector<rational>& values) {
        std::unordered_map<lpvar, rational> _values;
        lra_solver->get_model(_values);
        unsigned sz = values.size();
        for (unsigned i = 0; i < sz; ++i) {
            values[i] = _values[i];
            if (s.var_is_int(i) && !values[i].is_int())
                values[i] = ceil(values[i]);
        }
        TRACE(arith, for (unsigned i = 0; i < sz; ++i) tout << "j" << i << " := " << values[i] << "\n";);
    }

    lp::constraint_index stellensatz2::repair_variable(lp::lpvar v) {
        auto [inf, sup, conflict, lo, hi] = find_bounds(v);

        CTRACE(arith, inf != lp::null_ci || sup != lp::null_ci || conflict != lp::null_ci, 
                tout << "bounds for v" << v << " @" << m_var2level[v] << "\n";
                display_constraint(tout << "lo: ", inf); 
                display_constraint(tout << "hi: ", sup);
                display_constraint(tout << "conflict: ", conflict));

        if (conflict != lp::null_ci) 
            return conflict;        

        if (inf == lp::null_ci && sup == lp::null_ci)
            return inf;

        if (!constraint_is_false(inf) && !constraint_is_false(sup))
            return lp::null_ci;

        TRACE(arith, tout << "v" << v << " @" << m_var2level[v] << "\n");

        bool strict_lo = inf != lp::null_ci && m_constraints[inf].k == lp::lconstraint_kind::GT;
        bool strict_hi = sup != lp::null_ci && m_constraints[sup].k == lp::lconstraint_kind::GT;
        bool strict = strict_lo || strict_hi;

        if (inf == lp::null_ci) {
            SASSERT(sup != lp::null_ci);
            if (strict_hi) {
                if (has_lo(v))
                    hi = (hi + lo_val(v)) / 2;
                else
                    hi = hi - 1;
            }
            CTRACE(arith, !in_bounds(v, hi), display_var_range(tout << "repair v" << v << " to hi " << hi << "\n", v) << "\n");
            SASSERT(in_bounds(v, hi));
            m_values[v] = hi;            
            SASSERT(in_bounds(v));
        }
        else if (sup == lp::null_ci) {
            SASSERT(inf != lp::null_ci);
            if (strict_lo) {
                if (has_hi(v))
                    lo = (lo + hi_val(v)) / 2;
                else
                    lo = lo + 1;
            }
            CTRACE(arith, !in_bounds(v, lo),
                   display_var_range(tout << "repair v" << v << " to lo " << lo << "\n", v) << "\n";
                   display(tout));
            SASSERT(in_bounds(v, lo));
            m_values[v] = lo;
            SASSERT(in_bounds(v));
        }
        else if ((!strict && lo <= hi) || lo < hi) {
            // repair v by setting it between lo and hi assuming it is integral when v is integer

            auto mid = (lo + hi) / 2;
            if (var_is_int(v) && ceil(lo) <= hi)
                mid = ceil(lo);

            SASSERT(in_bounds(v, mid));
            TRACE(arith, tout << "repair v" << v << " := " << mid << " / " << m_values[v] << " lo: " << lo
                              << " hi: " << hi << "\n");
            m_values[v] = mid;
            SASSERT(in_bounds(v));
        }
        else {
            TRACE(arith, tout << "cannot repair v" << v << " between " << lo << " and " << hi << " " << (lo > hi)
                              << " is int " << var_is_int(v) << "\n";
                  display_constraint(tout, inf); display_constraint(tout, sup););
            auto res = resolve_variable(v, inf, sup);
            TRACE(arith, display_constraint(tout << "resolve ", res));
            if (constraint_is_false(res)) 
                return res;            
        }
        return lp::null_ci;
    }        

    bool stellensatz2::find_split(lpvar &v, rational &r, lp::lconstraint_kind &k) { 
        uint_set tried;                
        bool found = false;
        unsigned n = 0;
        for (lpvar w = 0; w < m_level2var.size(); ++w) {
            if (var_is_int(w) && !value(w).is_int()) {
                if (is_fixed(w))
                    continue;
                if (m_split_count[w] > m_config.max_splits_per_var)
                    continue;
                if (c().random(++n) != 0)
                    continue;
                r = floor(m_values[w]);
                k = lp::lconstraint_kind::LE;
                v = w;
                found = true;
            }
        }
        if (found) {
            ++m_split_count[v];
            IF_VERBOSE(1, verbose_stream() << "split v" << v << " " << m_split_count[v] << "\n");
        }
        return found;
    }

    void stellensatz2::set_in_bounds(lpvar v) {
        if (in_bounds(v))
            return;
        auto const &i = get_interval(pddm.mk_var(v));
        if (m_di.is_empty(i))
            return;
        if (i.m_lower_inf && i.m_upper_inf) {
            m_values[v] = rational::zero();
            return;
        }
        if (i.m_lower_inf)
            m_values[v] = i.m_upper_open ? i.m_upper - 1 : i.m_upper;
        else if (i.m_upper_inf)
            m_values[v] = i.m_lower_open ? i.m_lower + 1 : i.m_lower;
        else if (i.m_lower_open || i.m_upper_open)
            m_values[v] = (i.m_lower + i.m_lower) / 2;
        else
            m_values[v] = i.m_lower;
        SASSERT(in_bounds(v));
    }

    bool stellensatz2::in_bounds(lpvar v, rational const& value) const {
        auto const &i = get_interval(pddm.mk_var(v));
        if (m_di.is_above(i, value))
            return false;
        if (m_di.is_below(i, value))
            return false;
        return true;
    }

    //
    // Enumerate polynomial inequalities p*v + q >= 0
    // where variables in p, q are at levels below v.
    // If M(p) = 0 and M(q) < 0, return q >= 0 and assume p = 0
    // Otherwise, return greatest lower and least upper bounds for v based on polynomial inequalities.
    // 
    stellensatz2::repair_var_info stellensatz2::find_bounds(lpvar v) {
        repair_var_info result;
        auto &[inf, sup, van, lo, hi] = result;        
        for (auto ci : m_max_occurs[v]) {
            //
            // consider only constraints where v is maximal
            // and where the degree of constraints is bounded
            // for lower and upper bounds only constraints where v
            // occurs pseudo-linearly are considered
            //
            auto const &p = m_constraints[ci].p;
            auto const &vars = p.free_vars();
            TRACE(arith_verbose, display_constraint(tout, ci); for (auto j : vars) tout
                                                               << "j" << j << " deg: " << p.degree(j)
                                                               << " lvl: " << m_var2level[j]
                                                  << "\n";);
        
            

            lp::constraint_index q_ge_0 = lp::null_ci;

            auto f = factor(v, ci);
            q_ge_0 = vanishing(v, f, ci);
            if (q_ge_0 != lp::null_ci) {
                if (!constraint_is_true(q_ge_0)) {
                    van = q_ge_0;
                    return result;
                }
                TRACE(arith_verbose, display_constraint(tout << "vanished j" << v << " in ", ci);
                      display_constraint(tout << " to ", q_ge_0););
                continue;
            }
            
            if (f.degree > 1)
                continue;
            auto p_value = value(f.p);
            auto q_value = value(f.q);
            SASSERT(f.degree == 1);
            SASSERT(p_value != 0);
            auto quot = -q_value / p_value;
            if (p_value < 0) {
                if (var_is_int(v))
                    quot = floor(quot);
                // p*x + q >= 0  =>  x <= -q / p if p < 0
                if (sup == lp::null_ci || hi > quot) {
                    hi = quot;
                    sup = ci;
                }
                else if (hi == quot && m_constraints[ci].k == lp::lconstraint_kind::GT) {
                    sup = ci;
                }
            }
            else {
                if (var_is_int(v))
                    quot = ceil(quot);
                // p*x + q >= 0  =>  x >= -q / p if p > 0
                if (inf == lp::null_ci || lo < quot) {
                    lo = quot;
                    inf = ci;
                }
                else if (lo == quot && m_constraints[ci].k == lp::lconstraint_kind::GT) {
                    inf = ci;
                }
            }
        }    
        return result;
    }

    void stellensatz2::move_up(lpvar v) {
        auto l = m_var2level[v];
        if (l == 0)
            return;
        auto l0 = c().random(l);
        auto w = m_level2var[l0];
        m_var2level[v] = l0;
        m_var2level[w] = l;
        m_level2var[l0] = v;
        m_level2var[l] = w;
    }   

    std::ostream &stellensatz2::display(std::ostream &out) const {
        for (unsigned v = 0; v < num_vars(); ++v)
            display_var_range(out, v) << "\n";

        for (unsigned ci = 0; ci < m_constraints.size(); ++ci)
            display_constraint(out, ci);

        return out;
    }

    std::ostream &stellensatz2::display_verbose(std::ostream &out) const {
        
        display(out);

        // Display propagation data structures
        out << "\n=== Propagation State ===\n";
        
        // Display polynomial queue
        out << "Polynomial queue (qhead=" << m_prop_qhead << "):\n";
        for (unsigned i = 0; i < m_polynomial_queue.size(); ++i) {
            out << "  [" << i << "]" << (i < m_prop_qhead ? " (processed)" : "") << " "
            << m_polynomial_queue[i].first << "\n";
        }
        
        // Display intervals
        out << "\nIntervals:\n";
        for (unsigned idx = 0; idx < m_intervals.size(); ++idx) {
            auto const& ivs = m_intervals[idx];
            if (ivs.empty())
                continue;
            auto const& iv = *ivs.back();
            out << "  [" << idx << "] ";
            m_di.display(out, iv) << "\n";
        }
        
        // Display parents
        out << "\nParents:\n";
        for (unsigned idx = 0; idx < m_parents.size(); ++idx) {
            auto const& parents = m_parents[idx];
            if (parents.empty())
                continue;
            out << "  [" << idx << "] -> { ";
            bool first = true;
            for (auto const& p : parents) {
                if (!first) out << ", ";
                first = false;
                p.display(out);
            }
            out << " }\n";
        }
        
        // Display factors
        out << "\nFactors:\n";
        for (unsigned idx = 0; idx < m_factors.size(); ++idx) {
            auto const& factors = m_factors[idx];
            if (factors.empty())
                continue;
            out << "  [" << idx << "]:\n";
            for (auto const& [x, f, ci] : factors) 
                out << "    x" << x << " * ( " << f.p << ") + (" << f.q << ") (" << ci << ") " << m_constraints[ci].p << "\n";
            
        }
        
        return out;
    }

    std::ostream &stellensatz2::display_var_range(std::ostream &out, lpvar v) const {
        out << "v" << v << " " << m_values[v] << " ";
        return m_di.display(out, get_interval(pddm.mk_var(v)));
    }

    std::ostream &stellensatz2::display_product(std::ostream &out, svector<lpvar> const &vars) const {
        bool first = true;
        for (auto v : vars) {
            if (first)
                first = false;
            else
                out << " * ";
            out << "j" << v;
        }
        return out;
    }

    std::ostream &stellensatz2::display(std::ostream &out, term_offset const &t) const {
        bool first = true;
        for (auto [v, coeff] : t.first) {
            c().display_coeff(out, first, coeff);
            first = false;
            out << pp_j(*this, v);
        }
        if (t.second != 0)
            out << " + " << t.second;
        return out;
    }

    std::ostream &stellensatz2::display_var(std::ostream &out, lpvar j) const {
        if (c().is_monic_var(j))
            return display_product(out, c().emon(j).vars());
        else
            return out << "j" << j;
    }

    std::ostream &stellensatz2::display_constraint(std::ostream &out, lp::constraint_index ci) const {
        if (ci == lp::null_ci)
            return out << "(null)\n";
        bool is_true = constraint_is_true(ci);
        auto const &[p, k] = m_constraints[ci];
        auto level = m_levels[ci];
        display_constraint(out << "(" << ci << ") @" << level << ": ", m_constraints[ci])
               << (is_true ? " [true] " : " [false] ") << "(" << value(p) << " " << k << " 0)\n";
        auto const &j = m_justifications[ci];
        return display(out << "\t<- ", j) << "\n";
    }

    std::ostream &stellensatz2::display_constraint(std::ostream &out, constraint const &c) const {
        auto const &[p, k] = c;
        p.display(out);
        return out << " " << k << " 0";
    }
    
    std::ostream &stellensatz2::display(std::ostream &out, justification const &j) const {
        if (std::holds_alternative<external_justification>(j)) {
            auto dep = std::get<external_justification>(j).dep;
            unsigned_vector cs;
            c().lra_solver().dep_manager().linearize(dep, cs);
            for (auto c : cs)
                out << "[o " << c << "] ";  // constraint index from c().lra_solver.
        }
        else if (std::holds_alternative<addition_justification>(j)) {
            auto m = std::get<addition_justification>(j);
            out << "(" << m.left << ") + (" << m.right << ")";
        }
        else if (std::holds_alternative<eq_justification>(j)) {
            auto &m = std::get<eq_justification>(j);
            out << "(" << m.left << ") & (" << m.right << ")";
        }
        else if (std::holds_alternative<substitute_justification>(j)) {
            auto m = std::get<substitute_justification>(j);
            out << "(" << m.ci << ") (" << m.ci_eq << ") by j" << m.v << " := " << m.p;
        }
        else if (std::holds_alternative<propagation_justification>(j)) {
            auto &m = std::get<propagation_justification>(j);
            out << "propagate ";
            for (auto c : m.cs)
                out << "(" << c << ") ";
        }
        else if (std::holds_alternative<multiplication_justification>(j)) {
            auto m = std::get<multiplication_justification>(j);
            out << "(" << m.left << ") * (" << m.right << ")";
        }
        else if (std::holds_alternative<multiplication_poly_justification>(j)) {
            auto m = std::get<multiplication_poly_justification>(j);
            out << m.p << " * (" << m.ci << ")";
        }
        else if (std::holds_alternative<division_justification>(j)) {
            auto m = std::get<division_justification>(j);
            out << "(" << m.ci << ") / (" << m.divisor << ")";
        }
        else if (std::holds_alternative<assumption_justification>(j)) {
            out << "assumption";
        }
        else if (std::holds_alternative<gcd_justification>(j)) {
            auto m = std::get<gcd_justification>(j);
            out << " gcd (" << m.ci << ")";
        }
        else if (std::holds_alternative <bound_propagation_justification>(j)) {
            auto const& m = std::get<bound_propagation_justification>(j);
            out << " bound propagation (" << m.ci << ") with " << m.cs;
        }
        else
            UNREACHABLE();
        return out;
    }

    std::ostream &stellensatz2::display_lemma(std::ostream &out, lp::explanation const &ex) {
        m_constraints_in_conflict.reset();
        svector<lp::constraint_index> todo;
        for (auto c : ex)
            todo.push_back(c.ci());
        for (unsigned i = 0; i < todo.size(); ++i) {
            auto ci = todo[i];
            if (m_constraints_in_conflict.contains(ci))
                continue;
            m_constraints_in_conflict.insert(ci);
            out << "(" << ci << ") ";
            display_constraint(out, ci);
            auto const& j = m_justifications[ci];
            for (auto cij : justification_range(*this, j))
                todo.push_back(cij);
        }
        return out;
    }

    //
    // collect variables that are defined x + p >= 0: d1, -x - p >= 0 : d2.
    // substitute x by p elsewhere. 
    // Accumulate dependencies from d1, d2 into substituted (can be a propagation justification)
    //
    void stellensatz2::simplify() { 
        TRACE(arith, tout << "simplify\n");
        using var_ci_vector = svector<std::pair<unsigned, lp::constraint_index>>; 
        struct eq_info {
            lpvar v;
            dd::pdd eq;
            lp::constraint_index ci1, ci2;
        };
        u_map<var_ci_vector> bounds;
        vector<dd::pdd> pdds;
        vector<eq_info> eqs;
        for (unsigned ci = 0; ci < m_constraints.size(); ++ci) {
            auto const& [p, k] = m_constraints[ci];
            bool is_le = true;
            if (k != lp::lconstraint_kind::GE)
                continue;
            for (auto const &[coeff, vars] : p) {
                if (vars.size() != 1)
                    continue;
                if (coeff != 1 && coeff != -1)
                    continue;
                auto v = vars[0];
                auto &qs = bounds.insert_if_not_there(v, var_ci_vector());
                auto mp = -p;
                for (auto [q, ci2] : qs) {
                    auto Q = pdds[q];
                    if (mp != Q)
                        continue;
                    eqs.push_back({v, coeff == 1 ? -p : p, ci, ci2});                    
                }
                qs.push_back({pdds.size(), ci});
                pdds.push_back(p);
            }
        }
        uint_set tracked;
        for (auto [v, p, ci1, ci2] : eqs) {
            if (tracked.contains(ci1) || tracked.contains(ci2))
                continue;
            auto q = p + pddm.mk_var(v);
            if (q.free_vars().contains(v))
                continue;
            tracked.insert(ci1);
            tracked.insert(ci2);
            unsigned sz = m_constraints.size();
            for (unsigned ci = 0; ci < sz; ++ci) {
                auto const &[p, k] = m_constraints[ci];
                if (!p.free_vars().contains(v))
                    continue;
                auto r = p.subst_pdd(v, q);
                if (r.is_val())
                    continue;

                svector<lp::constraint_index> assumptions;
                assumptions.push_back(ci1);
                assumptions.push_back(ci2);
                assumptions.push_back(ci);
                propagation_justification prop{assumptions};
                add_constraint(r, k, prop);
            }
        }
    }

    // incremental bounds propagation
    // When adding a new bound x >= r, then
    // set up to walk all parents of x in constraints
    // recompute bounds for every of these sub-expressions
    // propagate recomputed bounds up if they are stronger
    // For sub-expressions that correspond to factors, perform
    // bounds propagations
    // For sub-expressions that correspond to constraints check that bounds have
    // non-empty intersection with the bound imposed by the constraint
    
    // 1. Life-time management of sub-expressions and insertion into propagation queue
    void stellensatz2::push_propagation(lp::constraint_index ci) {
        auto [p, k] = m_constraints[ci];
        m_scopes.push_back(
            {m_parent_trail.size(), 
             m_factor_trail.size(), 
             m_polynomial_queue.size(), 
             m_interval_trail.size(), 
             m_parent_constraints_trail.size(),
             m_prop_qhead});

        insert_parents(p);
        insert_parents(p, ci);
        for (auto x : p.free_vars()) {
            auto f = factor(x, ci);
            if (f.degree > 1)
                continue;
            insert_parents(f.p);
            insert_parents(f.q);
            insert_factor(f.p, x, f, ci);
            insert_factor(f.q, x, f, ci);
        }

        // 2 new bound is added, then update intervals and queue up for propagation
        auto const &b = m_bounds[ci];

        if (b.q.is_var()) 
            m_polynomial_queue.push_back({b.q, ci});        
        else if (b.mq.is_var()) 
            m_polynomial_queue.push_back({b.mq, ci});
        
    }

    void stellensatz2::insert_parents(dd::pdd const &p, lp::constraint_index ci) {
        m_parent_constraints.reserve(p.index() + 1);
        m_parent_constraints[p.index()].push_back(ci);
        m_parent_constraints_trail.push_back(p.index());
    }

    void stellensatz2::insert_parents(dd::pdd const &p) {
        if (m_is_parent.get(p.index(), false) || p.is_val())
            return;
        m_is_parent.setx(p.index(), true, false);
        m_parent_trail.push_back(p);
        m_intervals.reserve(p.index() + 1);
        m_intervals[p.index()].push_back(alloc(dep_interval));
        insert_child(p.lo(), p);
        insert_child(p.hi(), p);
    }

    void stellensatz2::insert_child(dd::pdd const &child, dd::pdd const &parent) {
        if (child.is_val())
            return;
        m_parents.reserve(child.index() + 1);
        m_parents[child.index()].push_back(parent);       
        insert_parents(child);
    }

    void stellensatz2::insert_factor(dd::pdd const &p, lpvar x, factorization const &f, lp::constraint_index ci) {
        if (p.is_val())
            return;
        m_factors.reserve(p.index() + 1);
        m_factors[p.index()].push_back({x, f, ci});
        m_factor_trail.push_back(p.index());
    }
    
    void stellensatz2::pop_propagation(lp::constraint_index ci) {
        auto const &s = m_scopes[ci];
        while (m_factor_trail.size() > s.factors_lim) {
            auto p_index = m_factor_trail.back();
            m_factors[p_index].pop_back();
            m_factor_trail.pop_back();
        }
        while (m_parent_trail.size() > s.parents_lim) {
            auto p = m_parent_trail.back();
            m_is_parent[p.index()] = false;
            if (!p.lo().is_val())
                m_parents[p.lo().index()].pop_back();
            if (!p.hi().is_val())
                m_parents[p.hi().index()].pop_back();
            m_parent_trail.pop_back();
        }
        m_polynomial_queue.shrink(s.polynomial_lim);
        while (m_parent_constraints_trail.size() > s.parent_constraints_lim) {
            auto p_index = m_parent_constraints_trail.back();
            m_parent_constraints[p_index].pop_back();
            m_parent_constraints_trail.pop_back();
        }

        while (m_interval_trail.size() > s.interval_lim) {
            auto p_index = m_interval_trail.back(); 
            auto iv = m_intervals[p_index].back();
            m_di.del(*iv);
            dealloc(iv);
            m_intervals[p_index].pop_back();
            m_interval_trail.pop_back();
        }
        m_prop_qhead = s.qhead; 
        m_scopes.pop_back();
    }
      
    void stellensatz2::propagate() {
        while (m_prop_qhead < m_polynomial_queue.size() && !is_conflict() && c().reslim().inc()) {
            auto [p, ci] = m_polynomial_queue[m_prop_qhead++];
            propagate_intervals(p, ci);
        }
    }

    bool stellensatz2::is_better(dep_interval const &new_iv, dep_interval const &old_iv) {
        auto &m = m_di.num_manager();
        if (old_iv.m_lower_inf && !new_iv.m_lower_inf)
            return true;
        if (old_iv.m_upper_inf && !new_iv.m_upper_inf)
            return true;
        if (!new_iv.m_lower_inf && !old_iv.m_lower_inf &&
            (m.gt(new_iv.m_lower, old_iv.m_lower) ||
             (m.eq(new_iv.m_lower, old_iv.m_lower) && new_iv.m_lower_open && !old_iv.m_lower_open)))
            return true;

        if (!new_iv.m_upper_inf && !old_iv.m_upper_inf &&
            (m.gt(old_iv.m_upper, new_iv.m_upper) ||
             (m.eq(new_iv.m_upper, old_iv.m_upper) && new_iv.m_upper_open && !old_iv.m_upper_open)))
            return true;

        return false;
    }

    dep_interval const &stellensatz2::get_interval(dd::pdd const &p) const {
        m_intervals.reserve(p.index() + 1);
        auto &ivs = m_intervals[p.index()];
        if (!ivs.empty())
            return *ivs.back();

        ivs.push_back(alloc(dep_interval));
        m_interval_trail.push_back(p.index());
        if (p.is_val()) 
            m_di.set_value(*ivs.back(), p.val());                
        return *ivs.back();
    }

    bool stellensatz2::strengthen_interval(dep_interval const &new_iv, dd::pdd const &p) {
        SASSERT(!p.is_val());
        SASSERT(!m_di.is_empty(new_iv));
        auto &old_iv = get_interval(p);

        if (!is_better(new_iv, old_iv))
            return false;
        
        m_intervals[p.index()].push_back(alloc(dep_interval));
        m_di.set<dep_intervals::with_deps>(*m_intervals[p.index()].back(), new_iv);
        m_interval_trail.push_back(p.index());
        return true;
    }

    void stellensatz2::propagate_intervals(dd::pdd const &p, lp::constraint_index ci) {
        if (is_conflict())
            return;
        if (ci != lp::null_ci) {
            auto [poly, k] = m_constraints[ci];
            auto const &b = m_bounds[ci];
            auto &m = m_di.num_manager();
            scoped_dep_interval new_iv(m_di);
            bool is_strict = k == lp::lconstraint_kind::GT;
            if (p == b.q) {
                auto const &iv = get_interval(b.q);
                m_di.set_lower_is_inf(new_iv, false);
                m_di.set_lower(new_iv, b.m_value);
                m_di.set_lower_is_open(new_iv, is_strict);
                m_di.set_lower_dep(new_iv, b.d);
                if (!iv.m_upper_inf)
                    m_di.copy_upper_bound<dep_intervals::with_deps>(iv, new_iv);
                if (is_bounds_conflict(new_iv))
                    return;
                if (!strengthen_interval(new_iv, b.q))
                    return;
            }
            else {
                auto const &iv = get_interval(b.mq);
                m_di.set_upper_is_inf(new_iv, false);
                m_di.set_upper_is_open(new_iv, is_strict);
                m_di.set_upper_dep(new_iv, b.d);
                m_di.set_upper(new_iv, -b.m_value);
                if (!iv.m_lower_inf)
                    m_di.copy_lower_bound<dep_intervals::with_deps>(iv, new_iv);
                if (is_bounds_conflict(new_iv))
                    return;
                if (!strengthen_interval(new_iv, b.mq))
                    return;
            }
        }

        // check constraints
        m_parent_constraints.reserve(p.index() + 1);
        for (auto ci : m_parent_constraints[p.index()]) {
            auto const &[poly, k] = m_constraints[ci];
            auto &iv_poly = get_interval(poly);
            if (constraint_is_bound_conflict(ci, iv_poly))
                return;  // conflict detected
        }

        // propagate to factors
        m_factors.reserve(p.index() + 1);
        for (auto const &[x, f, ci] : m_factors[p.index()]) {
            scoped_dep_interval iv_mq(m_di);
            auto &iv_p = get_interval(f.p);
            auto &iv_q = get_interval(f.q);
            m_di.neg<dep_intervals::with_deps>(iv_q, iv_mq);
            auto [p, k] = m_constraints[ci];  // p == f.p * x + f.q
            SASSERT(p == (f.p * pddm.mk_var(x)) + f.q);
            rational value;
            svector<lp::constraint_index> cs;
            if (constraint_is_propagating(iv_p, iv_mq, x, cs, k, value))
                propagate_constraint(x, k, value, ci, cs);
            if (is_conflict())
                return;
        }

        // for each parent of p, propagate updated intervals
        m_parents.reserve(p.index() + 1);
        for (auto parent : m_parents[p.index()]) {
            SASSERT(!parent.is_val());
            SASSERT(!is_conflict());
            scoped_dep_interval new_iv(m_di);
            auto &x = get_interval(pddm.mk_var(parent.var()));
            auto &lo = get_interval(parent.lo());
            auto &hi = get_interval(parent.hi());
            SASSERT(!m_di.is_empty(x));
            SASSERT(!m_di.is_empty(lo));
            SASSERT(!m_di.is_empty(hi));
            calculate_interval(new_iv, x, lo, hi);
            if (strengthen_interval(new_iv, parent))
                m_polynomial_queue.push_back({parent, lp::null_ci});
        }
    }

    bool stellensatz2::is_bounds_conflict(dep_interval &i) {
        if (m_di.is_empty(i)) {
            m_dm.linearize(i.m_lower_dep, m_conflict_dep);
            m_dm.linearize(i.m_upper_dep, m_conflict_dep);
            return true;
        }
        return false;
    }
}