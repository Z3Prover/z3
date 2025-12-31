/*++
  Copyright (c) 2025 Microsoft Corporation


  vanishing(v, p) = (q, r) with q = 0, r >= 0 if p := q*v + r, M(q) = 0

  TODOs:

  Assumptions are added to impose sign constraints on non-linear multipliers
  or to identify vanishing polynomials.
  The sign of the assumption is based on the current candidate interpretation.
  It could be that the negation of this assumption is asserted (and is 
  false under the current candiate interpretation). 
  The procedure could loop around refining a false assumption.
  To handle this we could also track bounds of polynomials. 
  Then we can check if a bound on a polynomial is already asserted, 
  either as a case split or as an input assertion.
  To retract consequences of temporary assumed bounds we would associate
  levels with constraints and also undo and replay constraints during backjumping/backtracking.
  A bound assumption corresponds to a decision. A conflict that depends on a bound assumption
  reverts the assumptiom, and justifies it by the conflict dependencies.
  In this way we would eliminate the double nested loop: saturate looping over the search loop.

  --*/

#include "params/smt_params_helper.hpp"
#include "math/dd/pdd_eval.h"
#include "math/lp/nla_core.h"
#include "math/lp/nla_coi.h"
#include "math/lp/nla_stellensatz.h"
#include <algorithm>
#include <ostream>
#include <unordered_map>
#include <utility>
#include <variant>
#include <math/dd/dd_pdd.h>
#include "explanation.h"
#include "int_solver.h"
#include "lar_solver.h"
#include "lia_move.h"
#include "lp_settings.h"
#include "lp_types.h"
#include "nla_common.h"
#include "nla_defs.h"
#include "nla_types.h"
#include <util/debug.h>
#include <util/dependency.h>
#include <util/lbool.h>
#include <util/memory_manager.h>
#include <util/params.h>
#include <util/rational.h>
#include <util/trace.h>
#include <util/trail.h>
#include <util/uint_set.h>
#include <util/util.h>
#include <util/vector.h>

namespace nla {
    
    lpvar stellensatz::monomial_factory::mk_monomial(lp::lar_solver &lra, svector<lpvar> const &vars) {
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

    lpvar stellensatz::monomial_factory::get_monomial(svector<lpvar> const &vars) {
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

    void stellensatz::monomial_factory::init(lpvar v, svector<lpvar> const &_vars) {
        svector<lpvar> vars(_vars);
        std::sort(vars.begin(), vars.end());
        m_vars2mon.insert(vars, v);
        m_mon2vars.insert(v, vars);
    }

    stellensatz::stellensatz(core* core) : 
        common(core), 
        m_solver(*this), 
        m_coi(*core), 
        pddm(core->lra_solver().number_of_vars()), 
        m_di(m_dm, core->reslim()) {
    }

    lbool stellensatz::saturate() {
        unsigned num_conflicts = 0;
        init_solver();
        TRACE(arith, display(tout << "stellensatz before saturation\n"));
    start_saturate:
        lbool r = search();

        TRACE(arith, tout << "search " << r << ": " << m_core << "\n");

        if (r == l_undef)
            r = m_solver.solve(m_core);
        TRACE(arith, display(tout << "stellensatz after saturation " << r << "\n"));
        if (r == l_false) {
            ++num_conflicts;
            IF_VERBOSE(2, verbose_stream() << "(nla.stellensatz :conflicts " << num_conflicts << ":constraints "
                                           << m_constraints.size() << ")\n");
            if (num_conflicts >= m_config.max_conflicts)
                return l_undef;
            while (backtrack(m_core)) {
                ++c().lp_settings().stats().m_stellensatz.m_num_backtracks;
                lbool rb = m_solver.solve(m_core);
                if (rb == l_false)
                    continue;
                if (rb == l_undef)
                    return rb;
                m_solver.update_values(m_values);
                goto start_saturate;
            }
            ++c().lp_settings().stats().m_stellensatz.m_num_conflicts;
            conflict(m_core);
        }
        if (r == l_true && !set_model())
            r = l_undef;
        return r;
    }

    void stellensatz::pop_constraint() {
        auto const &[p, k, j] = m_constraints.back();
        m_constraint_index.erase({p.index(), k});             
        m_constraints.pop_back();       
    }

    void stellensatz::init_solver() {
        reset_bounds();
        m_ctrail.reset();
        m_num_scopes = 0;
        m_monomial_factory.reset();
        m_coi.init();
        m_values.reset();
        init_vars();
        init_occurs();
        init_bounds();
    }

    void stellensatz::init_vars() {
        auto const& src = c().lra_solver();
        auto sz = src.number_of_vars();
        m_lower.reset();
        m_upper.reset();
        m_split_count.reset();
        m_lower.reserve(sz, UINT_MAX);
        m_upper.reserve(sz, UINT_MAX);
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

    void stellensatz::init_bounds() {
        reset_bounds();
        for (unsigned ci = 0; ci < m_constraints.size(); ++ci)
            init_bound(ci);        
    }

    void stellensatz::init_bound(lp::constraint_index ci) {
        unsigned level = m_num_scopes;
        auto [p, k, j] = m_constraints[ci];
        if (!p.is_unilinear())
            return;
        // ax + b >= 0
        auto b = p.lo().val();
        auto a = p.hi().val();
        auto x = p.var();
        if (a > 0) {
            auto lb = -b / a;
            if (var_is_int(x))
                lb = ceil(lb);
            if (!has_lo(x) || lo_val(x) < lb ||
                (!lo_is_strict(x) && k == lp::lconstraint_kind::GT && lo_val(x) == lb)) {
                auto dep = constraint2dep(ci);
                bound_info bi(x, k, lb, level, m_lower[x], dep, ci);
                m_lower[x] = m_bounds.size();
                m_bounds.push_back(bi);
                SASSERT(well_formed_last_bound());
            }
        }
        else if (a < 0) {
            auto ub = -b / a;
            if (var_is_int(x))
                ub = floor(ub);
            k = (k == lp::lconstraint_kind::GT) ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
            if (!has_hi(x) || hi_val(x) > ub ||
                (!hi_is_strict(x) && k == lp::lconstraint_kind::LT && hi_val(x) == ub)) {
                auto dep = constraint2dep(ci);
                bound_info bi(x, k, ub, level, m_upper[x], dep, ci);
                m_upper[x] = m_bounds.size();
                m_bounds.push_back(bi);
                SASSERT(well_formed_last_bound());
            }
        }
    }

    void stellensatz::reset_bounds() { 
        while (!m_bounds.empty())
            pop_bound();
    }

    // set the model based on m_values computed by the solver
    bool stellensatz::set_model() {
        if (any_of(m_constraints, [&](auto const &c) { return !constraint_is_true(c); }))
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

    dd::pdd stellensatz::to_pdd(lpvar v) {
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

    stellensatz::term_offset stellensatz::to_term_offset(dd::pdd const &p) {
        term_offset to;
        for (auto const &[coeff, vars] : p) {
            if (vars.empty())
                to.second += coeff;
            else
                to.first.add_monomial(coeff, m_monomial_factory.get_monomial(vars));                
        }        
        return to;
    }

    bool stellensatz::has_term_offset(dd::pdd const &p) {
        for (auto const &[coeff, vars] : p) 
            if (!vars.empty() && lp::null_lpvar == m_monomial_factory.get_monomial(vars))
                return false;
        return true;
    }

    void stellensatz::init_monomial(unsigned mon_var) {
        auto &mon = c().emons()[mon_var];
        m_monomial_factory.init(mon_var, mon.vars());
    }

    lp::constraint_index stellensatz::add_var_bound(lp::lpvar v, lp::lconstraint_kind k, rational const& rhs, justification j) {
        auto p = to_pdd(v) - rhs;
        rational d(1);
        for (auto const& [c, is_constant] : p.coefficients()) 
            d = lcm(d, denominator(c));
        if (d != 1)
            p *= d;        
        return gcd_normalize(add_constraint(p, k, j));
    }

    lp::constraint_index stellensatz::add_constraint(dd::pdd p, lp::lconstraint_kind k, justification j) {
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
        m_constraints.push_back({p, k, j });
        m_constraint_index.insert({p.index(), k}, ci);
        ++c().lp_settings().stats().m_stellensatz.m_num_constraints;
        
        m_has_occurs.reserve(ci + 1);
        struct undo_constraint : public trail {
            stellensatz &s;
            undo_constraint(stellensatz& s): s(s) {}
            void undo() override {
                s.pop_constraint();
            }
        };
        m_ctrail.push_scope();
        m_ctrail.push(undo_constraint(*this));
        return ci;
    }

    lp::constraint_index stellensatz::resolve_variable(lpvar x, lp::constraint_index ci,
                                                       lp::constraint_index other_ci) {
        TRACE(arith, tout << "resolve j" << x << " between ci " << (int)ci << " and other_ci " << (int)other_ci << "\n");
        if (ci == lp::null_ci || other_ci == lp::null_ci)
            return lp::null_ci;
        auto f = factor(x, ci);
        auto g = factor(x, other_ci);
        if (f.degree != 1)
            return lp::null_ci;  // future - could handle this
        if (g.degree != 1)
            return lp::null_ci;  // not handling degree > 1
        auto p_value1 = value(f.p);
        auto p_value2 = value(g.p);
        //
        // check that p_value1 and p_value2 have different signs
        // check that other_p is disjoint from tabu
        // compute overlaps extending x
        //
        if (p_value1 == 0 || p_value2 == 0) 
            return lp::null_ci;
        if (p_value1 > 0 && p_value2 > 0)
            return lp::null_ci;
        if (p_value1 < 0 && p_value2 < 0)
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

        auto sign_f = value(f_p) < 0;
        SASSERT(value(f_p) != 0);

        // m1m2 * f_p + f.q >= 0
        // m1m2 * g_p + g.q >= 0
        //
        lp::constraint_index ci_a, ci_b;
        auto const &[other_p, other_k, other_j] = m_constraints[other_ci];
        auto const &[p, k, j] = m_constraints[ci];

        bool g_strict = other_k == lp::lconstraint_kind::GT;
        bool f_strict = k == lp::lconstraint_kind::GT;
        if (g_p.is_val() && f_p.is_val() && g_p.val() == -f_p.val())
            ci_a = ci;
        else if (g_p.is_val())
            ci_a = multiply(ci, pddm.mk_val(g_p.val()));
        else if (!sign_f)
            ci_a = multiply(ci, assume(g_p, f_strict ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE));
        else
            ci_a = multiply(ci, assume(g_p, f_strict ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE));

        if (g_p.is_val() && f_p.is_val() && g_p.val() == -f_p.val())
            ci_b = other_ci;
        else if (f_p.is_val())
            ci_b = multiply(other_ci, pddm.mk_val(f_p.val()));
        else if (sign_f)
            ci_b = multiply(other_ci, assume(f_p, g_strict ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE));
        else
            ci_b = multiply(other_ci, assume(f_p, g_strict ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE));

        auto new_ci = add(ci_a, ci_b);
        
        ++c().lp_settings().stats().m_stellensatz.m_num_resolutions;

        TRACE(arith, tout << "eliminate j" << x << ":\n"; display_constraint(tout, ci) << "\n";
              display_constraint(tout, other_ci) << "\n"; display_constraint(tout, ci_a) << "\n";
              display_constraint(tout, ci_b) << "\n"; display_constraint(tout, new_ci) << "\n");

        new_ci = factor(new_ci);

        init_occurs(new_ci);

        return new_ci;
    }

    void stellensatz::conflict(svector<lp::constraint_index> const& core) {
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
    lp::constraint_index stellensatz::vanishing(lpvar x, factorization const &f, lp::constraint_index ci) { 
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
        TRACE(arith, display_constraint(tout << "j" << x << " ", ci) << "\n";
            display_constraint(tout << "reduced ", new_ci) << "\n";
        display_constraint(tout, p_is_0) << "\n");
        init_occurs(new_ci);        
        return new_ci;
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
    lp::constraint_index stellensatz::factor(lp::constraint_index ci) {
        auto const &[p, k, j] = m_constraints[ci];
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
            TRACE(arith_verbose, display_constraint(tout, new_ci) << "\n"; display_constraint(tout, assume(pv, k1)) << "\n";);
        }
        TRACE(arith, display_constraint(tout << "factor ", new_ci) << "\n");
        return new_ci;
    }

    unsigned stellensatz::degree_of_var_in_constraint(lpvar var, lp::constraint_index ci) const {
        return m_constraints[ci].p.degree(var);
    }

    stellensatz::factorization stellensatz::factor(lpvar v, lp::constraint_index ci) {
        auto const& [p, k, j] = m_constraints[ci];
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
    bool stellensatz::backtrack(svector<lp::constraint_index> const &core) {
        reset_bounds();
        m_constraints_in_conflict.reset();
        svector<lp::constraint_index> external, assumptions;
        for (auto ci : core)
            explain_constraint(ci, external, assumptions);
        if (assumptions.empty())
            return false;
        lp::constraint_index max_ci = 0;
        for (auto ci : assumptions)
            max_ci = std::max(ci, max_ci);
        TRACE(arith, tout << "max " << max_ci << " external " << external << " assumptions " << assumptions << "\n";
              display_constraint(tout, max_ci) << "\n";);
        // TODO, we can in reality replay all constraints that don't depend on max_ci
        vector<constraint> replay;
        unsigned i = 0;
        for (auto ci : external) {
            if (ci > max_ci)
                replay.push_back(m_constraints[ci]);
            else
                external[i++] = ci;
        }
        external.shrink(i);
        auto [p, k, j] = m_constraints[max_ci];
        while (m_constraints.size() > max_ci)
            m_ctrail.pop_scope(1);
        
        for (auto const &[_p, _k, _j] : replay) {
            auto ci = add_constraint(_p, _k, _j);
            init_occurs(ci);
            external.push_back(ci);
        }
        assumptions.erase(max_ci);
        external.append(assumptions);
        propagation_justification prop{external};
        auto new_ci = add_constraint(p, negate(k), prop);
        TRACE(arith, display_constraint(tout << "backtrack ", new_ci) << "\n");
        init_occurs(new_ci);
        init_bounds();
        return true;
    }

    bool stellensatz::core_is_linear(svector<lp::constraint_index> const &core) {
        m_constraints_in_conflict.reset();
        svector<lp::constraint_index> external, assumptions;
        for (auto ci : core)
            explain_constraint(ci, external, assumptions);
        return all_of(assumptions, [&](auto ci) { return has_term_offset(m_constraints[ci].p); });
    }

    void stellensatz::explain_constraint(lp::constraint_index ci, svector<lp::constraint_index> &external,
                                         svector<lp::constraint_index> &assumptions) {
        if (m_constraints_in_conflict.contains(ci))
            return;
        m_constraints_in_conflict.insert(ci);
        auto &[p, k, b] = m_constraints[ci];
        if (std::holds_alternative<external_justification>(b)) {
            external.push_back(ci);
        }
        else if (std::holds_alternative<multiplication_justification>(b)) {
            auto &m = std::get<multiplication_justification>(b);
            explain_constraint(m.left, external, assumptions);
            explain_constraint(m.right, external, assumptions);
        }
        else if (std::holds_alternative<eq_justification>(b)) {
            auto &m = std::get<eq_justification>(b);
            explain_constraint(m.left, external, assumptions);
            explain_constraint(m.right, external, assumptions);
        }
        else if (std::holds_alternative<division_justification>(b)) {
            auto &m = std::get<division_justification>(b);
            explain_constraint(m.ci, external, assumptions);
            explain_constraint(m.divisor, external, assumptions);
        }
        else if (std::holds_alternative<substitute_justification>(b)) {
            auto &m = std::get<substitute_justification>(b);
            explain_constraint(m.ci, external, assumptions);
            explain_constraint(m.ci_eq, external, assumptions);
        }
        else if (std::holds_alternative<propagation_justification>(b)) {
            auto &m = std::get<propagation_justification>(b);
            for (auto c : m.cs)
                explain_constraint(c, external, assumptions);
        }
        else if (std::holds_alternative<addition_justification>(b)) {
            auto &m = std::get<addition_justification>(b);
            explain_constraint(m.left, external, assumptions);
            explain_constraint(m.right, external, assumptions);
        }
        else if (std::holds_alternative<multiplication_poly_justification>(b)) {
            auto &m = std::get<multiplication_poly_justification>(b);
            explain_constraint(m.ci, external, assumptions);
        }
        else if (std::holds_alternative<assumption_justification>(b)) {
            assumptions.push_back(ci);
        }
        else if (std::holds_alternative<gcd_justification>(b)) {
            auto &m = std::get<gcd_justification>(b);
            explain_constraint(m.ci, external, assumptions);
        }
        else
            UNREACHABLE();
    }

    //
    // a constraint can be explained by a set of bounds used as justifications
    // and by an original constraint.
    // 
    void stellensatz::explain_constraint(lemma_builder &new_lemma, lp::constraint_index ci, lp::explanation &ex) {
        svector<lp::constraint_index> external, assumptions;
        explain_constraint(ci, external, assumptions);
        for (auto ci : external) {
            auto &[p, k, b] = m_constraints[ci];
            auto dep = std::get<external_justification>(b);
            c().lra_solver().push_explanation(dep.dep, ex);
        }
        for (auto ci : assumptions) {
            auto &[p, k, b] = m_constraints[ci];
            auto [t, coeff] = to_term_offset(p);
            new_lemma |= ineq(t, negate(k), -coeff);
        }
    }
 
    rational stellensatz::value(dd::pdd const& p) const {
        dd::pdd_eval eval;
        eval.var2val() = [&](unsigned v) -> rational { return value(v); };
        return eval(p);
    }

    //
    // normalize constraint by dividing by gcd of coefficients
    //
    lp::constraint_index stellensatz::gcd_normalize(lp::constraint_index ci) {
        auto [p, k, j] = m_constraints[ci];
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
    
    lp::constraint_index stellensatz::assume(dd::pdd const& p, lp::lconstraint_kind k) {
        if (k == lp::lconstraint_kind::EQ) {
            auto left = assume(p, lp::lconstraint_kind::GE);
            auto right = assume(-p, lp::lconstraint_kind::GE);
            return add_constraint(p, k, eq_justification{left, right});
        }
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
        return add_constraint(p, k, assumption_justification());
    }
    
    // p1 >= lo1, p2 >= lo2 => p1 + p2 >= lo1 + lo2
    lp::constraint_index stellensatz::add(lp::constraint_index left, lp::constraint_index right) {
        auto const &[p, k1, j1] = m_constraints[left];
        auto const &[q, k2, j2] = m_constraints[right];
        lp::lconstraint_kind k = join(k1, k2);
        return gcd_normalize(add_constraint(p + q, k, addition_justification{left, right}));
    }

    // p >= 0  =>  a * p >= 0 if a > 0,
    // p = 0   => p * q = 0  no matter what q
    lp::constraint_index stellensatz::multiply(lp::constraint_index ci, dd::pdd q) {        
        auto const& [p, k, j] = m_constraints[ci];
        auto k1 = k;
        if (q.is_val() && q.val() < 0)
            k1 = swap_side(k1);
        SASSERT(q.is_val() || k1 == lp::lconstraint_kind::EQ);
        return add_constraint(p * q, k1, multiplication_poly_justification{ci, q});
    }

    lp::constraint_index stellensatz::multiply(lp::constraint_index left, lp::constraint_index right) {
        auto const &[p, k1, j1] = m_constraints[left];
        auto const &[q, k2, j2] = m_constraints[right];
        lp::lconstraint_kind k = meet(k1, k2);
        return add_constraint(p*q, k, multiplication_justification{left, right});
    }

    // p k 0, d > 0 -> p/d k 0, where q := d / d
    // q is the quotient obtained by dividing the divisor constraint, which is of the form d - 1 >= 0 or d > 0
    lp::constraint_index stellensatz::divide(lp::constraint_index ci, lp::constraint_index divisor, dd::pdd q) {
        auto const &[p, k, j] = m_constraints[ci];
        return add_constraint(q, k, division_justification{ci, divisor});
    }

    lp::constraint_index stellensatz::substitute(lp::constraint_index ci, lp::constraint_index ci_eq, lpvar v,
                                                 dd::pdd p) {
        auto const &[p1, k1, j1] = m_constraints[ci];
        auto const &[p2, k2, j2] = m_constraints[ci_eq];    
        SASSERT(k2 == lp::lconstraint_kind::EQ);
        auto q = p1.subst_pdd(v, p);
        return add_constraint(q, k1, substitute_justification{ci, ci_eq, v, p});        
    }

    void stellensatz::init_occurs() {
        m_occurs.reset();
        m_occurs.reserve(num_vars());
        for (lp::constraint_index ci = 0; ci < m_constraints.size(); ++ci) 
            init_occurs(ci);        
    }

    void stellensatz::init_occurs(lp::constraint_index ci) {
        if (ci == lp::null_ci)
            return;
        if (m_has_occurs[ci])
            return;
        struct undo_occurs : public trail {
            stellensatz & s;
            lp::constraint_index ci;
            undo_occurs(stellensatz & s, lp::constraint_index ci) : s(s), ci(ci) {}
            void undo() override {
                s.remove_occurs(ci);
            }
        };
        m_ctrail.push(undo_occurs(*this, ci));
        m_has_occurs[ci] = true;
        auto const &con = m_constraints[ci];
        for (auto v : con.p.free_vars())
            m_occurs[v].push_back(ci);        
    }

    void stellensatz::remove_occurs(lp::constraint_index ci) {
        SASSERT(m_has_occurs[ci]);
        m_has_occurs[ci] = false;            
        auto const &con = m_constraints[ci];
        for (auto v : con.p.free_vars())
            m_occurs[v].pop_back();
    }

    bool stellensatz::is_int(svector<lp::lpvar> const& vars) const {
        return all_of(vars, [&](lpvar v) { return var_is_int(v); });
    }

    bool stellensatz::is_int(dd::pdd const &p) const {
        return is_int(p.free_vars());
    }

    bool stellensatz::var_is_int(lp::lpvar v) const {
        return c().lra_solver().var_is_int(v);
    }

    bool stellensatz::constraint_is_true(lp::constraint_index ci) const {
        return ci != lp::null_ci && constraint_is_true(m_constraints[ci]);
    }

    bool stellensatz::constraint_is_false(lp::constraint_index ci) const {
        return ci != lp::null_ci && constraint_is_false(m_constraints[ci]);
    }

    bool stellensatz::constraint_is_true(constraint const &c) const {
        auto const& [p, k, j] = c;
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

    bool stellensatz::constraint_is_trivial(lp::constraint_index ci) const {
        return ci != lp::null_ci && constraint_is_trivial(m_constraints[ci]);
    }

    bool stellensatz::constraint_is_trivial(constraint const &c) const {
        auto const &[p, k, j] = c;
        if (!p.is_val())
            return false;
        if (p.val() > 0)
            return k == lp::lconstraint_kind::GE || k == lp::lconstraint_kind::GT || k == lp::lconstraint_kind::NE;
        else if (p.val() == 0)
            return k == lp::lconstraint_kind::EQ || k == lp::lconstraint_kind::GE || k == lp::lconstraint_kind::LE;
        else // p.val() < 0
            return k == lp::lconstraint_kind::LE || k == lp::lconstraint_kind::LT || k == lp::lconstraint_kind::NE;
    }

    bool stellensatz::constraint_is_conflict(lp::constraint_index ci) const {
        return ci != lp::null_ci && constraint_is_conflict(m_constraints[ci]);
    }

    bool stellensatz::constraint_is_conflict(constraint const& c) const {
        auto const &[p, k, j] = c;
        return p.is_val() &&
               ((p.val() < 0 && k == lp::lconstraint_kind::GE) 
                   || (p.val() <= 0 && k == lp::lconstraint_kind::GT));
    }

    bool stellensatz::constraint_is_bound_conflict(constraint const& c, u_dependency*& d) {
        auto const& [p, k, j] = c;
        scoped_dep_interval iv(m_di);
        interval(p, iv);
        if (iv->m_upper_inf)
            return false;
        if (iv->m_upper > 0)
            return false;
        bool is_negative = iv->m_upper < 0 || iv->m_upper_open;
        SASSERT(is_negative || iv->m_upper == 0);
        bool is_conflict = k == lp::lconstraint_kind::GT || (k == lp::lconstraint_kind::GE && is_negative);
        if (!is_conflict)
            return false;
        d = iv->m_upper_dep;
        return true;
    }

    bool stellensatz::var_is_bound_conflict(lpvar v) const {
        if (!has_lo(v))
            return false;
        if (!has_hi(v))
            return false;
        if (lo_val(v) > hi_val(v))
            return true;
        if (lo_val(v) < hi_val(v))
            return false;
        return lo_is_strict(v) || hi_is_strict(v);
    }

    // 
    // Based on current bounds for variables, compute bounds of polynomial
    // 
    void stellensatz::interval(dd::pdd p, scoped_dep_interval& iv) {
        auto &m = iv.m();
        if (p.is_val()) {
            m.set_value(iv, p.val());
            return;
        }
        scoped_dep_interval x(m), lo(m), hi(m);        
        auto v = p.var();
        auto lb = m_lower[v];
        if (lb == UINT_MAX) {
            m.set_lower_is_inf(x, true);
        }
        else {
            auto lo = m_bounds[lb];
            m.set_lower_is_inf(x, false);
            m.set_lower_is_open(x, lo.m_kind == lp::lconstraint_kind::GT);
            m.set_lower(x, lo.m_value);
            m.set_lower_dep(x, bound2dep(lb));
        }
        auto ub = m_upper[v];
        if (ub == UINT_MAX) {
            m.set_upper_is_inf(x, true);
        }
        else {
            auto hi = m_bounds[ub];
            m.set_upper_is_inf(x, false);
            m.set_upper_is_open(x, hi.m_kind == lp::lconstraint_kind::LT);
            m.set_upper(x, hi.m_value);
            m.set_upper_dep(x, bound2dep(ub));
        }
        interval(p.hi(), hi);
        interval(p.lo(), lo);
        m.mul<dep_intervals::with_deps>(x, hi, hi);
        m.add<dep_intervals::with_deps>(lo, hi, iv);          
    }

    //
    // Main search loop.
    // Resolve conflicts, propagate and case split on bounds.
    // 
    lbool stellensatz::search() { 
        init_search();   
        lbool is_sat = l_undef;
        while (is_sat == l_undef && c().reslim().inc()) {
            if (is_conflict())
                is_sat = resolve_conflict();
            else if (should_propagate())
                propagate();
            else if (!decide())
                is_sat = l_true;
        }
        if (is_sat == l_true) 
            return all_of(m_constraints, [&](auto const &c) { return constraint_is_true(c); }) ? l_true : l_undef;        
        return is_sat;
    }

    void stellensatz::init_search() {
        m_prop_qhead = 0;
        m_level2var.reset();
        m_var2level.reset();
        for (unsigned v = 0; v < m_values.size(); ++v)
            m_level2var.push_back(v);
        random_gen rand(c().random());
        shuffle(m_level2var.size(), m_level2var.begin(), rand);
           
        m_var2level.resize(m_values.size(), m_level2var.size());
        for (unsigned i = 0; i < m_level2var.size(); ++i)
            m_var2level[m_level2var[i]] = i;
        for (auto const &c : m_constraints)
            if (constraint_is_false(c))
                for (auto v : c.p.free_vars())
                    move_up(v); 
    }


    // 
    // Conflict resolution is similar to CDCL
    // walk m_bounds based on the propagated bounds
    // flip the last decision and backjump to the UIP.
    //     
    lbool stellensatz::resolve_conflict() { 
        TRACE(arith, 
              tout << "resolving conflict: "; display_constraint(tout, m_conflict) << "\n"; display(tout););
        SASSERT(is_conflict());
        m_conflict_marked_bounds.reset();
        m_conflict_marked_ci.reset();
        mark_dependencies(m_conflict_dep);
        unsigned conflict_level = 0;
        m_core.reset();
        for (auto d : m_conflict_marked_bounds) {
            auto &b = m_bounds[d];
            conflict_level = std::max(conflict_level, b.m_level);
        }
        bool found_decision = false;
        TRACE(arith, tout << "conflict level " << conflict_level << " bounds: " << m_conflict_marked_bounds 
            << " constraints: " << m_conflict_marked_ci << "\n");
        while (!found_decision && !m_bounds.empty() && !m_conflict_marked_bounds.empty()) {
            while (!m_conflict_marked_bounds.contains(m_bounds.size() - 1))
                pop_bound();

            auto const &[v, k, value, level, last_bound, is_decision, dep, ci] = m_bounds.back();

            mark_dependencies(dep);
            m_conflict_marked_bounds.remove(m_bounds.size() - 1);
            m_conflict = resolve_variable(v, m_conflict, ci);  // adds assumptions..
            if (conflict_level == 0 && ci != lp::null_ci)
                m_core.push_back(ci);
            found_decision = is_decision;
            TRACE(arith, tout << "num bounds: " << m_bounds.size() << "\n";
                  tout << "resolving on v" << v << " at level " << level << " is_decision: " << is_decision << "\n";
                  display_constraint(tout, ci) << "\n"; tout << "new conflict: ";
                  display_constraint(tout, m_conflict) << "\n";
            );
        }
        SASSERT(found_decision || conflict_level == 0);
        SASSERT(!found_decision || conflict_level != 0);
        if (conflict_level == 0) {
            for (auto ci : m_conflict_marked_ci)
                m_core.push_back(ci);
            if (m_conflict != lp::null_ci)
                m_core.push_back(m_conflict);
            reset_conflict();
            reset_bounds();
            return l_false;
        }
        if (constraint_is_conflict(m_conflict)) {
            m_core.push_back(m_conflict);
            reset_conflict();
            reset_bounds();
            return l_false;
        }

        auto [v, k, value, level, last_bound, is_decision, dep, ci] = m_bounds.back();
        SASSERT(is_decision);
        while (!m_bounds.empty() && !m_conflict_marked_bounds.contains(m_bounds.size() - 1))
            pop_bound();
        switch (k) {
        case lp::lconstraint_kind::GE:
            if (var_is_int(v)) {
                k = lp::lconstraint_kind::LE;
                value = value - 1;
            }
            else
                k = lp::lconstraint_kind::LT;
            break;
        case lp::lconstraint_kind::GT: k = lp::lconstraint_kind::LE; break;
        case lp::lconstraint_kind::LT: k = lp::lconstraint_kind::GE; break;
        case lp::lconstraint_kind::LE:
            if (var_is_int(v)) {
                k = lp::lconstraint_kind::GE;
                value = value + 1;
            }
            else
                k = lp::lconstraint_kind::GT;
            break;        
        }
        dep = nullptr;
        unsigned propagation_level = 0;
        for (auto d : m_conflict_marked_bounds) {
            dep = m_dm.mk_join(bound2dep(d), dep);
            propagation_level = std::max(propagation_level, m_bounds[d].m_level);
        }        
        for (auto ci : m_conflict_marked_ci)
            dep = m_dm.mk_join(constraint2dep(ci), dep);
        m_prop_qhead = m_bounds.size();
        bool is_upper = (k == lp::lconstraint_kind::LE) || (k == lp::lconstraint_kind::LT);
        last_bound = is_upper ? m_upper[v] : m_lower[v];
        (is_upper ? m_upper[v] : m_lower[v]) = m_bounds.size();
        m_bounds.push_back(bound_info(v, k, value, propagation_level, last_bound, dep, m_conflict));
        // set the value within bounds if the bounds are consistent.
        set_in_bounds(v);
        TRACE(arith, tout << "scopes " << m_num_scopes << "\n";
              display_bound(tout << "backjump ", m_bounds.size() - 1) << "\n");
        SASSERT(well_formed_last_bound());
        reset_conflict();
        return l_undef; 
    }   

    void stellensatz::mark_dependencies(u_dependency* d) { 
        auto [bounds, cdeps] = antecedents(d);
        for (auto a : cdeps)
            m_conflict_marked_ci.insert(a);
        for (auto a : bounds)
            m_conflict_marked_bounds.insert(a);
    }

    void stellensatz::pop_bound() { 
        auto const &[v, k, value, level, last_bound, is_decision, dep, ci] = m_bounds.back();
        bool is_upper = (k == lp::lconstraint_kind::LE) || (k == lp::lconstraint_kind::LT);
        (is_upper ? m_upper[v] : m_lower[v]) = last_bound;
        if (is_decision) {            
            m_dm.pop_scope(1);
            --m_num_scopes;
        }
        m_bounds.pop_back();
    }

    void stellensatz::propagate() {
        if (m_prop_qhead == m_bounds.size())
            return;
       
        for (; m_prop_qhead < m_bounds.size(); ++m_prop_qhead) {
            if (!c().reslim().inc())
                return;
            auto v = m_bounds[m_prop_qhead].m_var;
            if (var_is_bound_conflict(v)) {
                TRACE(arith, tout << "var is bound conflict v" << v << "\n");
                set_conflict(v);
                return;
            }
            for (unsigned i = 0; i < m_occurs[v].size(); ++i) {
                auto ci = m_occurs[v][i];
                if (false && constraint_is_true(ci))
                    continue;

                TRACE(arith, tout << "propagate v" << v << " (" << ci << ")\n");

                // detect conflict or propagate dep_intervals
                u_dependency *d = nullptr;
                if (constraint_is_bound_conflict(ci, d)) {
                    TRACE(arith, tout << "constraint is bound conflict: "; display_constraint(tout, ci) << "\n";);
                    d = m_dm.mk_join(constraint2dep(ci), d);
                    set_conflict(ci, d);
                    return;
                }

                lpvar w;
                rational value;
                lp::lconstraint_kind k;
                unsigned level = 0;
                if (constraint_is_propagating(ci, d, w, value, k)) {
                    TRACE(arith, display_constraint(tout << "constraint is propagating ", ci) << "\n";
                          tout << "v" << w << " " << k << " " << value << "\n";);

                    auto [bounds, cs] = antecedents(d);
                    for (auto a : bounds)
                        level = std::max(level, m_bounds[a].m_level);
                    SASSERT(level <= m_num_scopes);
                    bool is_upper = k == lp::lconstraint_kind::LE || k == lp::lconstraint_kind::LT;
                    bool is_strict = k == lp::lconstraint_kind::LT || k == lp::lconstraint_kind::GT;
                    auto last_bound = is_upper ? m_upper[w] : m_lower[w];

                    // block repeated bounds propagation within same level
                    if (propagation_cycle(w, value, is_upper, level, ci)) 
                        continue;                    

                    (is_upper ? m_upper[w] : m_lower[w]) = m_bounds.size();
                    d = m_dm.mk_join(constraint2dep(ci), d);
                    m_bounds.push_back(bound_info(w, k, value, level, last_bound, d, ci));

                    if (var_is_bound_conflict(w)) {
                        set_conflict(w);
                        return;
                    }

                    set_in_bounds(w);

                    CTRACE(arith, !well_formed_last_bound(), display(tout));
                    SASSERT(well_formed_last_bound());
                    SASSERT(well_formed_var(w));
                }
                // constraint is false, but not propagating
            }
        }
    }

    bool stellensatz::propagation_cycle(lpvar v, rational const &value, bool is_upper, unsigned level, lp::constraint_index ci) const {
        if (!in_bounds(v, value))
            return false;
        auto last_bound = is_upper ? m_upper[v] : m_lower[v];
        while (last_bound != UINT_MAX && m_bounds[last_bound].m_level == level) {
            auto other_ci = m_bounds[last_bound].m_constraint_justification;
            if (ci == other_ci)
                return true;
            last_bound = m_bounds[last_bound].m_last_bound;
        }
        return false;
    }
   
    //
    // Attempt to repair variables in some order
    // If hitting a variable that cannot be repaired, create a decision based on the value conflict.
    // Attempts to repair a variable can result in a new conflict obtained from vanishing polynomials
    // or conflicting bounds. The conflicts are assumed to contain variables of lower levels and
    // repair of those constraints are re-attempted.
    // If a variable is in a false constraint that cannot be repaired, pick a non-fixed
    // variable from the constraint and tighten its bound.
    // 
    bool stellensatz::decide() {
        rational value;
        lp::lconstraint_kind k;       
        lpvar w;

        unsigned num_fixed = 0;
        unsigned num_levels = m_level2var.size();
        unsigned num_rounds = 0;
        unsigned max_rounds = num_levels * 5;
        m_tabu.reset();
        for (unsigned level = 0; level < num_levels && c().reslim().inc() && num_rounds < max_rounds; ++level) {
            w = m_level2var[level];
            ++num_rounds;
            lp::constraint_index conflict = repair_variable(w);
            TRACE(arith, display_constraint(tout << "repair lvl:" << level << " v" << w << ": ", conflict) 
                << " in bounds " << in_bounds(w) 
                << " is tabu " << m_tabu.contains(conflict) << "\n");
            if (conflict == lp::null_ci)
                continue;
            SASSERT(constraint_is_false(conflict));
            if (constraint_is_conflict(conflict)) {
                set_conflict(conflict, nullptr);
                return true;
            }

            if (m_tabu.contains(conflict))  // already attempted to repair this constraint without success
                continue;

            m_tabu.insert(conflict);

            auto p = m_constraints[conflict].p;
            SASSERT(!p.free_vars().empty());
            if (!p.free_vars().contains(w)) {
                // backtrack decision to max variable in ci
                level = std::min(max_level(m_constraints[conflict]) - 1, level);
                continue;
            }

            if (is_fixed(w) && level > num_fixed) {
                // swap this variable level with another so it is solved before non-fixed variables
                IF_VERBOSE(3, verbose_stream() << "fixed v" << w << " cannot be repaired " << level << "\n";
                           display_constraint(verbose_stream(), conflict) << "\n");
                move_up(w);
                ++num_fixed;
                --level;
                continue;
            }          

            // variable wasn't repaired. 
            // Repair other variables, and then case split on variables that occur in non-repaired constraints.
            //
        }


        if (find_split(w, value, k)) {        
            SASSERT(k == lp::lconstraint_kind::LE || k == lp::lconstraint_kind::GE);
            bool is_upper = k == lp::lconstraint_kind::LE;
            SASSERT(!is_upper || !has_lo(w) || lo_val(w) <= value);
            SASSERT( is_upper || !has_hi(w) || hi_val(w) >= value);
            ++m_num_scopes;
            m_dm.push_scope();
            auto last_bound = is_upper ? m_upper[w] : m_lower[w];
            (is_upper ? m_upper[w] : m_lower[w]) = m_bounds.size();
            auto bdep = bound2dep(m_bounds.size());
            m_bounds.push_back(bound_info(w, k, value, m_num_scopes, last_bound, bdep));
            m_values[w] = value;
            TRACE(arith, tout << "decide v" << w << " " << k << " " << value << "\n");
            IF_VERBOSE(3, verbose_stream() << "v" << w << " " << k << " " << value << "\n");
            SASSERT(in_bounds(w));
            SASSERT(well_formed_var(w));
            SASSERT(well_formed_last_bound());
            ++c().lp_settings().stats().m_stellensatz.m_num_decisions;
            return true;
        }

        return false;
    }

    unsigned stellensatz::max_level(constraint const &c) const {
        unsigned level = 0;
        auto const &vars = c.p.free_vars();
        for (auto v : vars)
            level = std::max(level, m_var2level[v]);
        return level;
    }

    //
    // Compute intervals for polynomials p, q, in constraint px + q >= 0
    // Determine bounds on x implied by intervals on p, q.
    // If a tighter bound is computed for x, produce the bound propagation.
    // 
    bool stellensatz::constraint_is_propagating(lp::constraint_index ci, u_dependency*& d, lpvar& v, rational& value, lp::lconstraint_kind& k) {
        auto [p, ck, j] = m_constraints[ci];
        for (auto x : p.free_vars()) {
            auto f = factor(x, ci);
            if (f.degree > 1)
                continue;
            scoped_dep_interval ivp(m_di), ivq(m_di);
            interval(f.p, ivp);
            interval(-f.q, ivq); 
            TRACE(arith_verbose, tout << "variable v" << x << " in " << p << "\n";
                  m_di.display(tout << "interval: " << f.p << ": ", ivp) << "\n";
                  m_di.display(tout << "interval: " << -f.q << ": ", ivq) << "\n";
                  display_constraint(tout, ci) << "\n");
           
            // p > 0:
            // => x >= -q / p
            if (!ivq->m_lower_inf && !ivp->m_lower_inf && ivp->m_lower > 0) {
                // v >= -q / p
                auto quot = ivq->m_lower / ivp->m_lower;
                if (var_is_int(x))
                    quot = ceil(quot);
                bool is_strict = !var_is_int(x) && (ck == lp::lconstraint_kind::GT || ivq->m_lower_open || ivp->m_lower_open);
                if (!has_lo(x) || quot > lo_val(x) || (!lo_is_strict(x) && quot == lo_val(x) && is_strict)) {
                    TRACE(arith, tout << "new lower bound v" << x << " " << quot << "\n");
                    d = m_dm.mk_join(ivq->m_lower_dep, ivp->m_lower_dep);
                    k = is_strict ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE;
                    v = x;
                    value = quot;
                    return true;
                }
            }
            
            // p <= hi_p < 0
            // lo_q <= q <= hi_q < 0
            // => x <= lo_q / hi_p
            if (!ivp->m_upper_inf && ivp->m_upper < 0 && !ivq->m_upper_inf && !ivq->m_lower_inf && ivq->m_upper <= 0) {
                // v <= -q / p
                auto quot = ivq->m_lower / ivp->m_upper;
                if (var_is_int(x))
                    quot = floor(quot);
                bool is_strict =
                    !var_is_int(x) && (ck == lp::lconstraint_kind::GT || ivq->m_lower_open || ivp->m_upper_open);
                if (!has_hi(x) || quot < hi_val(x) || (!hi_is_strict(x) && quot == hi_val(x) && is_strict)) {
                    TRACE(arith, tout << "new upper bound v" << x << " " << quot << "\n");
                    d = m_dm.mk_join(ivq->m_upper_dep, m_dm.mk_join(ivq->m_lower_dep, ivp->m_upper_dep));
                    k = is_strict ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                    v = x;
                    value = quot;
                    return true;
                }
            }
            // lo_p <= p < 0
            // 0 <= lo_q <= -q 
            // => x <= lo_q / lo_p
            // 
            if (!ivp->m_upper_inf && ivp->m_upper < 0 && !ivp->m_lower_inf && 
                !ivq->m_lower_inf && ivq->m_lower >= 0) {
                auto quot = ivq->m_lower / ivp->m_lower;
                if (var_is_int(x))
                    quot = floor(quot);
                bool is_strict =
                    !var_is_int(x) && (ck == lp::lconstraint_kind::GT || ivq->m_lower_open || ivp->m_lower_open);
                if (!has_hi(x) || quot < hi_val(x) || (!hi_is_strict(x) && quot == hi_val(x) && is_strict)) {
                    TRACE(arith, tout << "new upper bound v" << x << " " << quot << "\n");
                    d = m_dm.mk_join(ivp->m_upper_dep, m_dm.mk_join(ivp->m_lower_dep, ivq->m_lower_dep));
                    k = is_strict ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                    v = x;
                    value = quot;
                    return true;
                }
            }
        }
        return false;
    }

    bool stellensatz::well_formed() const {        
        for (unsigned v = 0; v < num_vars(); ++v) 
            if (!well_formed_var(v))
                return false;    
        for (unsigned i = 0; i < m_bounds.size(); ++i)
            if (!well_formed_bound(i))
                return false;
        return true;
    }

    //
    // integer variables have only non-strict bounds
    // bounds are assigned at monotonically increasing levels
    // previous bounds are the same sign (lower or upper bounds)
    // previous bounds are weaker
    // previous bounds are for the same variable
    // 
    bool stellensatz::well_formed_bound(unsigned bound_index) const { 
        auto const &b = m_bounds[bound_index];
        if (var_is_int(b.m_var) && b.m_kind == lp::lconstraint_kind::LT)
            return false;
        if (var_is_int(b.m_var) && b.m_kind == lp::lconstraint_kind::GT)
            return false;
        auto last_bound = b.m_last_bound;
        if (last_bound == UINT_MAX)
            return true;
        auto const &last_b = m_bounds[last_bound];
        // this is possible because unit propagation is partial
        if (false && last_b.m_level > b.m_level) 
            return false;
        bool is_upper = b.m_kind == lp::lconstraint_kind::LE || b.m_kind == lp::lconstraint_kind::LT;
        bool is_upper2 = last_b.m_kind == lp::lconstraint_kind::LE || last_b.m_kind == lp::lconstraint_kind::LT;
        if (is_upper != is_upper2)
            return false;
        if (is_upper && b.m_value > last_b.m_value)
            return false;
        if (!is_upper && b.m_value < last_b.m_value)
            return false;
        if (b.m_var != last_b.m_var)
            return false;
        return true;
    }

    //
    // values of variables are within bounds unless the bounds are conflicting
    // m_lower[v], m_upper[v] are annotated by the same variable v.
    //
    bool stellensatz::well_formed_var(lpvar v) const {
        if (var_is_bound_conflict(v))
            return true;
        auto const &value = m_values[v];
        if (var_is_int(v) && !value.is_int())
            return false;
        
        if (has_lo(v) && value < lo_val(v))
            return false;
        if (has_lo(v) && lo_is_strict(v) && value == lo_val(v))
            return false;
        if (has_lo(v) && lo_kind(v) != lp::lconstraint_kind::GE && lo_kind(v) != lp::lconstraint_kind::GT)
            return false;
        if (has_lo(v) && m_bounds[m_lower[v]].m_var != v)
            return false;
        if (has_hi(v) && value > hi_val(v))
            return false;
        if (has_hi(v) && hi_is_strict(v) && value == hi_val(v))
            return false;
        if (has_hi(v) && hi_kind(v) != lp::lconstraint_kind::LE && hi_kind(v) != lp::lconstraint_kind::LT)
            return false;
        if (has_hi(v) && m_bounds[m_upper[v]].m_var != v)
            return false;
        return true;
    }

    std::pair<unsigned_vector, unsigned_vector> stellensatz::antecedents(u_dependency *d) const { 
        unsigned_vector bounds, cs, deps;
        m_dm.linearize(d, deps);
        for (auto dep : deps) {
            if (is_constraintdep(dep))
                cs.push_back(dep2constraint(dep));
            else
                bounds.push_back(dep2bound(dep));
        }
        return {bounds, cs};
    }


    void stellensatz::updt_params(params_ref const& p) {
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


    void stellensatz::solver::init() {
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
            auto const &[p, k, j] = s.m_constraints[ci];
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

    stellensatz::term_offset stellensatz::solver::to_term_offset(dd::pdd const &p) {
        term_offset to;
        for (auto const &[coeff, vars] : p) {
            if (vars.empty())
                to.second += coeff;
            else
                to.first.add_monomial(coeff, m_monomial_factory.mk_monomial(*lra_solver, vars));
        }
        return to;
    }

    lbool stellensatz::solver::solve(svector<lp::constraint_index>& core) {
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

    lbool stellensatz::solver::solve_lra() {
        auto status = lra_solver->find_feasible_solution();;
        if (lra_solver->is_feasible())
            return l_true;
        if (status == lp::lp_status::INFEASIBLE) {
            lra_solver->get_infeasibility_explanation(m_ex);
            return l_false;
        }
        return l_undef;
    }

    lbool stellensatz::solver::solve_lia() {
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
    void stellensatz::solver::update_values(vector<rational>& values) {
        std::unordered_map<lpvar, rational> _values;
        lra_solver->get_model(_values);
        unsigned sz = values.size();
        for (unsigned i = 0; i < sz; ++i) 
            values[i] = _values[i];
        TRACE(arith, for (unsigned i = 0; i < sz; ++i) tout << "j" << i << " := " << values[i] << "\n";);
    }

    lp::constraint_index stellensatz::repair_variable(lp::lpvar v) {
        auto [inf, sup, conflict, lo, hi] = find_bounds(v);

        CTRACE(arith, inf != lp::null_ci || sup != lp::null_ci || conflict != lp::null_ci, 
                tout << "bounds for v" << v << " @ " << m_var2level[v] << "\n";
                display_constraint(tout << "lo: ", inf) << "\n"; 
                display_constraint(tout << "hi: ", sup) << "\n";
                display_constraint(tout << "conflict: ", conflict) << "\n");

        if (conflict != lp::null_ci) 
            return conflict;        

        if (inf == lp::null_ci && sup == lp::null_ci)
            return inf;

        if (!constraint_is_false(inf) && !constraint_is_false(sup))
            return lp::null_ci;

        TRACE(arith, tout << "v" << v << " @ " << m_var2level[v] << "\n");

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
            if (in_bounds(v, hi)) {
                m_values[v] = hi;            
                SASSERT(in_bounds(v));
                return lp::null_ci;
            }
            else {
                auto const& b = m_bounds[m_lower[v]];
                auto res = resolve_variable(v, b.m_constraint_justification, sup);
                TRACE(arith, display_constraint(tout << "resolved against implied lower bound ", res) << "\n");
                if (constraint_is_false(res))                     
                    return res;                
            }
        }
        else if (sup == lp::null_ci) {
            SASSERT(inf != lp::null_ci);
            if (strict_lo) {
                if (has_hi(v))
                    lo = (lo + hi_val(v)) / 2;
                else
                    lo = lo + 1;
            }
            CTRACE(arith, !in_bounds(v, lo), display_var_range(tout << "repair v" << v << " to lo " << lo << "\n", v) << "\n");
            if (in_bounds(v, lo)) {
                m_values[v] = lo;
                SASSERT(in_bounds(v));
                return lp::null_ci;
            }
            else {
                auto const &b = m_bounds[m_upper[v]];
                auto res = resolve_variable(v, b.m_constraint_justification, inf);
                TRACE(arith, display_constraint(tout << "resolved against implied upper bound ", res) << "\n";
                display_bound(tout, m_upper[v]) << "\n");
                if (constraint_is_false(res))                     
                    return res;                
            }
        }
        else if (((!strict && lo <= hi) || lo < hi) && (!var_is_int(v) || ceil(lo) <= hi)) {
            // repair v by setting it between lo and hi assuming it is integral when v is integer
            auto mid = var_is_int(v) ? ceil(lo) : ((lo + hi) / 2);
            if (in_bounds(v, mid)) {
                TRACE(arith, tout << "repair v" << v << " := " << mid << " / " << m_values[v] << " lo: " << lo << " hi: " << hi << "\n");
                m_values[v] = mid;
                SASSERT(in_bounds(v));
                //SASSERT(!constraint_is_false(sup)); // if it uses m_lower, m_upper bounds that are propagated to compute lo/hi the repair may not be sufficient to satisfy the constraints.
                //SASSERT(!constraint_is_false(inf));
                return lp::null_ci;
            }

            auto res = resolve_variable(v, inf, sup);
            if (constraint_is_false(res)) 
                return res;            
            TRACE(arith_verbose, display_var_range(tout << "mid point is not in bounds v" << v << " mid: " << mid << " " << lo
                                                << " " << hi << "\n",
                                           v)
                             << "\n");
            return lp::null_ci;
        }
        else {
            TRACE(arith, tout << "cannot repair v" << v << " between " << lo << " and " << hi << " " << (lo > hi)
                              << " is int " << var_is_int(v) << "\n";
                  display_constraint(tout, inf) << "\n"; display_constraint(tout, sup) << "\n";);
            auto res = resolve_variable(v, inf, sup);
            TRACE(arith, display_constraint(tout << "resolve ", res) << " " << constraint_is_false(res) << "\n");
            if (constraint_is_false(res)) 
                return res;            
        }

        if (!constraint_is_false(inf))
            return sup;
        if (!constraint_is_false(sup))
            return inf;
        return c().random(2) == 0 ? sup : inf;
    }        

    bool stellensatz::find_split(lpvar &v, rational &r, lp::lconstraint_kind &k) { 
        uint_set tried;        
        bool found = false;
        unsigned n = 0;
        for (auto ci : m_constraints) {
            if (!constraint_is_false(ci))
                continue;
            auto const &vars = ci.p.free_vars();
            for (auto w : vars) {
                if (tried.contains(w))
                    continue;
                tried.insert(w);
                if (is_fixed(w))
                    continue;
                if (m_split_count[w] > m_config.max_splits_per_var)
                    continue;
                if (c().random(++n) != 0)
                    continue;
                r = m_values[w];
                CTRACE(arith, !in_bounds(w), tout << "value not in bounds v" << w << " := " << r << "\n";
                       display(tout););
                SASSERT(in_bounds(w));
                if (has_lo(w) && !lo_is_strict(w) && r == lo_val(w))
                    k = lp::lconstraint_kind::LE;
                else if (has_hi(w) && !hi_is_strict(w) && r == hi_val(w))
                    k = lp::lconstraint_kind::GE;
                else if (has_lo(w) && has_hi(w) && (lo_is_strict(w) || hi_is_strict(w))) {
                    r = (lo_val(w) + hi_val(w)) / 2;
                    k = lp::lconstraint_kind::GE;
                }
                else if (!has_lo(w))
                    k = lp::lconstraint_kind::GE;
                else if (!has_hi(w))
                    k = lp::lconstraint_kind::LE;
                else
                    k = c().random(2) == 0 ? lp::lconstraint_kind::GE : lp::lconstraint_kind::LE;
                v = w;
                found = true;
            }
        }
        CTRACE(arith, found, tout << "split v" << v << " " << k << " " << r << "\n");
        if (found)
            ++m_split_count[v];
        return found;
    }

    void stellensatz::set_in_bounds(lpvar v) {
        if (in_bounds(v))
            return;
        if (!has_lo(v))
            m_values[v] = hi_is_strict(v) ? hi_val(v) - 1 : hi_val(v);
        else if (!has_hi(v))
            m_values[v] = lo_is_strict(v) ? lo_val(v) + 1 : lo_val(v);
        else if (lo_is_strict(v) || hi_is_strict(v))
            m_values[v] = (lo_val(v) + hi_val(v)) / 2;
        else
            m_values[v] = lo_val(v);
        SASSERT(in_bounds(v));
    }

    bool stellensatz::in_bounds(lpvar v, rational const& value) const {
        if (has_lo(v)) {
            if (value < lo_val(v))
                return false;
            if (lo_is_strict(v) && value <= lo_val(v))
                return false;
        }
        if (has_hi(v)) {
            if (value > hi_val(v))
                return false;
            if (hi_is_strict(v) && value >= hi_val(v))
                return false;
        }
        return true;
    }

    //
    // Enumerate polynomial inequalities p*v + q >= 0
    // where variables in p, q are at levels below v.
    // If M(p) = 0 and M(q) < 0, return q >= 0 and assume p = 0
    // Otherwise, return greatest lower and least upper bounds for v based on polynomial inequalities.
    // 
    stellensatz::repair_var_info stellensatz::find_bounds(lpvar v) {
        repair_var_info result;
        auto &[inf, sup, van, lo, hi] = result;        
        for (auto ci : m_occurs[v]) {
            //
            // consider only constraints where v is maximal
            // and where the degree of constraints is bounded
            // for lower and upper bounds only constraints where v
            // occurs pseudo-linearly are considered
            //
            auto const &p = m_constraints[ci].p;
            auto const &vars = p.free_vars();
            if (any_of(vars, [&](unsigned j) { return p.degree(j) == 1 && m_var2level[j] > m_var2level[v]; }))
                continue;
            TRACE(arith_verbose, display_constraint(tout, ci) << "\n"; for (auto j : vars) tout
                                                               << "j" << j << " deg: " << p.degree(j)
                                                               << " lvl: " << m_var2level[j]
                                                  << "\n";);
        
            if (p.degree() > m_config.max_degree)
                continue;
            auto f = factor(v, ci);
            auto q_ge_0 = vanishing(v, f, ci);
            if (q_ge_0 != lp::null_ci) {
                if (!constraint_is_true(q_ge_0)) {
                    van = q_ge_0;
                    return result;
                }
                TRACE(arith_verbose, display_constraint(tout << "vanished j" << v << " in ", ci) << "\n";
                      display_constraint(tout << " to ", q_ge_0) << "\n";);
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
        if (has_lo(v) && m_bounds[m_lower[v]].m_constraint_justification != lp::null_ci) {
            if (inf == lp::null_ci || lo < lo_val(v)) {
                lo = lo_val(v);
                inf = m_bounds[m_lower[v]].m_constraint_justification;
            }
        }
        if (has_hi(v) && m_bounds[m_upper[v]].m_constraint_justification != lp::null_ci) {
            if (sup == lp::null_ci || hi > hi_val(v)) {
                hi = hi_val(v);
                sup = m_bounds[m_upper[v]].m_constraint_justification;
            }
        }
        return result;
    }

    void stellensatz::move_up(lpvar v) {
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
    
    std::ostream &stellensatz::display_bound(std::ostream &out, unsigned i) const {
        unsigned lvl = 0;
        return display_bound(out, i, lvl);
    }

    std::ostream &stellensatz::display_bound(std::ostream &out, unsigned i, unsigned &level) const {
        auto const &[v, k, val, level1, last_bound, is_decision, dep, ci] = m_bounds[i];
        out << i;
        if (level1 != level) {
            level = level1;
            out << "@ " << level;
        }
        auto [bounds, cdeps] = antecedents(dep);
        auto deps = antecedents(dep);
        out << ": v" << v << " " << k << " " << val << " " << ((last_bound == UINT_MAX) ? -1 : (int)last_bound)
            << (is_decision ? " d " : " ");
        if (!bounds.empty())
            out << "bounds: " << bounds;
        if (!cdeps.empty())
            out << "ci: " << cdeps;
        if (ci != lp::null_ci)
            out << " (" << ci << ")";
        out << "\n";
        return out;
    }

    std::ostream &stellensatz::display(std::ostream &out) const {
        unsigned level = UINT_MAX;
        for (unsigned i = 0; i < m_bounds.size(); ++i)
            display_bound(out, i, level);

        for (unsigned v = 0; v < num_vars(); ++v) 
            display_var_range(out, v) << "\n";
        
        for (unsigned ci = 0; ci < m_constraints.size(); ++ci) {
            display_constraint(out, ci) << "\n";
            display(out << "\t<- ", m_constraints[ci].j) << "\n";
        }
        return out;
    }

    std::ostream &stellensatz::display_var_range(std::ostream &out, lpvar v) const {
        out << "v" << v << " " << m_values[v] << " ";
        if (has_lo(v)) {
            if (lo_is_strict(v))
                out << "(";
            else
                out << "[";
            out << lo_val(v);
        }
        else
            out << "(-oo";
        out << ", ";
        if (has_hi(v)) {
            out << hi_val(v);
            if (hi_is_strict(v))
                out << ")";
            else
                out << "]";
        }
        else
            out << "+oo)";
        if (has_lo(v))
            out << " " << m_lower[v];
        if (has_hi(v))
            out << " " << m_upper[v];
        return out;
    }

    std::ostream &stellensatz::display_product(std::ostream &out, svector<lpvar> const &vars) const {
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

    std::ostream &stellensatz::display(std::ostream &out, term_offset const &t) const {
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

    std::ostream &stellensatz::display_var(std::ostream &out, lpvar j) const {
        if (c().is_monic_var(j))
            return display_product(out, c().emon(j).vars());
        else
            return out << "j" << j;
    }

    std::ostream &stellensatz::display_constraint(std::ostream &out, lp::constraint_index ci) const {
        if (ci == lp::null_ci)
            return out << "(null) ";
        bool is_true = constraint_is_true(ci);
        auto const &[p, k, j] = m_constraints[ci];
        return display_constraint(out << "(" << ci << ") ", m_constraints[ci])
               << (is_true ? " [true] " : " [false] ") << "(" << value(p) << " " << k << " 0)";
    }

    std::ostream &stellensatz::display_constraint(std::ostream &out, constraint const &c) const {
        auto const &[p, k, j] = c;
        p.display(out);
        return out << " " << k << " 0";
    }

    std::ostream &stellensatz::display(std::ostream &out, justification const &j) const {
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
        else
            UNREACHABLE();
        return out;
    }

    std::ostream &stellensatz::display_lemma(std::ostream &out, lp::explanation const &ex) {
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
            display_constraint(out, ci) << " ";
            auto const &j = m_constraints[ci].j;

            display(out, j) << "\n";
            if (std::holds_alternative<multiplication_justification>(j)) {
                auto m = std::get<multiplication_justification>(j);
                todo.push_back(m.left);
                todo.push_back(m.right);
            }
            if (std::holds_alternative<eq_justification>(j)) {
                auto m = std::get<eq_justification>(j);
                todo.push_back(m.left);
                todo.push_back(m.right);
            }
            if (std::holds_alternative<propagation_justification>(j)) {
                auto m = std::get<propagation_justification>(j);
                todo.append(m.cs);
            }
            else if (std::holds_alternative<substitute_justification>(j)) {
                auto m = std::get<substitute_justification>(j);
                todo.push_back(m.ci);
                todo.push_back(m.ci_eq);
            }
            else if (std::holds_alternative<division_justification>(j)) {
                auto m = std::get<division_justification>(j);
                todo.push_back(m.ci);
                todo.push_back(m.divisor);
            }
            else if (std::holds_alternative<addition_justification>(j)) {
                auto m = std::get<addition_justification>(j);
                todo.push_back(m.left);
                todo.push_back(m.right);
            }
            else if (std::holds_alternative<multiplication_poly_justification>(j)) {
                auto m = std::get<multiplication_poly_justification>(j);
                todo.push_back(m.ci);
            }
            else if (std::holds_alternative<external_justification>(j)) {
                // do nothing
            }
            else if (std::holds_alternative<assumption_justification>(j)) {
                // do nothing
            }
            else if (std::holds_alternative<gcd_justification>(j)) {
                auto m = std::get<gcd_justification>(j);
                todo.push_back(m.ci);
            }
            else
                NOT_IMPLEMENTED_YET();
        }
        return out;
    }
}
