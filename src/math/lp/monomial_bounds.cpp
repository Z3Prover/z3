/*++
  Copyright (c) 2020 Microsoft Corporation

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  --*/

#include "math/lp/monomial_bounds.h"
#include "math/lp/nla_core.h"
#include "math/lp/nla_intervals.h"
#include "math/lp/numeric_pair.h"

namespace nla {

    monomial_bounds::monomial_bounds(core *c) : common(c), dep(c->m_intervals.get_dep_intervals()) {}

    void monomial_bounds::generate_lemmas() {
        for (auto v : c().m_to_refine) {
            generate_lemma(c().emon(v));
            if (add_lemma())
                break;
        }
    }

    bool monomial_bounds::is_too_big(mpq const &q) const {
        return rational(q).bitsize() > 256;
    }

    /**
     * Accumulate product of variables in monomial starting at position 'start'
     */
    void monomial_bounds::compute_product(unsigned start, monic const &m, scoped_dep_interval &product) {
        scoped_dep_interval vi(dep);
        unsigned power = 1;
        for (unsigned i = start; i < m.size();) {
            lpvar v = m.vars()[i];
            var2interval(v, vi);
            ++i;
            for (power = 1; i < m.size() && m.vars()[i] == v; ++i, ++power)
                ;
            dep.power<dep_intervals::with_deps>(vi, power, vi);
            dep.mul<dep_intervals::with_deps>(product, vi, product);
        }
    }



    bool monomial_bounds::should_propagate_lower(dep_interval const &range, lpvar v, unsigned p) {
        if (dep.lower_is_inf(range))
            return false;
        auto bound = c().val(v);
        auto const &lower = dep.lower(range);
        if (p > 1)
            bound = power(bound, p);
        return bound < lower;
    }

    bool monomial_bounds::should_propagate_upper(dep_interval const &range, lpvar v, unsigned p) {
        if (dep.upper_is_inf(range))
            return false;
        auto bound = c().val(v);
        auto const &upper = dep.upper(range);
        if (p > 1)
            bound = power(bound, p);
        return bound > upper;
    }

    void monomial_bounds::var2interval(lpvar v, scoped_dep_interval &i) {
        u_dependency *d = nullptr;
        rational bound;
        bool is_strict;
        if (c().has_lower_bound(v, d, bound, is_strict)) {
            dep.set_lower_is_open(i, is_strict);
            dep.set_lower(i, bound);
            dep.set_lower_dep(i, d);
            dep.set_lower_is_inf(i, false);
        }
        else {
            dep.set_lower_is_inf(i, true);
        }
        if (c().has_upper_bound(v, d, bound, is_strict)) {
            dep.set_upper_is_open(i, is_strict);
            dep.set_upper(i, bound);
            dep.set_upper_dep(i, d);
            dep.set_upper_is_inf(i, false);
        }
        else {
            dep.set_upper_is_inf(i, true);
        }
    }

    /**
     * Interval-based lemma generation for monomial 'm'.
     * Runs the shared-factor (sandwich) and binomial-sign propagators.
     * These emit lemmas; they do not tighten LP bounds.
     */
    bool monomial_bounds::generate_lemma(monic const &m) {
        unsigned num_free, power;
        lpvar free_var;
        analyze_monomial(m, num_free, free_var, power);
        bool do_propagate_down = !is_free(m.var()) && num_free <= 1;
        if (do_propagate_down && c().params().arith_nl_monomial_sandwich() && propagate_shared_factor(m))
            return true;
        if (c().params().arith_nl_monomial_binomial_sign() && propagate_binomial_sign(m))
            return true;
        return false;
    }

    /**
     * LP-bound tightening for monomial 'm'.
     * For each variable v in m, divide the interval of m.var() by the product of
     * the other variables and strengthen v's LP bounds (down-propagation).
     * Finally strengthen the LP bounds of m.var() from the product interval.
     * Unlike generate_lemma(), this emits no lemmas -- it only tightens LP bounds.
     */
    bool monomial_bounds::tighten_lp(monic const &m) {
        unsigned num_free, power;
        lpvar free_var;
        analyze_monomial(m, num_free, free_var, power);
        bool do_propagate_up = num_free == 0;
        bool do_propagate_down = !is_free(m.var()) && num_free <= 1;
        if (!do_propagate_up && !do_propagate_down)
            return false;

        scoped_dep_interval product(dep);
        scoped_dep_interval vi(dep), mi(dep);
        scoped_dep_interval other_product(dep);
        var2interval(m.var(), mi);
        dep.set_value(product, rational::one());
        bool tightened = false;
        for (unsigned i = 0; i < m.size();) {
            lpvar v = m.vars()[i];
            ++i;
            for (power = 1; i < m.size() && v == m.vars()[i]; ++i, ++power)
                ;
            var2interval(v, vi);
            dep.power<dep_intervals::with_deps>(vi, power, vi);

            if (do_propagate_down && (num_free == 0 || free_var == v)) {
                dep.set<dep_intervals::with_deps>(other_product, product);
                compute_product(i, m, other_product);
                if (tighten_lp_bound(mi, v, power, other_product))
                    tightened = true;
            }
            dep.mul<dep_intervals::with_deps>(product, vi, product);
        }
        if (!do_propagate_up)
            return tightened;
        return tighten_lp_bound(product, m.var(), 1) || tightened;
    }

    bool monomial_bounds::tighten_lp_bound(dep_interval &mi, lpvar v, unsigned power,
                                           dep_interval &product) {
        if (!dep.separated_from_zero(product))
            return false;
        scoped_dep_interval range(dep);
        dep.div<dep_intervals::with_deps>(mi, product, range);
        return tighten_lp_bound(range, v, power);
    }

    bool monomial_bounds::is_free(lpvar v) const {
        return !c().has_lower_bound(v) && !c().has_upper_bound(v);
    }    

    bool monomial_bounds::is_zero(lpvar v) const {
        return 
            c().has_lower_bound(v) && 
            c().has_upper_bound(v) &&
            c().get_lower_bound(v).is_zero() && 
            c().get_upper_bound(v).is_zero();
    }    

    /**
     * Count the number of unbound (free) variables.
     * Variables with no lower and no upper bound multiplied 
     * to an odd degree have unbound ranges when it comes to 
     * bounds propagation.
     */
    void monomial_bounds::analyze_monomial(monic const& m, unsigned& num_free, lpvar& fv, unsigned& fv_power) const {
        unsigned power = 1;
        num_free = 0;
        fv = null_lpvar;
        fv_power = 0;
        for (unsigned i = 0; i < m.vars().size(); ) {
            lpvar v = m.vars()[i];
            ++i;
            for (power = 1; i < m.vars().size() && m.vars()[i] == v; ++i, ++power);
            if (is_zero(v)) {
                num_free = 0;
                return;
            }
            if (power % 2 == 1 && is_free(v)) {
                ++num_free;
                fv_power = power;
                fv = v;
            }
        }
    }

    bool monomial_bounds::propagate_changed_bounds() {        
        bool propagated = false;
        for (lpvar v : c().m_monics_with_changed_bounds) {
            if (!c().is_monic_var(v))
                continue;
            monic& m = c().emon(v);
            if (propagate_linear_bound(m))
                propagated = true;
            if (tighten_lp(m))
                propagated = true;
            if (c().lra.get_status() == lp::lp_status::INFEASIBLE)
                break;
        }   
        return propagated;
    }

    bool monomial_bounds::propagate_linear_bounds() {
        bool propagated = false;
        for (auto& mm : c().emons()) {
            //if (!c().is_monic_var(v))
            //    continue;
            monic &m = c().emon(mm.var());
            if (propagate_linear_bound(m))
                propagated = true;
            if (c().lra.get_status() == lp::lp_status::INFEASIBLE)
                break;
        }
        return propagated;
    }

    bool monomial_bounds::add_lemma() {
        if (c().lra.get_status() != lp::lp_status::INFEASIBLE)
            return false;
        lp::explanation exp;
        c().lra.get_infeasibility_explanation(exp);
        lemma_builder lemma(c(), "propagate fixed - infeasible lra");
        lemma &= exp;
        return true;
    }

    bool monomial_bounds::propagate_linear_bound(monic & m) {
        if (m.is_propagated())
            return false;
        lpvar w, fixed_to_zero;

        if (!is_linear(m, w, fixed_to_zero)) 
            return false;

        c().emons().set_propagated(m);

        bool propagated = false;
        if (fixed_to_zero != null_lpvar) {
            propagated = propagate_fixed_to_zero(m, fixed_to_zero);
        } 
        else {
            rational k = fixed_var_product(m, w);
            if (w == null_lpvar)
                propagated = propagate_fixed(m, k);
            else
                propagated = propagate_nonfixed(m, k, w);
        }
        if (propagated)
            ++c().lra.settings().stats().m_nla_propagate_eq;
        return propagated;
    }

    lp::explanation monomial_bounds::get_explanation(u_dependency* dep) {
        lp::explanation exp;
        svector<lp::constraint_index> cs;
        c().lra.dep_manager().linearize(dep, cs);
        for (auto d : cs)
            exp.add_pair(d, mpq(1));
        return exp;
    }
    
    bool monomial_bounds::propagate_fixed_to_zero(monic const& m, lpvar fixed_to_zero) {
        if (c().var_is_fixed_to_zero(m.var()))
            return false;
        auto* dep = c().lra.get_bound_constraint_witnesses_for_column(fixed_to_zero);
        TRACE(nla_solver, tout << "propagate fixed " << m << " =  0, fixed_to_zero = " << fixed_to_zero << "\n";);
        c().lra.update_column_type_and_bound(m.var(), lp::lconstraint_kind::EQ, rational(0), dep);
        
        // propagate fixed equality
        c().add_fixed_equality(m.var(), rational(0), get_explanation(dep));
        return true;
    }

    bool monomial_bounds::propagate_fixed(monic const& m, rational const& k) {
        if (c().var_is_fixed(m.var()) && c().get_lower_bound(m.var()) == k)
            return false;
        auto* dep = explain_fixed(m, k);
        TRACE(nla_solver, tout << "propagate fixed " << m << " = " << k << "\n";);
        c().lra.update_column_type_and_bound(m.var(), lp::lconstraint_kind::EQ, k, dep);
        
        // propagate fixed equality
        c().add_fixed_equality(m.var(), k, get_explanation(dep));
        return true;
    }

    bool monomial_bounds::propagate_nonfixed(monic const& m, rational const& k, lpvar w) {
        if (c().val(m.var()) == k * c().val(w)) {
            return false;
        }
        vector<std::pair<lp::mpq, unsigned>> coeffs;        
        coeffs.push_back({-k, w});
        coeffs.push_back({rational::one(), m.var()});
        lp::lpvar j = c().lra.add_term(coeffs, UINT_MAX);
        auto* dep = explain_fixed(m, k);
        TRACE(nla_solver, tout << "propagate nonfixed " << m << " = " << k << " " << w << "\n";);
        c().lra.update_column_type_and_bound(j, lp::lconstraint_kind::EQ, mpq(0), dep);

        if (k == 1) {
            c().add_equality(m.var(), w, get_explanation(dep));
        }
        return true;
    }

    u_dependency* monomial_bounds::explain_fixed(monic const& m, rational const& k) {
        u_dependency* dep = nullptr;
        auto update_dep = [&](unsigned j) {
            dep = c().lra.dep_manager().mk_join(dep, c().lra.get_column_lower_bound_witness(j));
            dep = c().lra.dep_manager().mk_join(dep, c().lra.get_column_upper_bound_witness(j));
            return dep;
        };

        if (k == 0) {
            for (auto j : m.vars()) 
                if (c().var_is_fixed_to_zero(j)) 
                    return update_dep(j);
        }
        else {
            for (auto j : m.vars()) 
                if (c().var_is_fixed(j))
                    update_dep(j);
        }
        return dep;
    }

    
    bool monomial_bounds::is_linear(monic const& m, lpvar& w, lpvar & fixed_to_zero) {
        w = fixed_to_zero = null_lpvar;
        for (lpvar v : m) {
            if (!c().var_is_fixed(v)) {
                if (w != null_lpvar)
                    return false;
                w = v;
            }
            else if (c().get_lower_bound(v).is_zero()) {
                fixed_to_zero = v;
                return true;
            }
        }
        return true;
    }
    
    
    rational monomial_bounds::fixed_var_product(monic const& m, lpvar w) {
        rational r(1);
        for (lpvar v : m) {
            //  we have to use the column bounds here, because the column value may be outside the bounds
            if (v != w ){
                SASSERT(c().var_is_fixed(v));
                r *= c().lra.get_lower_bound(v).x;
            }
        }
        return r;
    }
    
    /**
     * Dual-row shared-factor sandwich. For a binary monomial m = u*v, find LP
     * term columns whose term has shape  a_m * m + a_v * v  (exactly two
     * variables, both factors of m). The term column's bound is a sound
     * interval for (a_m * m + a_v * v). Substituting m = u*v yields
     * v * (a_m * u + a_v); dividing by the interval on v (sign-determined)
     * gives an interval on (a_m * u + a_v), and an affine shift gives an
     * interval on u. The derived interval is fed to the existing
     * propagate_value path so the lemma channel and integer rounding are
     * shared with the rest of the propagation pipeline.
     */
    bool monomial_bounds::propagate_shared_factor(monic const& m) {
        if (m.size() != 2)
            return false;
        lpvar f0 = m.vars()[0], f1 = m.vars()[1];
        if (f0 == f1)
            return false;

        unsigned const fanout_limit = c().params().arith_nl_monomial_sandwich_max_fanout();

        auto try_pair = [&](lpvar u, lpvar v) -> bool {
            // Skip if u participates in too many monomials: tightening such a
            // factor cascades through ord-binom / monotonicity on every monic
            // that contains it.
            if (fanout_limit > 0) {
                unsigned fanout = 0;
                for (auto const& m1 : c().emons().get_use_list(u)) {
                    (void)m1;
                    if (++fanout > fanout_limit)
                        return false;
                }
            }
            scoped_dep_interval vi(dep);
            var2interval(v, vi);
            if (!dep.separated_from_zero(vi))
                return false;

            auto& lra = c().lra;
            unsigned const ROW_CAP = 16;
            unsigned scanned = 0;

            for (auto const& cell : lra.A_r().m_columns[m.var()]) {
                if (++scanned > ROW_CAP)
                    break;
                unsigned basic = lra.get_base_column_in_row(cell.var());
                if (basic == m.var() || basic == v || basic == u)
                    continue;
                if (!lra.column_has_term(basic))
                    continue;
                auto const& term = lra.get_term(basic);
                if (term.size() != 2 ||
                    !term.contains(m.var()) || !term.contains(v))
                    continue;

                rational const& a_m = term.get_coeff(m.var());
                rational const& a_v = term.get_coeff(v);
                if (a_m.is_zero())
                    continue;

                // Term value = a_m*m + a_v*v; bound on basic bounds the term.
                // Substituting m = u*v: term = v * (a_m*u + a_v).
                scoped_dep_interval bi(dep);
                var2interval(basic, bi);

                scoped_dep_interval inner(dep);
                dep.div<dep_intervals::with_deps>(bi, vi, inner);

                scoped_dep_interval shift(dep);
                dep.set_value(shift, -a_v);
                scoped_dep_interval scaled(dep);
                dep.add<dep_intervals::with_deps>(inner, shift, scaled);

                scoped_dep_interval u_int(dep);
                dep.mul<dep_intervals::with_deps>(rational::one() / a_m, scaled, u_int);

                TRACE(nla_solver, tout << "sandwich shared-factor basic=" << basic
                      << " m=" << m.var() << " v=" << v << " u=" << u
                      << " a_m=" << a_m << " a_v=" << a_v << "\n";);

                if (tighten_lp_bound(u_int, u, 1))
                    return true;  // one lemma per call to keep the channel quiet
            }
            return false;
        };

        return try_pair(f1, f0) || try_pair(f0, f1);
    }

    /**
     * Sign-pinned binomial bound. For a binary monomial m = u*v in m_to_refine,
     * use the current LP value mv = val(m.var()) as a one-sided anchor on the
     * monomial value variable, and derive a deterministic interval for u via
     * sign-aware division by v.
     *
     * Direction is chosen by the disagreement: if val(m.var()) > val(u)*val(v)
     * the LP placed the monomial above the factor product, so we condition on
     * "m.var() >= mv"; otherwise on "m.var() <= mv". The resulting clause is
     * structurally analogous to a propagate_value lemma plus one extra
     * snapshot literal on m.var(): under the asserted bounds on v, the clause
     * reduces to a 2-disjunct (snapshot literal | factor bound).
     *
     * Targets the case ord-binom currently handles: factors have determined
     * signs, m.var() may have no LP bound at all. The clause is sound modulo
     * the monomial definition (the same condition propagate_down,
     * propagate_shared_factor and ord-binom rely on).
     */
    bool monomial_bounds::propagate_binomial_sign(monic const& m) {
        if (m.size() != 2)
            return false;
        lpvar f0 = m.vars()[0], f1 = m.vars()[1];
        if (f0 == f1)
            return false;

        rational const mv = c().val(m.var());
        rational const fp = c().val(f0) * c().val(f1);
        if (mv == fp)
            return false;
        bool const below = mv > fp;            // LP placed m.var() too high
        llc const anchor_cmp = below ? llc::LT : llc::GT;

        auto try_anchor = [&](lpvar u, lpvar v) -> bool {
            // Throttle once per (m.var(), u, v, direction) tuple. Without it
            // each new val(m.var()) snapshot would re-emit and the search
            // would cascade across model changes the same way ord-binom does.
            if (c().throttle().insert_new(
                    nla_throttle::MONOMIAL_BINOMIAL_SIGN,
                    m.var(), u, v, below))
                return false;

            scoped_dep_interval vi(dep);
            var2interval(v, vi);
            if (!dep.separated_from_zero(vi))
                return false;

            // Synthesize a one-sided interval for m.var() at mv. No deps;
            // the snapshot literal goes into the lemma body directly.
            scoped_dep_interval mi_anchor(dep);
            if (below) {
                dep.set_lower(mi_anchor, mv);
                dep.set_lower_is_inf(mi_anchor, false);
                dep.set_lower_is_open(mi_anchor, false);
                dep.set_upper_is_inf(mi_anchor, true);
            } else {
                dep.set_upper(mi_anchor, mv);
                dep.set_upper_is_inf(mi_anchor, false);
                dep.set_upper_is_open(mi_anchor, false);
                dep.set_lower_is_inf(mi_anchor, true);
            }

            scoped_dep_interval u_int(dep);
            dep.div<dep_intervals::with_deps>(mi_anchor, vi, u_int);

            bool emitted = false;
            if (should_propagate_lower(u_int, u, 1)) {
                auto const& lower = dep.lower(u_int);
                if (!is_too_big(lower)) {
                    auto cmp = dep.lower_is_open(u_int) ? llc::GT : llc::GE;
                    lp::explanation ex;
                    dep.get_lower_dep(u_int, ex);
                    lemma_builder lemma(c(), "binomial sign anchor");
                    lemma &= ex;
                    lemma |= ineq(m.var(), anchor_cmp, mv);
                    lemma |= ineq(u, cmp, lower);
                    emitted = true;
                }
            }
            if (should_propagate_upper(u_int, u, 1)) {
                auto const& upper = dep.upper(u_int);
                if (!is_too_big(upper)) {
                    auto cmp = dep.upper_is_open(u_int) ? llc::LT : llc::LE;
                    lp::explanation ex;
                    dep.get_upper_dep(u_int, ex);
                    lemma_builder lemma(c(), "binomial sign anchor");
                    lemma &= ex;
                    lemma |= ineq(m.var(), anchor_cmp, mv);
                    lemma |= ineq(u, cmp, upper);
                    emitted = true;
                }
            }
            return emitted;
        };

        return try_anchor(f1, f0) || try_anchor(f0, f1);
    }

    /**
     * range is an interval that v^p is guaranteed to lie in.
     * Strengthen the *upper* bound of v from range, analogously to the upper
     * branch of propagate_value(range, v, p), but only when a single bound on v
     * follows (no lemmas). We use the existing bounds of v -- not its value --
     * to resolve the sign for even powers.
     *
     * An upper bound on v is implied by:
     *   range.upper = U:
     *     p odd            -> v <= root(p, U)
     *     p even, U >= 0   -> v <= root(p, U)          (|v| <= root(p, U))
     *   range.lower = L, p even, v known <= 0:
     *     v <= -root(p, L)                             (resolves the disjunction)
     * Only exact rational roots are used, so bounds that are not obtained from
     * propagation are out of scope.
     */
    bool monomial_bounds::tighten_lp_upper_bound(dep_interval const &range, lpvar v, unsigned p) {
        SASSERT(p > 0);
        auto improves_upper = [&](rational const& cand) {
            return !c().has_upper_bound(v) || cand < c().get_upper_bound(v);
        };
        bool tightened = false;
        rational r;
        // From range.upper: v <= root(p, U).
        if (!dep.upper_is_inf(range)) {
            rational U(dep.upper(range));
            if (U.root(p, r) && improves_upper(r)) {
                auto cmp = dep.upper_is_open(range) ? llc::LT : llc::LE;
                propagate_lp_bound(v, cmp, r, dep.get_upper_dep(range));
                tightened = true;
            }
        }
        // Even power, v known non-positive: range.lower gives v <= -root(p, L).
        if ((p & 1) == 0 && !dep.lower_is_inf(range) &&
            c().has_upper_bound(v) && !c().get_upper_bound(v).is_pos()) {
            rational L(dep.lower(range));
            if (!L.is_neg() && L.root(p, r) && improves_upper(-r)) {
                auto cmp = dep.lower_is_open(range) ? llc::LT : llc::LE;
                u_dependency* d = c().lra.join_deps(dep.get_lower_dep(range),
                                                    c().lra.get_column_upper_bound_witness(v));
                propagate_lp_bound(v, cmp, -r, d);
                tightened = true;
            }
        }
        return tightened;
    }

    /**
     * range is an interval that v^p is guaranteed to lie in.
     * Strengthen the *lower* bound of v from range (mirror of the above).
     *
     * A lower bound on v is implied by:
     *   range.lower = L:
     *     p odd            -> v >= root(p, L)
     *   range.upper = U, p even, U >= 0:
     *     v >= -root(p, U)                             (|v| <= root(p, U))
     *   range.lower = L, p even, v known >= 0:
     *     v >= root(p, L)                              (resolves the disjunction)
     */
    bool monomial_bounds::tighten_lp_lower_bound(dep_interval const &range, lpvar v, unsigned p) {
        SASSERT(p > 0);
        auto improves_lower = [&](rational const& cand) {
            return !c().has_lower_bound(v) || cand > c().get_lower_bound(v);
        };
        bool tightened = false;
        rational r;
        if ((p & 1) == 1) {
            // From range.lower: v >= root(p, L).
            if (!dep.lower_is_inf(range)) {
                rational L(dep.lower(range));
                if (L.root(p, r) && improves_lower(r)) {
                    auto cmp = dep.lower_is_open(range) ? llc::GT : llc::GE;
                    propagate_lp_bound(v, cmp, r, dep.get_lower_dep(range));
                    tightened = true;
                }
            }
            return tightened;
        }
        // Even power. From range.upper: v >= -root(p, U).
        if (!dep.upper_is_inf(range)) {
            rational U(dep.upper(range));
            if (!U.is_neg() && U.root(p, r) && improves_lower(-r)) {
                auto cmp = dep.upper_is_open(range) ? llc::GT : llc::GE;
                propagate_lp_bound(v, cmp, -r, dep.get_upper_dep(range));
                tightened = true;
            }
        }
        // Even power, v known non-negative: range.lower gives v >= root(p, L).
        if (!dep.lower_is_inf(range) &&
            c().has_lower_bound(v) && !c().get_lower_bound(v).is_neg()) {
            rational L(dep.lower(range));
            if (!L.is_neg() && L.root(p, r) && improves_lower(r)) {
                auto cmp = dep.lower_is_open(range) ? llc::GT : llc::GE;
                u_dependency* d = c().lra.join_deps(dep.get_lower_dep(range),
                                                    c().lra.get_column_lower_bound_witness(v));
                propagate_lp_bound(v, cmp, r, d);
                tightened = true;
            }
        }
        return tightened;
    }

    /**
     * Ensure that bounds are integral when the variable is integer.
     */
    void monomial_bounds::propagate_lp_bound(lpvar v, lp::lconstraint_kind cmp, rational const &q, u_dependency *d) {
        SASSERT(cmp != llc::EQ && cmp != llc::NE);
        if (!c().var_is_int(v))
            c().lra.update_column_type_and_bound(v, cmp, q, d);
        else if (q.is_int()) {
            if (cmp == llc::GT)
                c().lra.update_column_type_and_bound(v, llc::GE, q + 1, d);
            else if (cmp == llc::LT)
                c().lra.update_column_type_and_bound(v, llc::LE, q - 1, d);
            else
                c().lra.update_column_type_and_bound(v, cmp, q, d);
        }
        else if (cmp == llc::GE || cmp == llc::GT)
            c().lra.update_column_type_and_bound(v, llc::GE, ceil(q), d);
        else
            c().lra.update_column_type_and_bound(v, llc::LE, floor(q), d);
    }

    bool monomial_bounds::tighten_lp_bound(dep_interval const &range, lpvar v, unsigned power) {
        bool propagated = false;
        if (tighten_lp_upper_bound(range, v, power))
            propagated = true;
        if (tighten_lp_lower_bound(range, v, power))
            propagated = true;
        return propagated;
    }
       
    bool monomial_bounds::tighten_lp_bounds() {
        bool new_bound = false;
        for (auto &m : c().emons())
            if (tighten_lp(m))
                new_bound = true;
        return new_bound;
    }

    /**
       \brief Fix the columns determined by rows that are already all but fixed.

       lar_solver::row_determines_column finds a row in which every column but one
       is fixed together with the value that row forces on the remaining column;
       both bounds of that column are then set to it. This is constant folding
       over the row, with no simplex involved.

       Only columns occurring in a monomial are considered: the point is the
       effect on nonlinear reasoning, not tighter arithmetic in general.
       is_linear takes a monic with at most one non-fixed factor out of nonlinear
       reasoning altogether, so fixing one column can linearize every monomial it
       occurs in at once. lar_solver does not derive these values on its own,
       since it only analyzes rows touched by a pivot and theory_lra drops an
       implied bound with no matching atom.

       Only one pass is made. A fixpoint loop would find strictly more, but this
       runs on every nonlinear propagation, so a later round mostly finds what the
       next call would have found anyway. Fixing every determined column measured
       better than capping how many one call may fix.
    */
    bool monomial_bounds::propagate_fixed_rows() {
        auto& lra = c().lra;
        if (!c().params().arith_nl_propagate_fixed_rows())
            return false;

        indexed_uint_set nl_vars;
        for (auto const& m : c().emons()) {
            nl_vars.insert(m.var());
            for (lpvar k : m.vars())
                nl_vars.insert(k);
        }

        bool propagated = false;
        for (unsigned i = 0; i < lra.row_count(); ++i) {
            if (lra.get_row(i).size() > 32)
                continue;
            lpvar free_j;
            rational value;
            if (!lra.row_determines_column(i, free_j, value))
                continue;
            if (!nl_vars.contains(free_j))
                continue;
            if (lra.column_has_lower_bound(free_j) && lra.column_has_upper_bound(free_j) &&
                lra.get_lower_bound(free_j).x == value && lra.get_upper_bound(free_j).x == value)
                continue;
            u_dependency* dep = lra.get_bound_constraint_witnesses_for_fixed_in_row(i);
            lra.update_column_type_and_bound(free_j, lp::lconstraint_kind::GE, value, dep);
            lra.update_column_type_and_bound(free_j, lp::lconstraint_kind::LE, value, dep);
            propagated = true;
        }
        if (propagated)
            lra.find_feasible_solution();
        return propagated;
    }

    // ================================================================
    // max_min: incremental LP bound optimization.
    //
    // A direct adaptation of smt::theory_arith::max_min (see
    // src/smt/theory_arith_aux.h).  We maximize (or minimize) a single
    // column 'v' over the current LP tableau by a bounded-effort primal
    // simplex walk: repeatedly pick a non-basic variable that improves the
    // objective, ratio-test its column to find the tightest blocking basic
    // variable, and pivot.  The tableau is left at a feasible vertex; the
    // implied bound is then read off 'v's tableau row and rounded to respect
    // the integrality of integer columns.
    //
    // Integrality is maintained during the walk (the 'maintain_integrality ==
    // true' configuration of theory_arith): every move of a column is a multiple
    // of the integrality quantum 'min_gain', so integer columns keep integral
    // values throughout.  The final implied bound is additionally floored/ceiled
    // for integer 'v'.
    // ================================================================

    static lp::impq mm_abs(lp::impq const& v) {
        return v.is_neg() ? -v : v;
    }

    // Round 'val' down to the nearest multiple of the (integral) 'divisor'.
    // Mirrors theory_arith::normalize_gain.  'divisor == -1' means "no quantum".
    static void mm_round_down(lp::impq& val, rational const& divisor) {
        if (divisor.is_one())
            val = lp::impq(lp::floor(val));
        else if (!divisor.is_minus_one())
            val = lp::impq(lp::floor(val / divisor) * divisor);
    }

    lpvar monomial_bounds::mm_basic_in_row(unsigned row) const {
        return c().lra.get_base_column_in_row(row);
    }

    // A gain is safe when the column is unbounded in the chosen direction, or
    // the required integral quantum still fits within the maximal feasible move.
    // Mirrors theory_arith::safe_gain.
    bool monomial_bounds::mm_safe_gain(mm_gain const& g) const {
        return g.unbounded || lp::impq(g.min_gain) <= g.max_gain;
    }

    // Initialize the gain for moving 'x' in direction 'inc' (increase when inc,
    // decrease otherwise) from its own bound.  For integer columns the quantum
    // 'min_gain' starts at 1.  Mirrors theory_arith::init_gains.
    monomial_bounds::mm_gain monomial_bounds::mm_init_gains(lpvar x, bool inc) const {
        auto& s = c().lra;
        mm_gain g;
        if (inc && s.column_has_upper_bound(x)) {
            g.unbounded = false;
            g.max_gain = s.column_upper_bound(x) - s.get_column_value(x);
        }
        else if (!inc && s.column_has_lower_bound(x)) {
            g.unbounded = false;
            g.max_gain = s.get_column_value(x) - s.column_lower_bound(x);
        }
        if (s.column_is_int(x))
            g.min_gain = rational::one();
        return g;
    }

    // Tighten 'g' by the room that basic variable 'x_i' (with coefficient 'a_ij'
    // on the moving column) has before hitting a bound.  When 'x_i' is an integer
    // column, the quantum 'min_gain' is raised to the lcm of the denominators of
    // the involved coefficients and both gains are rounded down to that quantum,
    // so the move keeps 'x_i' integral.  Returns true when 'max_gain' was
    // strengthened.  Mirrors theory_arith::update_gains.
    bool monomial_bounds::mm_update_gains(bool inc, lpvar x_i, rational const& a_ij, mm_gain& g) const {
        auto& s = c().lra;
        SASSERT(!a_ij.is_zero());
        if (!mm_safe_gain(g))
            return false;

        bool decrement_x_i = (inc && a_ij.is_pos()) || (!inc && a_ij.is_neg());
        bool bounded_i = false;
        lp::impq max_inc;
        if (decrement_x_i && s.column_has_lower_bound(x_i)) {
            max_inc = mm_abs((s.get_column_value(x_i) - s.column_lower_bound(x_i)) / a_ij);
            bounded_i = true;
        }
        else if (!decrement_x_i && s.column_has_upper_bound(x_i)) {
            max_inc = mm_abs((s.column_upper_bound(x_i) - s.get_column_value(x_i)) / a_ij);
            bounded_i = true;
        }

        bool xi_int = s.column_is_int(x_i);
        rational den_aij(1);
        if (xi_int)
            den_aij = denominator(a_ij);
        SASSERT(den_aij.is_pos() && den_aij.is_int());

        // Moving 'x_i' by k requires moving the entering column by k/a_ij; to keep
        // an integer 'x_i' integral the entering column must step in multiples of
        // denominator(a_ij).  Accumulate that into the quantum and re-round.
        if (xi_int && !den_aij.is_one()) {
            if (g.min_gain.is_neg())
                g.min_gain = den_aij;
            else
                g.min_gain = lcm(g.min_gain, den_aij);
            if (!g.unbounded)
                mm_round_down(g.max_gain, g.min_gain);
        }
        if (xi_int && !g.unbounded && !g.max_gain.is_int()) {
            g.max_gain = lp::impq(lp::floor(g.max_gain));
            mm_round_down(g.max_gain, g.min_gain);
        }

        if (bounded_i) {
            if (xi_int) {
                max_inc = lp::impq(lp::floor(max_inc));
                mm_round_down(max_inc, g.min_gain);
            }
            if (g.unbounded) {
                g.unbounded = false;
                g.max_gain = max_inc;
                return true;
            }
            if (g.max_gain > max_inc) {
                g.max_gain = max_inc;
                return true;
            }
        }
        return false;
    }

    // Ratio test: for entering column 'x_j' moving in direction 'inc', find the
    // basic variable 'x_i' that first blocks the move and the maximal gain.
    // Returns false (unsafe) when the integrality quantum cannot be satisfied, so
    // the caller treats 'x_j' as unusable.  Mirrors theory_arith::pick_var_to_leave.
    bool monomial_bounds::mm_pick_var_to_leave(lpvar x_j, bool inc, rational& a_ij, mm_gain& g, lpvar& x_i) const {
        auto& s = c().lra;
        x_i = null_lpvar;
        g = mm_init_gains(x_j, inc);
        // an integer entering column must sit at an integral value to move in
        // integral steps.
        if (s.column_is_int(x_j) && !s.get_column_value(x_j).is_int())
            return false;
        for (auto const& cell : s.A_r().m_columns[x_j]) {
            lpvar si = mm_basic_in_row(cell.var());
            rational const& coeff_ij = s.A_r().get_val(cell);
            if (mm_update_gains(inc, si, coeff_ij, g) ||
                (x_i == null_lpvar && !g.unbounded)) {
                x_i = si;
                a_ij = coeff_ij;
            }
        }
        return mm_safe_gain(g);
    }

    // Apply 'delta' to non-basic column 'j', propagating to dependent basic
    // columns (theory_arith::update_value).
    void monomial_bounds::mm_update_value(lpvar j, lp::impq const& delta) {
        if (delta.is_zero())
            return;
        auto& s = c().lra;
        lp::impq new_val = s.get_column_value(j) + delta;
        s.set_value_for_nbasic_column_report(j, new_val, [](unsigned) {});
    }

    // Move (now non-basic) 'x_i' maximally towards its bound in direction 'inc'
    // without violating other columns' bounds, in integral steps when 'x_i' is an
    // integer column (theory_arith::move_to_bound).
    bool monomial_bounds::mm_move_to_bound(lpvar x_i, bool inc, unsigned& best_efforts) {
        auto& s = c().lra;
        if (s.column_is_int(x_i) && !s.get_column_value(x_i).is_int()) {
            ++best_efforts;
            return false;
        }
        mm_gain g = mm_init_gains(x_i, inc);
        for (auto const& cell : s.A_r().m_columns[x_i]) {
            lpvar si = mm_basic_in_row(cell.var());
            rational const& coeff = s.A_r().get_val(cell);
            mm_update_gains(inc, si, coeff, g);
        }
        bool result = false;
        if (mm_safe_gain(g) && !g.unbounded) {
            lp::impq step = g.max_gain;
            if (!inc)
                step = -step;
            mm_update_value(x_i, step);
            result = !g.max_gain.is_zero();
        }
        if (!result)
            ++best_efforts;
        return result;
    }

    // Primal-simplex walk maximizing/minimizing 'v' (theory_arith::max_min).
    void monomial_bounds::mm_optimize(lpvar v, bool maximize) {
        auto& s = c().lra;
        unsigned best_efforts = 0;
        unsigned const max_efforts = 20;
        unsigned rounds = 0;
        unsigned const max_rounds = 200;

        while (best_efforts < max_efforts && rounds < max_rounds && !c().lp_settings().get_cancel_flag()) {
            ++rounds;
            lpvar x_j = null_lpvar, x_i = null_lpvar;
            rational a_ij(0);
            mm_gain best;          // gain of the selected move
            bool inc = false;
            bool has_bound = false;

            // Consider a candidate entering variable 'cand' whose coefficient in
            // the objective (v expressed over the non-basic columns) is
            // 'obj_coeff'.  Returns true to stop scanning (unbounded direction).
            auto consider = [&](lpvar cand, rational const& obj_coeff) -> bool {
                bool curr_inc = obj_coeff.is_pos() ? maximize : !maximize;
                if ((curr_inc && s.column_has_upper_bound(cand)) ||
                    (!curr_inc && s.column_has_lower_bound(cand)))
                    has_bound = true;
                // cannot move a variable already at the relevant bound
                if (curr_inc && s.column_has_upper_bound(cand) &&
                    s.get_column_value(cand) == s.column_upper_bound(cand))
                    return false;
                if (!curr_inc && s.column_has_lower_bound(cand) &&
                    s.get_column_value(cand) == s.column_lower_bound(cand))
                    return false;
                rational curr_a(0);
                mm_gain cur;
                lpvar curr_xi = null_lpvar;
                bool safe = mm_pick_var_to_leave(cand, curr_inc, curr_a, cur, curr_xi);
                if (!safe) {
                    // the integrality quantum cannot be met on this column
                    has_bound = true;
                    ++best_efforts;
                    return false;
                }
                if (curr_xi == null_lpvar) {
                    // limited only by its own bound (or fully unbounded)
                    x_j = cand; x_i = null_lpvar; inc = curr_inc; best = cur; a_ij = curr_a;
                    return true;
                }
                if (cur.max_gain > best.max_gain) {
                    x_i = curr_xi; x_j = cand; a_ij = curr_a; best = cur; inc = curr_inc;
                }
                else if (cur.max_gain.is_zero() && (x_i == null_lpvar || curr_xi < x_i)) {
                    x_i = curr_xi; x_j = cand; a_ij = curr_a; best = cur; inc = curr_inc;
                }
                return false;
            };

            if (!s.is_base(v)) {
                consider(v, rational::one());
            }
            else {
                unsigned ri = s.r_heading()[v];
                rational a_v(0);
                for (auto const& e : s.A_r().m_rows[ri])
                    if (e.var() == v) { a_v = e.coeff(); break; }
                for (auto const& e : s.A_r().m_rows[ri]) {
                    if (e.var() == v)
                        continue;
                    // v = -(1/a_v) * sum a_e x_e, so d(v)/d(x_e) has the sign of
                    // -a_e/a_v; only the sign steers the search direction.
                    rational objc = -e.coeff();
                    if (a_v.is_neg())
                        objc.neg();
                    if (consider(e.var(), objc))
                        break;
                }
            }

            if (!has_bound && x_i == null_lpvar && x_j == null_lpvar)
                return; // objective is unbounded in the chosen direction
            if (x_j == null_lpvar)
                return; // optimized: no improving move remains

            // a non-unit integral quantum means the exact optimum may not be
            // reachable in integral steps: count it as best-effort progress.
            if (best.min_gain.is_pos() && !best.min_gain.is_one())
                ++best_efforts;

            if (x_i == null_lpvar) {
                // move x_j directly to its own bound
                if (inc && s.column_has_upper_bound(x_j)) {
                    if (best.max_gain.is_zero())
                        return;
                    mm_update_value(x_j, best.max_gain);
                    continue;
                }
                if (!inc && s.column_has_lower_bound(x_j)) {
                    if (best.max_gain.is_zero())
                        return;
                    mm_update_value(x_j, -best.max_gain);
                    continue;
                }
                return; // unbounded
            }

            // x_j can move exactly across to its opposite bound without pivoting
            if (s.column_has_lower_bound(x_j) && s.column_has_upper_bound(x_j) &&
                s.column_lower_bound(x_j) != s.column_upper_bound(x_j) &&
                (s.column_upper_bound(x_j) - s.column_lower_bound(x_j) == best.max_gain)) {
                lp::impq step = best.max_gain;
                if (!inc)
                    step = -step;
                mm_update_value(x_j, step);
                continue;
            }

            // pivot x_j into the basis (x_i leaves); the degenerate pivot keeps
            // the current point, then move x_i to its bound to raise v.
            s.pivot(x_j, x_i);
            bool inc_xi = inc ? a_ij.is_neg() : a_ij.is_pos();
            mm_move_to_bound(x_i, inc_xi, best_efforts);
        }
    }

    // Read the implied bound on 'v' off its final tableau row and round it to
    // respect the integrality of integer columns (theory_arith::mk_bound_from_row
    // + normalize_bound).  Returns the joined explanation, or nullptr if no bound
    // is implied (e.g. a required bound on a row variable is missing).
    u_dependency* monomial_bounds::mm_bound_from_row(lpvar v, bool maximize, rational& bound) {
        auto& s = c().lra;
        if (!s.is_base(v))
            return nullptr;
        unsigned ri = s.r_heading()[v];
        auto const& row = s.A_r().m_rows[ri];
        rational a_v(0);
        for (auto const& e : row)
            if (e.var() == v) { a_v = e.coeff(); break; }
        if (a_v.is_zero())
            return nullptr;
        lp::impq acc(0);
        u_dependency* dep = nullptr;
        for (auto const& e : row) {
            if (e.var() == v)
                continue;
            lpvar k = e.var();
            rational ck = -e.coeff() / a_v; // v = sum ck * x_k
            if (ck.is_zero())
                continue;
            bool use_upper = maximize ? ck.is_pos() : ck.is_neg();
            if (use_upper) {
                if (!s.column_has_upper_bound(k))
                    return nullptr;
                acc += s.column_upper_bound(k) * ck;
                dep = s.join_deps(dep, s.get_column_upper_bound_witness(k));
            }
            else {
                if (!s.column_has_lower_bound(k))
                    return nullptr;
                acc += s.column_lower_bound(k) * ck;
                dep = s.join_deps(dep, s.get_column_lower_bound_witness(k));
            }
        }
        if (s.column_is_int(v))
            bound = maximize ? lp::floor(acc) : lp::ceil(acc);
        else
            bound = acc.x;
        return dep;
    }

    u_dependency* monomial_bounds::improve_bound(lpvar j, bool is_lower, rational& bound) {
        auto& s = c().lra;
        if (!s.is_feasible())
            return nullptr;
        bool maximize = !is_lower;
        mm_optimize(j, maximize);
        rational b(0);
        u_dependency* dep = mm_bound_from_row(j, maximize, b);
        if (!dep)
            return nullptr;
        if (is_lower) {
            if (s.column_has_lower_bound(j) && b <= s.column_lower_bound(j).x)
                return nullptr;
        }
        else {
            if (s.column_has_upper_bound(j) && b >= s.column_upper_bound(j).x)
                return nullptr;
        }
        bound = b;
        return dep;
    }

}

