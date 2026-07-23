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

    bool monomial_bounds::propagate_linear_monomials() {        
        bool propagated = false;
        for (lpvar v : c().m_monics_with_changed_bounds) {
            if (!c().is_monic_var(v))
                continue;
            monic& m = c().emon(v);
            if (propagate_linear_monomial(m))
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

    bool monomial_bounds::propagate_linear_monomial(monic & m) {
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
        IF_VERBOSE(1, verbose_stream() << "propagate_lp_bound: v=" << v << " cmp=" << cmp << " q=" << q << "\n";);
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
        if (propagate_linear_monomials())
            new_bound = true;
        IF_VERBOSE(1, verbose_stream() << "tighten_lp_bounds: new_bound=" << new_bound << "\n";);
        return new_bound;
    }

}

