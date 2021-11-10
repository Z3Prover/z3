/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation using forbidden intervals as described in
    "Solving bitvectors with MCSAT: explanations from bits and pieces"
    by S. Graham-Lengrand, D. Jovanovic, B. Dutertre.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6



--*/
#include "math/polysat/forbidden_intervals.h"
#include "math/polysat/interval.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    struct fi_record {
        eval_interval interval;
        vector<signed_constraint> side_cond;  
        signed_constraint src;
    };

    /**
     * Find a sequence of intervals that covers all of Z_modulus.
     *
     * \returns true iff such a covering exists
     * \param longest_i: the longest interval (as index into 'records')
     * \param out_seq: will contain the covering (as list of indices into 'records')
     */
    static bool find_covering_sequence(vector<fi_record> const& records, unsigned longest_i, rational modulus, unsigned_vector& out_seq) {
        rational baseline = records[longest_i].interval.hi_val();
        while (!records[longest_i].interval.currently_contains(baseline)) {
            rational best_extent = rational::zero();
            unsigned furthest_i = UINT_MAX;
            for (unsigned i = records.size(); i-- > 0; ) {
                auto const& interval = records[i].interval;
                if (interval.currently_contains(baseline)) {
                    rational extent = mod(interval.hi_val() - baseline, modulus);
                    if (extent > best_extent) {
                        best_extent = extent;
                        furthest_i = i;
                    }
                }
            }
            if (furthest_i == UINT_MAX) {
                // There's a hole we can't cover.
                // This can happen if a constraint didn't produce an interval
                // (but not necessarily, values may be covered by multiple constraints)
                return false;
            }
            SASSERT(best_extent > 0);
            out_seq.push_back(furthest_i);
            baseline = records[furthest_i].interval.hi_val();
        }
        SASSERT(out_seq.size() > 0);
        if (!records[out_seq[0]].interval.currently_contains(baseline))
            out_seq.push_back(longest_i);
        return true;
    }

    /**
    * A single constraint implies an empty interval.
    * We assume that neg_cond is a consequence of src that  
    * does not mention the variable v to be eliminated.
    */
    void forbidden_intervals::full_interval_conflict(signed_constraint src, vector<signed_constraint> const& side_cond, conflict& core) {
        core.reset();
        for (auto c : side_cond)
            core.insert(c);
        core.insert(src);
        core.set_bailout();
    }

    bool forbidden_intervals::perform(pvar v, vector<signed_constraint> const& just, conflict& core) {
        
        // Extract forbidden intervals from conflicting constraints
        vector<fi_record> records;
        rational longest_len;
        unsigned longest_i = UINT_MAX;
        for (signed_constraint c : just) {
            LOG_H3("Computing forbidden interval for: " << c);
            eval_interval interval = eval_interval::full();
            vector<signed_constraint> side_cond;
            if (get_interval(c, v, interval, side_cond)) {
                LOG("interval: " << interval);
                LOG("neg_cond: " << side_cond);
                if (interval.is_currently_empty())
                    continue;
                if (interval.is_full()) {
                    // We have a single interval covering the whole domain
                    // => the side conditions of that interval are enough to produce a conflict
                    full_interval_conflict(c, side_cond, core);
                    revert_core(core);
                    return true;
                }
                else {
                    auto const len = interval.current_len();
                    if (len > longest_len) {
                        longest_len = len;
                        longest_i = records.size();
                    }
                }
                records.push_back({ std::move(interval), std::move(side_cond), c });
            }
        }

        if (records.empty()) {
            LOG("aborted (no intervals)");
            return false;
        }


        SASSERT(longest_i != UINT_MAX);
        LOG("longest: i=" << longest_i << "; " << records[longest_i].interval);

        rational const modulus = rational::power_of_two(s.size(v));

        // Select a sequence of covering intervals
        unsigned_vector seq;
        if (!find_covering_sequence(records, longest_i, modulus, seq)) {
            LOG("aborted (intervals do not cover domain)");
            return false;
        }
        LOG("seq: " << seq);
        SASSERT(seq.size() >= 2);  // otherwise has_full should have been true

        // Update the conflict state
        // Idea:
        // - If the src constraints hold, and
        // - if the side conditions hold, and
        // - the upper bound of each interval is contained in the next interval,
        // then the forbidden intervals cover the whole domain and we have a conflict.
        // 

        core.reset();
        // Add side conditions and interval constraints
        for (unsigned seq_i = seq.size(); seq_i-- > 0; ) {
            unsigned const i = seq[seq_i];
            unsigned const next_i = seq[(seq_i + 1) % seq.size()];
            // Build constraint: upper bound of each interval is not contained in the next interval,
            // using the equivalence:  t \in [l;h[  <=>  t-l < h-l
            auto const& hi = records[i].interval.hi();
            auto const& next_lo = records[next_i].interval.lo();
            auto const& next_hi = records[next_i].interval.hi();
            auto lhs = hi - next_lo;
            auto rhs = next_hi - next_lo;
            signed_constraint c = s.m_constraints.ult(lhs, rhs);
            LOG("constraint: " << c);
            core.insert(c);
            // Side conditions
            // TODO: check whether the condition is subsumed by c?  maybe at the end do a "lemma reduction" step, to try and reduce branching?
            for (auto sc : records[i].side_cond)
                core.insert(sc);
            
            core.insert(records[i].src);
        }
        core.set_bailout();
        revert_core(core);
        return true;
    }



    /** Precondition: all variables other than v are assigned.
     *
     * \param[out] out_interval     The forbidden interval for this constraint
     * \param[out] out_neg_cond     Negation of the side condition (the side condition is true when the forbidden interval is trivial). May be NULL if the condition is constant.
     * \returns True iff a forbidden interval exists and the output parameters were set.
     */

    bool forbidden_intervals::get_interval(signed_constraint const& c, pvar v, eval_interval& out_interval, vector<signed_constraint>& out_side_cond) {
        if (!c->is_ule())
            return false;
        
        struct backtrack {
            bool released = false;
            vector<signed_constraint>& side_cond;
            unsigned sz;
            backtrack(vector<signed_constraint>& s):side_cond(s), sz(s.size()) {}
            ~backtrack() {
                if (!released)
                    side_cond.shrink(sz);
            }
        };

        backtrack _backtrack(out_side_cond);
         
        /**
        * TODO: to express the interval for coefficient 2^i symbolically,
        * we need right-shift/upper-bits-extract in the language.
        * So currently we can only do it if the coefficient is 1 or -1.
        */

        auto [ok1, a1, e1, b1] = linear_decompose(v, c->to_ule().lhs(), out_side_cond);
        auto [ok2, a2, e2, b2] = linear_decompose(v, c->to_ule().rhs(), out_side_cond);
        if (!ok1 || !ok2 || (a1.is_zero() && a2.is_zero()))
            return false;
        if (a1 != a2 && !a1.is_zero() && !a2.is_zero())
            return false;
        SASSERT(b1.is_val());
        SASSERT(b2.is_val());

        LOG("values " << a1 << " " << a2);       

        _backtrack.released = true;

        if (match_linear1(c, a1, b1, e1, a2, b2, e2, out_interval, out_side_cond))
            return true;
        if (match_linear2(c, a1, b1, e1, a2, b2, e2, out_interval, out_side_cond))
            return true;
        if (match_linear3(c, a1, b1, e1, a2, b2, e2, out_interval, out_side_cond))
            return true;
        if (match_linear4(c, a1, b1, e1, a2, b2, e2, out_interval, out_side_cond))
            return true;
        if (match_linear5(c, a1, b1, e1, a2, b2, e2, out_interval, out_side_cond))
            return true;

        _backtrack.released = false;
        return false;
    }

    void forbidden_intervals::push_eq(bool is_zero, pdd const& p, vector<signed_constraint>& side_cond) {
        SASSERT(!p.is_val() || (is_zero == p.is_zero()));
        if (p.is_val())
            return;
        else if (is_zero)
            side_cond.push_back(s.m_constraints.eq(p));
        else
            side_cond.push_back(~s.m_constraints.eq(p));
    }

    std::tuple<bool, rational, pdd, pdd> forbidden_intervals::linear_decompose(pvar v, pdd const& p, vector<signed_constraint>& out_side_cond) {
        auto& m = p.manager();
        pdd q = m.zero();
        pdd e = m.zero();
        unsigned const deg = p.degree(v);
        if (deg == 0)
            e = p;
        else if (deg == 1)
            p.factor(v, 1, q, e);
        else
            return std::tuple(false, rational(0), q, e);

        if (!q.is_val()) {
            pdd r = q.subst_val(s.assignment());
            if (!r.is_val())
                return std::tuple(false, rational(0), q, e);
            out_side_cond.push_back(s.eq(q, r));
            q = r;
        }
        auto b = e.subst_val(s.assignment());
        return std::tuple(b.is_val(), q.val(), e, b);
    };

    eval_interval forbidden_intervals::to_interval(
        signed_constraint const& c, bool is_trivial, rational const& coeff,
        rational & lo_val, pdd & lo,
        rational & hi_val, pdd & hi) {
        
        dd::pdd_manager& m = lo.manager();

        if (is_trivial) {
            if (c.is_positive())
                // TODO: we cannot use empty intervals for interpolation. So we
                // can remove the empty case (make it represent 'full' instead),
                // and return 'false' here. Then we do not need the proper/full
                // tag on intervals.
                return eval_interval::empty(m);
            else
                return eval_interval::full();
        }

        if (!coeff.is_one()) {
            rational pow2 = m.max_value() + 1;
            SASSERT(coeff == m.max_value());
            // Transform according to:  y \in [l;u[  <=>  -y \in [1-u;1-l[
            //      -y \in [1-u;1-l[
            //      <=>  -y - (1 - u) < (1 - l) - (1 - u)    { by: y \in [l;u[  <=>  y - l < u - l }
            //      <=>  u - y - 1 < u - l                   { simplified }
            //      <=>  (u-l) - (u-y-1) - 1 < u-l           { by: a < b  <=>  b - a - 1 < b }
            //      <=>  y - l < u - l                       { simplified }
            //      <=>  y \in [l;u[.
            lo = 1 - lo;
            hi = 1 - hi;
            swap(lo, hi);
            lo_val = mod(1 - lo_val, pow2);
            hi_val = mod(1 - hi_val, pow2);
            lo_val.swap(hi_val);
        }

        if (c.is_positive())
            return eval_interval::proper(lo, lo_val, hi, hi_val);
        else
            return eval_interval::proper(hi, hi_val, lo, lo_val);
    }

    /**
    * Match  e1 + t <= e2, with t = 2^j1*y
    * condition for empty/full: e2 == -1
    */
    bool forbidden_intervals::match_linear1(signed_constraint const& c,
        rational const& a1, pdd const& b1, pdd const& e1, 
        rational const& a2, pdd const& b2, pdd const& e2,
        eval_interval& interval, vector<signed_constraint>& side_cond) {
        if (a2.is_zero() && coefficient_is_01(e1.manager(), a1)) {
            SASSERT(!a1.is_zero());
            bool is_trivial = (b2 + 1).is_zero();
            push_eq(is_trivial, e2 + 1, side_cond);
            auto lo = e2 - e1 + 1;
            rational lo_val = (b2 - b1 + 1).val();
            auto hi = -e1;
            rational hi_val = (-b1).val();
            interval = to_interval(c, is_trivial, a1, lo_val, lo, hi_val, hi);
            return true;
        }
        return false;
    }

    /**
     * e1 <= e2 + t, with t = 2^j2*y
     * condition for empty/full: e1 == 0
     */
    bool forbidden_intervals::match_linear2(signed_constraint const& c,
        rational const& a1, pdd const& b1, pdd const& e1,
        rational const& a2, pdd const& b2, pdd const& e2,
        eval_interval& interval, vector<signed_constraint>& side_cond) {
        if (a1.is_zero() && coefficient_is_01(e1.manager(), a2)) {
            SASSERT(!a2.is_zero());
            bool is_trivial = b1.is_zero();
            push_eq(is_trivial, e1, side_cond);
            auto lo = -e2;
            rational lo_val = (-b2).val();
            auto hi = e1 - e2;
            rational hi_val = (b1 - b2).val();
            interval = to_interval(c, is_trivial, a2, lo_val, lo, hi_val, hi);
            return true;
        }
        return false;
    }

    /**
     * e1 + t <= e2 + t, with t = 2^j1*y = 2^j2*y
     * condition for empty/full: e1 == e2/
     */
    bool forbidden_intervals::match_linear3(signed_constraint const& c,
        rational const& a1, pdd const& b1, pdd const& e1,
        rational const& a2, pdd const& b2, pdd const& e2,
        eval_interval& interval, vector<signed_constraint>& side_cond) {
        if (coefficient_is_01(e1.manager(), a1) && coefficient_is_01(e1.manager(), a2) && a1 == a2 && !a1.is_zero()) {
            bool is_trivial = b1.val() == b2.val();
            push_eq(is_trivial, e1 - e2, side_cond);
            auto lo = -e2;
            rational lo_val = (-b2).val();
            auto hi = -e1;
            rational hi_val = (-b1).val();
            interval = to_interval(c, is_trivial, a1, lo_val, lo, hi_val, hi);
            return true;
        }
        return false;
    }

    /**
    * a1*y + e1 = 0, with a1 odd
    */
    bool forbidden_intervals::match_linear4(signed_constraint const& c,
        rational const& a1, pdd const& b1, pdd const& e1,
        rational const& a2, pdd const& b2, pdd const& e2,
        eval_interval& interval, vector<signed_constraint>& side_cond) {
        if (a1.is_odd() && a2.is_zero() && b2.val().is_zero()) {
            push_eq(false, e2, side_cond);
            rational a_inv, pow2 = e1.manager().max_value() + 1;
            VERIFY(a1.mult_inverse(e1.manager().power_of_2(), a_inv));
            auto lo = -e1 * a_inv;
            auto lo_val = mod(-b1.val() * a_inv, pow2);
            auto hi = lo + 1;
            auto hi_val = mod(lo_val + 1, pow2);
            interval = to_interval(c, false, rational::one(), lo_val, lo, hi_val, hi);
            return true;
        }
        return false;
    }

    /**
     * Ad-hoc linear forbidden intervals 
     * ax <= b, b != -1, a < b:     x not in [ceil((b+1)/a) .. floor((2^K-1)/a)]
     * b <= ax, 0 < a < b:          x not in [0 .. floor((b-1)/a)] 
     * ax < b, a < b:               x not in [ceil(b/a) .. floor((2^K-1)/a)]
     * b < ax, 0 < a <= b:          x not in [0 .. floor(b/a)]     
     * 
     * TODO: generalize to ax + b <= c scenarios where ax does not overflow 
     * and ax+b does not overflow, but is larger than c
     * Scenarios:
     *  - ax + b <= c
     *  - ax + b < c
     *  - c <= ax + b
     *  - c < ax + b
     */
    bool forbidden_intervals::match_linear5(signed_constraint const& c,
        rational const& a1, pdd const& b1, pdd const& e1,
        rational const& a2, pdd const& b2, pdd const& e2,
        eval_interval& interval, vector<signed_constraint>& side_cond) {
        auto& m = e1.manager();

        // ax <= b, b != -1, a < b:     x not in [ceil((b+1)/a) .. floor((2^K-1)/a)]
        if (c.is_positive() && 
            !a1.is_zero() && !a1.is_one() && 
            a2.is_zero() && b1.is_zero() && e2.is_val() && 
            a1 < b2.val() && b2.val() != m.max_value()) {
            if (!e1.is_val())
                side_cond.push_back(s.eq(e1));
            auto lo_val = ceil((b2.val() + 1) / a1);
            auto hi_val = floor(m.max_value() / a1) + 1;
            SASSERT(lo_val < hi_val);
            auto lo = m.mk_val(lo_val);
            auto hi = m.mk_val(hi_val);
            interval = eval_interval::proper(lo, lo_val, hi, hi_val);
            return true;            
        }

        // b <= ax, 0 < a < b:          x not in [0 .. floor((b-1)/a)] 
        if (c.is_positive() && 
            !a2.is_zero() && !a2.is_one() && 
            a1.is_zero() && b2.is_zero() &&
            a2 < b1.val() && e1.is_val()) {
            if (!e2.is_val())
                side_cond.push_back(s.eq(e2));
            rational lo_val = rational::zero();
            rational hi_val = floor((b1.val() - 1) / a2) + 1;
            SASSERT(lo_val < hi_val);
            auto lo = m.mk_val(lo_val);
            auto hi = m.mk_val(hi_val);
            interval = eval_interval::proper(lo, lo_val, hi, hi_val);
            return true;
        }

        // ax < b, a < b:               x not in [ceil(b/a) .. floor((2^K-1)/a)]
        if (c.is_negative() && 
            !a2.is_zero() && !a2.is_one() && b2.is_zero() && 
            a1.is_zero() && e1.is_val() && a2 < b1.val()) {
            if (!e2.is_val())
                side_cond.push_back(s.eq(e2));
            rational lo_val = ceil(b1.val() / a2);
            rational hi_val = floor(m.max_value() / a2) + 1;
            auto lo = m.mk_val(lo_val);
            auto hi = m.mk_val(hi_val);
            interval = eval_interval::proper(lo, lo_val, hi, hi_val);
            return true;
        }

        // b < ax, 0 < a <= b:          x not in [0 .. floor(b/a)]     
        if (c.is_negative() &&
            !a1.is_zero() && !a1.is_one() && b1.is_zero() &&
            a2.is_zero() && e2.is_val() && a1 <= b2.val()) { 
            if (!e1.is_val())
                side_cond.push_back(s.eq(e2));
            rational lo_val = rational::zero();
            rational hi_val = floor(b2.val() / a1) + 1;
            auto lo = m.mk_val(lo_val);
            auto hi = m.mk_val(hi_val);
            interval = eval_interval::proper(lo, lo_val, hi, hi_val);
            return true;
        }
        return false;
    }

    void forbidden_intervals::revert_core(conflict& core) {
        for (auto c : core) {
            if (c.bvalue(s) == l_false) {
                core.reset();
                core.set(~c);
                return;
            }
        }
    }

}
