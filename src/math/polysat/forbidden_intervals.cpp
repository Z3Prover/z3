/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation using forbidden intervals as described in
    "Solving bitvectors with MCSAT: explanations from bits and pieces"
    by S. Graham-Lengrand, D. Jovanovic, B. Dutertre.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6


TODO:
compute forbidden interval coefficients a1, a2 modulo current assignment to handle pseudo-linear cases.
test_mont_bounds(8) produces constraint 13 <= v1*v2, where v2 = 1, then v1 is linear and is constrained above 13.



--*/
#include "math/polysat/forbidden_intervals.h"
#include "math/polysat/interval.h"
#include "math/polysat/log.h"

namespace polysat {

    struct fi_record {
        eval_interval interval;
        signed_constraint neg_cond;  // could be multiple constraints later
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
    void forbidden_intervals::full_interval_conflict(signed_constraint src, signed_constraint neg_cond, conflict& core) {
        SASSERT(neg_cond);
        core.reset();
        core.insert(~neg_cond);
        core.insert(src);
        core.set_bailout();
    }

    bool forbidden_intervals::perform(solver& s, pvar v, vector<signed_constraint> const& just, conflict& core) {
        
        // Extract forbidden intervals from conflicting constraints
        vector<fi_record> records;
        rational longest_len;
        unsigned longest_i = UINT_MAX;
        for (signed_constraint c : just) {
            LOG_H3("Computing forbidden interval for: " << c);
            eval_interval interval = eval_interval::full();
            signed_constraint neg_cond;
            if (get_interval(s, c, v, interval, neg_cond)) {
                LOG("interval: " << interval);
                LOG("neg_cond: " << neg_cond);
                if (interval.is_currently_empty())
                    continue;
                if (interval.is_full()) {
                    // We have a single interval covering the whole domain
                    // => the side conditions of that interval are enough to produce a conflict
                    full_interval_conflict(c, neg_cond, core);
                    return true;
                }
                else {
                    auto const len = interval.current_len();
                    if (len > longest_len) {
                        longest_len = len;
                        longest_i = records.size();
                    }
                }
                records.push_back({ std::move(interval), std::move(neg_cond), c });
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
            auto hi = records[i].interval.hi();
            auto next_lo = records[next_i].interval.lo();
            auto next_hi = records[next_i].interval.hi();
            auto lhs = hi - next_lo;
            auto rhs = next_hi - next_lo;
            // NB: do we really have to pass in the level to this new literal?
            // seems separating the level from the constraint is what we want
            // the level of a literal is when it was assigned. Lemmas could have unassigned literals.
            signed_constraint c = s.m_constraints.ult(lhs, rhs);
            LOG("constraint: " << c);
            core.insert(c);
            // Side conditions
            // TODO: check whether the condition is subsumed by c?  maybe at the end do a "lemma reduction" step, to try and reduce branching?
            signed_constraint& neg_cond = records[i].neg_cond;
            if (neg_cond)
                core.insert(~neg_cond);
            
            core.insert(records[i].src);
        }
        core.set_bailout();
        return true;
    }


    /** Precondition: all variables other than v are assigned.
     *
     * \param[out] out_interval     The forbidden interval for this constraint
     * \param[out] out_neg_cond     Negation of the side condition (the side condition is true when the forbidden interval is trivial). May be NULL if the condition is constant.
     * \returns True iff a forbidden interval exists and the output parameters were set.
     */

    bool forbidden_intervals::get_interval(solver& s, signed_constraint const& c, pvar v, eval_interval& out_interval, signed_constraint& out_neg_cond)
    {
        if (!c->is_ule())
            return false;
        // Current only works when degree(v) is at most one on both sides
        pdd lhs = c->to_ule().lhs();
        pdd rhs = c->to_ule().rhs();
        unsigned const deg1 = lhs.degree(v);
        unsigned const deg2 = rhs.degree(v);
        if (deg1 > 1 || deg2 > 1)
            return false;

        if (deg1 == 0 && deg2 == 0) {
            return false;
            UNREACHABLE();  // this case is not useful for conflict resolution (but it could be handled in principle)
            // i is empty or full, condition would be this constraint itself?
            return true;
        }

        unsigned const sz = s.size(v);
        dd::pdd_manager& m = s.sz2pdd(sz);
        rational const pow2 = rational::power_of_two(sz);
        rational const minus_one = pow2 - 1;

        pdd p1 = m.zero();
        pdd e1 = m.zero();
        if (deg1 == 0)
            e1 = lhs;
        else
            lhs.factor(v, 1, p1, e1);

        pdd p2 = m.zero();
        pdd e2 = m.zero();
        if (deg2 == 0)
            e2 = rhs;
        else
            rhs.factor(v, 1, p2, e2);

        // Interval extraction only works if v-coefficients are the same
        // LOG("factored " << deg1 << " " << deg2 << " " << p1 << " " << p2);
        if (deg1 != 0 && deg2 != 0 && p1 != p2)
            return false;

        // LOG("valued " << p1.is_val() << " " << p2.is_val());
        // TODO: p1, p2 could be values under assignment.
        // It could allow applying forbidden interval elimination under the assignment.
        // test_monot_bounds(8)
        // 
        // Currently only works if coefficient is a power of two
        if (!p1.is_val())
            return false;
        if (!p2.is_val())
            return false;
        rational a1 = p1.val();
        rational a2 = p2.val();
        // TODO: to express the interval for coefficient 2^i symbolically, we need right-shift/upper-bits-extract in the language.
        // So currently we can only do it if the coefficient is 1 or -1.
        LOG("values " << a1 << " " << a2);
        if (!a1.is_zero() && !a1.is_one() && a1 != minus_one)
            return false;
        if (!a2.is_zero() && !a2.is_one() && a2 != minus_one)
            return false;
        /*
        unsigned j1 = 0;
        unsigned j2 = 0;
        if (!a1.is_zero() && !a1.is_power_of_two(j1))
            return false;
        if (!a2.is_zero() && !a2.is_power_of_two(j2))
            return false;
        */

        rational const y_coeff = a1.is_zero() ? a2 : a1;
        SASSERT(!y_coeff.is_zero());

        // Concrete values of evaluable terms
        auto e1s = e1.subst_val(s.assignment());
        auto e2s = e2.subst_val(s.assignment());
        // TODO: this is not always true! cjust[v]/conflict may contain unassigned variables (they're coming from a previous conflict, but together they lead to a conflict. need something else to handle that.)
        if (!e1s.is_val())
            return false;
        if (!e2s.is_val())
            return false;
        SASSERT(e1s.is_val());
        SASSERT(e2s.is_val());

        bool is_trivial;
        pdd condition_body = m.zero();
        pdd lo = m.zero();
        rational lo_val = rational::zero();
        pdd hi = m.zero();
        rational hi_val = rational::zero();

        if (a2.is_zero()) {
            SASSERT(!a1.is_zero());
            // e1 + t <= e2, with t = 2^j1*y
            // condition for empty/full: e2 == -1
            is_trivial = (e2s + 1).is_zero();
            condition_body = e2 + 1;
            if (!is_trivial) {
                lo = e2 - e1 + 1;
                lo_val = (e2s - e1s + 1).val();
                hi = -e1;
                hi_val = (-e1s).val();
            }
        }
        else if (a1.is_zero()) {
            SASSERT(!a2.is_zero());
            // e1 <= e2 + t, with t = 2^j2*y
            // condition for empty/full: e1 == 0
            is_trivial = e1s.is_zero();
            condition_body = e1;
            if (!is_trivial) {
                lo = -e2;
                lo_val = (-e2s).val();
                hi = e1 - e2;
                hi_val = (e1s - e2s).val();
            }
        }
        else {
            SASSERT(!a1.is_zero());
            SASSERT(!a2.is_zero());
            SASSERT_EQ(a1, a2);
            // e1 + t <= e2 + t, with t = 2^j1*y = 2^j2*y
            // condition for empty/full: e1 == e2
            is_trivial = e1s.val() == e2s.val();
            condition_body = e1 - e2;
            if (!is_trivial) {
                lo = -e2;
                lo_val = (-e2s).val();
                hi = -e1;
                hi_val = (-e1s).val();
            }
        }

        if (condition_body.is_val()) {
            // Condition is trivial; no need to create a constraint for that.
            SASSERT(is_trivial == condition_body.is_zero());
            out_neg_cond = nullptr;
        }
        else if (is_trivial)
            out_neg_cond = ~s.m_constraints.eq(condition_body);
        else
            out_neg_cond = s.m_constraints.eq(condition_body);

        if (is_trivial) {
            if (c.is_positive())
                // TODO: we cannot use empty intervals for interpolation. So we
                // can remove the empty case (make it represent 'full' instead),
                // and return 'false' here. Then we do not need the proper/full
                // tag on intervals.
                out_interval = eval_interval::empty(m);
            else
                out_interval = eval_interval::full();
        }
        else {
            if (y_coeff == minus_one) {
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
            else
                SASSERT(y_coeff.is_one());

            if (!c.is_positive()) {
                swap(lo, hi);
                lo_val.swap(hi_val);
            }
            out_interval = eval_interval::proper(lo, lo_val, hi, hi_val);
        }

        return true;
    }

}
