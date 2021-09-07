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
move "forbidden interval method from constraints

--*/
#include "math/polysat/forbidden_intervals.h"
#include "math/polysat/clause_builder.h"
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
    void forbidden_intervals::full_interval_conflict(signed_constraint src, signed_constraint neg_cond, conflict_core& core) {
        SASSERT(neg_cond);
        core.insert(~neg_cond);
        core.remove(src); // or add a lemma?
    }

    bool forbidden_intervals::perform(solver& s, pvar v, conflict_core& core) {

        // Extract forbidden intervals from conflicting constraints
        vector<fi_record> records;
        rational longest_len;
        unsigned longest_i = UINT_MAX;
        for (signed_constraint c : core) {
            LOG_H3("Computing forbidden interval for: " << c);
            eval_interval interval = eval_interval::full();
            signed_constraint neg_cond;
            if (c->forbidden_interval(s, c.is_positive(), v, interval, neg_cond)) {
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

        unsigned lemma_lvl = 0;
        for (unsigned i : seq) {
            signed_constraint const& c = records[i].src;
            lemma_lvl = std::max(lemma_lvl, c->level());
        }

        // Update the conflict state
        // Idea:
        // - If the src constraints hold, and
        // - if the side conditions hold, and
        // - the upper bound of each interval is contained in the next interval,
        // then the forbidden intervals cover the whole domain and we have a conflict.
        // 

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
            signed_constraint c = s.m_constraints.ult(lemma_lvl, lhs, rhs);
            LOG("constraint: " << c);
            core.insert(c);
            // Side conditions
            // TODO: check whether the condition is subsumed by c?  maybe at the end do a "lemma reduction" step, to try and reduce branching?
            signed_constraint& neg_cond = records[i].neg_cond;
            if (neg_cond)
                core.insert(std::move(~neg_cond));

            core.remove(records[i].src);
        }
        return true;
    }

}
