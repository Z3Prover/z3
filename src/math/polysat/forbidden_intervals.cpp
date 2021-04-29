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
#include "math/polysat/log.h"

namespace polysat {

    struct fi_record {
        eval_interval interval;
        scoped_ptr<constraint> cond;  // could be multiple constraints later
        constraint* src;
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

    bool forbidden_intervals::explain(solver& s, ptr_vector<constraint> const& conflict, pvar v, scoped_ptr_vector<constraint>& out_lemma) {

        // Extract forbidden intervals from conflicting constraints
        vector<fi_record> records;
        bool has_full = false;
        rational longest_len;
        unsigned longest_i = UINT_MAX;
        for (constraint* c : conflict) {
            LOG("constraint: " << *c);
            eval_interval interval = eval_interval::full();
            constraint* cond = nullptr;  // TODO: change to scoped_ptr
            if (c->forbidden_interval(s, v, interval, cond)) {
                LOG("~> interval: " << interval);
                if (cond)
                    LOG("       cond: " << *cond);
                else
                    LOG("       cond: <null>");
                if (interval.is_currently_empty()) {
                    dealloc(cond);
                    continue;
                }
                if (interval.is_full())
                    has_full = true;
                else {
                    auto const len = interval.current_len();
                    if (len > longest_len) {
                        longest_len = len;
                        longest_i = records.size();
                    }
                }
                records.push_back({std::move(interval), cond, c});
                if (has_full)
                    break;
            }
        }

        if (has_full) {
            auto const& full_record = records.back();
            SASSERT(full_record.interval.is_full());
            LOG("has_full: " << std::boolalpha << has_full);
            // TODO: use full interval to explain
            NOT_IMPLEMENTED_YET();
            return false;
        }

        if (records.empty())
            return false;

        SASSERT(longest_i != UINT_MAX);
        LOG("longest: i=" << longest_i << "; " << records[longest_i].interval);

        rational const modulus = rational::power_of_two(s.size(v));

        // Select a sequence of covering intervals
        unsigned_vector seq;
        if (!find_covering_sequence(records, longest_i, modulus, seq)) {
            return false;
        }
        LOG("seq: " << seq);

        p_dependency* d = nullptr;
        unsigned lemma_lvl = 0;
        for (unsigned i : seq) {
            constraint* c = records[i].src;
            d = s.m_dm.mk_join(d, c->dep());
            lemma_lvl = std::max(lemma_lvl, c->level());
        }
        p_dependency_ref lemma_dep(d, s.m_dm);

        // Create lemma
        // Idea:
        // - If the side conditions hold, and
        // - the upper bound of each interval is contained in the next interval,
        // then the forbidden intervals cover the whole domain and we have a conflict.
        // We learn the negation of this conjunction.
        for (unsigned seq_i = seq.size(); seq_i-- > 0; ) {
            unsigned const i = seq[seq_i];
            unsigned const next_i = seq[(seq_i+1) % seq.size()];
            // Build constraint: upper bound of each interval is not contained in the next interval,
            // using the equivalence:  t \in [l;h[  <=>  t-l < h-l
            auto const& hi = records[i].interval.hi();
            auto const& next_lo = records[next_i].interval.lo();
            auto const& next_hi = records[next_i].interval.hi();
            auto const& lhs = hi - next_lo;
            auto const& rhs = next_hi - next_lo;
            constraint* c = constraint::ult(lemma_lvl, s.m_next_bvar++, neg_t, lhs, rhs, lemma_dep);
            LOG("constraint: " << *c);
            out_lemma.push_back(c);
            // Side conditions
            // TODO: check whether the condition is subsumed by c?  maybe at the end do a "lemma reduction" step, to try and reduce branching?
            scoped_ptr<constraint>& cond = records[i].cond;
            if (cond)
                out_lemma.push_back(cond.detach());
        }

        return true;
    }

}
