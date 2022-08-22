/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Clause Simplification

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2022-08-22

Notes:

--*/
#include "math/polysat/solver.h"
#include "math/polysat/simplify_clause.h"

namespace polysat {

    simplify_clause::simplify_clause(solver& s):
        s(s)
    {}

    bool simplify_clause::apply(clause& cl)
    {
        bool changed = false;
        if (try_unilinear_subsumption(cl)) changed = true;
        return changed;
    }

    struct subs_entry : fi_record {
        unsigned lit_idx;
        pvar var;
        bool subsumed;
    };

    /**
     * Test simple subsumption between univariate and linear literals, i.e.,
     * the case where both literals can be represented by a single contiguous forbidden interval.
     *
     * A literal C subsumes literal D if the forbidden interval of C is a subset of the forbidden interval of D.
     * C subsumes D  <==  fi(C) subset fi(D)
     */
    bool simplify_clause::try_unilinear_subsumption(clause& cl)
    {
        LOG_H2("Unilinear subsumption for: " << cl);
        subs_entry entry;
        vector<subs_entry> entries;  // TODO: we don't need to store the full fi_record
        forbidden_intervals fi(s);
        // Find univariate and linear constraints and their forbidden intervals
        for (unsigned i = 0; i < cl.size(); ++i) {
            sat::literal lit = cl[i];
            signed_constraint c = s.lit2cnstr(lit);
            if (!c->is_ule())
                continue;
            auto const& ule = c->to_ule();
            pdd const& lhs = ule.lhs();
            pdd const& rhs = ule.rhs();
            if (!lhs.is_val() && !lhs.is_unilinear())
                continue;
            if (!rhs.is_val() && !rhs.is_unilinear())
                continue;
            if (!lhs.is_val() && !rhs.is_val() && lhs.var() != rhs.var())
                continue;
            LOG("Literal " << lit_pp(s, lit));
            SASSERT(!lhs.is_val() || !rhs.is_val());  // purely numeric constraints should have been filtered out by the clause_builder
            pvar v = rhs.is_val() ? lhs.var() : rhs.var();
            VERIFY(fi.get_interval(c, v, entry));
            if (entry.coeff != 1)
                continue;
            entry.lit_idx = i;
            entry.var = v;
            entry.subsumed = false;
            entries.push_back(entry);
        }
        // Check subsumption between intervals for the same variable
        bool any_subsumed = false;
        for (unsigned i = 0; i < entries.size(); ++i) {
            subs_entry& e = entries[i];
            if (e.subsumed)
                continue;
            for (unsigned j = i + 1; j < entries.size(); ++j) {
                subs_entry& f = entries[j];
                SASSERT(e.lit_idx != f.lit_idx);
                if (e.var != f.var)
                    continue;
                if (e.interval.currently_contains(f.interval)) {
                    // f subset of e  ==>  f.src subsumes e.src
                    LOG("Literal " << cl[e.lit_idx] << " subsumed by " << cl[f.lit_idx]);
                    e.subsumed = true;
                    any_subsumed = true;
                    break;
                }
                if (f.interval.currently_contains(e.interval)) {
                    // e subset of f  ==>  e.src subsumes f.src
                    LOG("Literal " << cl[f.lit_idx] << " subsumed by " << cl[e.lit_idx]);
                    f.subsumed = true;
                    any_subsumed = true;
                    continue;
                }
            }
        }
        // Remove subsumed literals
        if (!any_subsumed)
            return false;
        auto e_it = entries.begin();
        while (e_it != entries.end() && !e_it->subsumed)
            ++e_it;
        SASSERT(e_it != entries.end() && e_it->subsumed);
        unsigned next_subsumed_i = e_it->lit_idx;
        unsigned i = next_subsumed_i;
        unsigned j = next_subsumed_i;
        while (i < cl.size()) {
            if (i == next_subsumed_i) {
                while (e_it != entries.end() && !e_it->subsumed)
                    ++e_it;
                if (e_it != entries.end())
                    next_subsumed_i = e_it->lit_idx;
                // NOTE: no need to update next_subsumed_i in the else-branch since we already passed that location
                i++;
            }
            else
                cl[j++] = cl[i++];
        }
        cl.m_literals.shrink(j);
        return true;
    }

}
