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

    bool simplify_clause::apply(clause& cl) {
        if (try_constant_subsumptions(cl))
            return true;
        return false;
    }

    pdd simplify_clause::abstract(pdd const& p, pdd& v) {
        if (p.is_val())
            return p;
        if (p.is_unilinear()) {
            v = p.manager().mk_var(p.var());
            return p;
        }
        unsigned max_var = p.var();
        auto& m = p.manager();
        pdd r(m);
        v = p - p.offset();
        r = p - v;
        auto const& lc = p.leading_coefficient();
        if (mod(-lc, m.two_to_N()) < lc) {
            v = -v;
            r -= m.mk_var(max_var);
        }
        else 
            r += m.mk_var(max_var);
        return r;
    }

    void simplify_clause::prepare_subs_entry(subs_entry& entry, signed_constraint c) {
        entry.valid = false;
        if (!c->is_ule())
            return;
        forbidden_intervals fi(s);

        auto const& ule = c->to_ule();
        auto& m = ule.lhs().manager();
        signed_constraint sc = c;
        pdd v_lhs(m), v_rhs(m);
        pdd lhs = abstract(ule.lhs(), v_lhs);
        pdd rhs = abstract(ule.rhs(), v_rhs);
        if (lhs.is_val() && rhs.is_val())
            return;
        if (!lhs.is_val() && !rhs.is_val() && v_lhs != v_rhs)
            return;
        if (lhs != ule.lhs() || rhs != ule.rhs()) {
            sc = s.ule(lhs, rhs);
            if (c.is_negative())
                sc.negate();
        }
        pvar v = rhs.is_val() ? lhs.var() : rhs.var();
        VERIFY(fi.get_interval(sc, v, entry));
        if (entry.coeff != 1)
            return;
        entry.var = lhs.is_val() ? v_rhs : v_lhs;
        entry.subsumed = false;
        entry.valid = true;
    }


    /**
     * Test simple subsumption between univariate and linear literals, i.e.,
     * the case where both literals can be represented by a single contiguous forbidden interval.
     *
     * A literal C subsumes literal D if the forbidden interval of C is a subset of the forbidden interval of D.
     * C subsumes D  <==  fi(C) subset fi(D)
     */
    bool simplify_clause::try_unilinear_subsumption(clause& cl) {
        LOG_H2("Unilinear subsumption for: " << cl);

        m_entries.reserve(cl.size());
        for (unsigned i = 0; i < cl.size(); ++i) {
            subs_entry& entry = m_entries[i];
            sat::literal lit = cl[i];
            LOG("Literal " << lit_pp(s, lit));
            signed_constraint c = s.lit2cnstr(lit);
            prepare_subs_entry(entry, c);
        }
        
        // Check subsumption between intervals for the same variable
        bool any_subsumed = false;
        for (unsigned i = 0; i < cl.size(); ++i) {
            subs_entry& e = m_entries[i];
            if (e.subsumed || !e.valid)
                continue;
            for (unsigned j = 0; j < cl.size(); ++j) {
                subs_entry& f = m_entries[j];
                if (f.subsumed || !f.valid || i == j || !e.var || !f.var || *e.var != *f.var)
                    continue;
                if (e.interval.currently_contains(f.interval)) {
                    // f subset of e  ==>  f.src subsumes e.src
                    LOG("Literal " << s.lit2cnstr(cl[i]) << " subsumed by " << s.lit2cnstr(cl[j]));
                    e.subsumed = true;
                    any_subsumed = true;
                    break;
                }
            }
        }
        // Remove subsumed literals
        if (!any_subsumed)
            return false;
        unsigned j = 0;
        for (unsigned i = 0; i < cl.size(); ++i) 
            if (!m_entries[i].subsumed)
                cl[j++] = cl[i];
        cl.m_literals.shrink(j);
        return true;
    }

}
