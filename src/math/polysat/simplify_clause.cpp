/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Clause Simplification

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2022-08-22

Notes:

    TODO: check why it fails with test_l2
          at least 7 should be subsumed by 8 ??? (or the other way around)
          and 6 should also be subsumed (but there's a difference in coefficient)
        Lemma: 7 -6 -0 8 -1
            7: -1 <= 2*v1 + 2  [ bvalue=l_false @1 pwatched=0  ]
            -6: v1 + -1 != 0  [ bvalue=l_false @1 pwatched=0  ]
            -0: v1 + 2*v0 + 1 != 0  [ bvalue=l_false @0 pwatched=1  ]
            8: 1 <= 2*v1 + 2  [ bvalue=l_false @1 pwatched=0  ]
            -1: 2*v1 + v0 != 0  [ bvalue=l_false @0 pwatched=1  ]

    TODO: from test_l5, conflict #2:   (mod 2^3)
        Lemma: -1 \/ -2 \/ -6 \/ -7
           -1: 2*v1 + v0 + 4 != 0  [ bvalue=l_false @0 pwatched=1  ]
           -2: 4*v1 + v0 + 4 != 0  [ bvalue=l_false @0 pwatched=1  ]
           -6: 2*v1 + -2 != 0  [ bvalue=l_undef pwatched=0  ]
           -7: v1 + -1 != 0  [ bvalue=l_undef pwatched=0  ]

            -7  ==>  v1 \not\in { 1 }
            -6  ==>  v1 \not\in { 1, 5 }
            ==> -6 subsumes -7

    TODO: from test_ineq_basic5:
        Lemma: -0 \/ -1 \/ 2 \/ 3
           -0: -4 > v1 + v0  [ bvalue=l_false @0 pwatched=1  ]
           -1: v1 > 2  [ bvalue=l_false @0 pwatched=1  ]
           2: -3 <= -1*v0 + -7  [ bvalue=l_undef pwatched=0  ]
           3: -4 <= v0  [ bvalue=l_undef pwatched=0  ]

--*/
#include "math/polysat/solver.h"
#include "math/polysat/simplify_clause.h"

namespace polysat {

    simplify_clause::simplify_clause(solver& s):
        s(s)
    {}

    bool simplify_clause::apply(clause& cl) {
        if (try_equal_body_subsumptions(cl))
            return true;
        return false;
    }

    /**
     * Abstract body of the polynomial (i.e., the variable terms without constant term)
     * by a single variable.
     *
     * abstract(2*x*y + x + 7)
     * -> v = 2*x*y + x
     *    r = x + 7
     *
     * \return Abstracted polynomial
     * \param[out] v Body
     */
    pdd simplify_clause::abstract(pdd const& p, pdd& v) {
        if (p.is_val()) {
            SASSERT(v.is_zero());
            return p;
        }
        if (p.is_unilinear()) {
            // we need an interval with coeff == 1 to be able to compare intervals easily
            auto const& coeff = p.hi().val();
            if (coeff.is_one() || coeff == p.manager().max_value()) {
                v = p.manager().mk_var(p.var());
                return p;
            }
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
     * Test simple subsumption between inequalities over equal polynomials (up to the constant term),
     * i.e., subsumption between literals of the form:
     *
     *      p + n_1 <= n_2
     *      n_3 <= p + n_4
     *      p + n_5 <= p + n_6
     *
     * (p polynomial, n_i constant numbers)
     *
     * A literal C subsumes literal D if the forbidden interval of C is a subset of the forbidden interval of D.
     * C subsumes D  <==  fi(C) subset fi(D)
     */
    bool simplify_clause::try_equal_body_subsumptions(clause& cl) {
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
