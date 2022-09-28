/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Clause Simplification

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2022-08-22

Notes:

    TODO: check why it fails with test_l2   (mod 2^2)
        Lemma: -0 \/ -1 \/ -6 \/ 8
             -0: v1 + 2*v0 + 1 != 0              [ l_false assert@0 pwatched ]
             -1: 2*v1 + v0 != 0                  [ l_false assert@0 pwatched ]
             -6: v1 + -1 != 0                    [ l_undef ]
              8: 1 <= 2*v1 + 2                   [ l_undef ]

        -6  ==>  v1 \not\in { 1 }
        8   ==>  v1 \not\in { 1, 3 }
        so 8 subsumes -6   (8 ==> -6)
        Actually:
            - this means we have to keep -6 and throw out 8.
            - because in case of v1 := 3, the original lemma will be satisfied.
            TODO: meaning of "subsumption" is probably flipped in the code below?

    TODO: from test_l5, conflict #2:   (mod 2^3)
        Lemma: -1 \/ -2 \/ -6 \/ -7
           -1: 2*v1 + v0 + 4 != 0   [ bvalue=l_false @0 pwatched=1  ]
           -2: 4*v1 + v0 + 4 != 0   [ bvalue=l_false @0 pwatched=1  ]
           -6: 2*v1 + -2 != 0       [ bvalue=l_undef pwatched=0  ]
           -7: v1 + -1 != 0         [ bvalue=l_undef pwatched=0  ]

            -7  ==>  v1 \not\in { 1 }
            -6  ==>  v1 \not\in { 1, 5 }
            ==> -6 subsumes -7

    TODO: from test_ineq_basic5:    (mod 2^4)
        Lemma: -0 \/ -1 \/ 2 \/ 3
           -0: -4 > v1 + v0         [ bvalue=l_false @0 pwatched=1  ]
           -1: v1 > 2               [ bvalue=l_false @0 pwatched=1  ]
            2: -3 <= -1*v0 + -7     [ bvalue=l_undef pwatched=0  ]
            3: -4 <= v0             [ bvalue=l_undef pwatched=0  ]

        2  ==>  v0 \not\in [0;12[
        3  ==>  v0 \not\in [13;10[
        A value is "truly" forbidden if neither branch works:
            v0 \not\in [0;12[ intersect [13;10[  ==  [0;10[
        ==> replace 2, 3 by single constraint 10 <= v0

--*/
#include "math/polysat/solver.h"
#include "math/polysat/simplify_clause.h"

namespace polysat {

    simplify_clause::simplify_clause(solver& s):
        s(s)
    {}

    bool simplify_clause::apply(clause& cl) {
        if (try_recognize_bailout(cl))
            return true;
        if (try_equal_body_subsumptions(cl))
            return true;
        return false;
    }

    // If x != k appears among the new literals, all others are superfluous
    bool simplify_clause::try_recognize_bailout(clause& cl) {
        LOG_H2("Try to find bailout literal");
        pvar v = null_var;
        sat::literal eq = sat::null_literal;
        rational k;
        for (sat::literal lit : cl) {
            LOG_V("Examine " << lit_pp(s, lit));
            lbool status = s.m_bvars.value(lit);
            // skip premise literals
            if (status == l_false)
                continue;
            SASSERT(status != l_true);  // would be an invalid lemma
            SASSERT_EQ(status, l_undef);  // new literal
            auto c = s.lit2cnstr(lit);
            // For now we only handle the case where exactly one variable is
            // unassigned among the new constraints
            for (pvar w : c->vars()) {
                if (s.is_assigned(w))
                    continue;
                if (v == null_var)
                    v = w;
                else if (v != w)
                    return false;
            }
            SASSERT(v != null_var);  // constraints without unassigned variables would be evaluated at this point
            if (c.is_diseq() && c.diseq().is_unilinear()) {
                pdd const& p = c.diseq();
                if (p.hi().is_one()) {
                    eq = lit;
                    k = (-p.lo()).val();
                }
            }
        }
        if (eq == sat::null_literal)
            return false;
        LOG("Found bailout literal: " << lit_pp(s, eq));
        // Keep all premise literals and the equation
        unsigned j = 0;
        for (unsigned i = 0; i < cl.size(); ++i) {
            sat::literal const lit = cl[i];
            lbool const status = s.m_bvars.value(lit);
            if (status == l_false || lit == eq)
                cl[j++] = cl[i];
            else {
                DEBUG_CODE({
                    auto a = s.assignment();
                    a.push_back({v, k});
                    SASSERT(s.lit2cnstr(lit).is_currently_false(s, a));
                });
            }
        }
        cl.m_literals.shrink(j);
        return true;
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
