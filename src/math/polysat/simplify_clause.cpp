/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Clause Simplification

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2022-08-22

Notes:

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


    TODO: from bench1:
        Lemma: 12 \/ -26 \/ 292 \/ 294 \/ 295
             12: v11 <= v10 + v0                 [ l_false assert@0 pwatched active ]
            -26: v12 + -1*v11 != 0               [ l_false assert@0 pwatched active ]
            292: v10 + v0 + 1 == 0               [ l_false eval@6 pwatched active ]
            294: v12 + -1*v10 + -1*v0 + -1 == 0  [ l_undef ]
            295: v10 + v0 + 1 <= v12             [ l_undef ]

        292: v10 + v0 + 1 == 0
        294: v10 + v0 + 1 == v12
        295: v10 + v0 + 1 <= v12

        ==> drop 294 because it implies 295
        ==> drop 292 because it implies 295

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

    // If x != k appears among the new literals, all others are superfluous.
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
        entry.subsuming = false;
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
     * A literal C subsumes literal D (i.e, C ==> D),
     * if the forbidden interval of C is a superset of the forbidden interval of D.
     * fi(D) subset fi(C)  ==>  C subsumes D
     * If C subsumes D, remove C from the lemma.
     */
    bool simplify_clause::try_equal_body_subsumptions(clause& cl) {
        LOG_H2("Equal-body-subsumption for: " << cl);

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
            if (e.subsuming || !e.valid)
                continue;
            for (unsigned j = 0; j < cl.size(); ++j) {
                subs_entry& f = m_entries[j];
                if (f.subsuming || !f.valid || i == j || *e.var != *f.var)
                    continue;
                if (e.interval.currently_contains(f.interval)) {
                    // f subset of e  ==>  f.src subsumed by e.src
                    LOG("Removing " << s.lit2cnstr(cl[i]) << " because it subsumes " << s.lit2cnstr(cl[j]));
                    e.subsuming = true;
                    any_subsumed = true;
                    break;
                }
            }
        }
        // Remove subsuming literals
        if (!any_subsumed)
            return false;
        unsigned j = 0;
        for (unsigned i = 0; i < cl.size(); ++i)
            if (!m_entries[i].subsuming)
                cl[j++] = cl[i];
        cl.m_literals.shrink(j);
        return true;
    }




#if 0
    // All variables of clause 'cl' except 'z' are assigned.
    // Goal: a possibly weaker clause that implies a restriction on z around z_val
    clause_ref simplify_clause::make_asserting(clause& cl, pvar z, rational z_val) {
        signed_constraints cz;  // constraints of 'cl' that contain 'z'
        sat::literal_vector lits;  // literals of the new clause
        for (sat::literal lit : cl) {
            signed_constraint c = s.lit2cnstr(lit);
            if (c.contains_var(z))
                cz.push_back(c);
            else
                lits.push_back(lit);
        }
        SASSERT(!cz.empty());
        if (cz.size() == 1) {
            // TODO: even in this case, if the constraint is non-linear in z, we might want to extract a maximal forbidden interval around z_val.
            return nullptr;
        }
        else {
            // multiple constraints that contain z
            find_implied_constraint(cz, z, z_val, lits);
            return clause::from_literals(std::move(lits));
        }
    }

    // Each constraint in 'cz' is univariate in 'z' under the current assignment.
    // Goal: a literal that is implied by the disjunction of cz and ensures z != z_val in viable.
    //       (plus side conditions that do not depend on z)
    void simplify_clause::find_implied_constraint(signed_constraints const& cz, pvar z, rational z_val, sat::literal_vector& out_lits)
    {
        unsigned const out_lits_original_size = out_lits.size();

        forbidden_intervals fi(s);
        fi_record entry;

        auto intersection = eval_interval::full();
        bool all_unit = true;

        for (signed_constraint const& c : cz) {
            if (fi.get_interval(c, z, entry) && entry.coeff == 1) {
                intersection = intersection.intersect(entry.interval);
                for (auto const& sc : entry.side_cond)
                    out_lits.push_back(sc.blit());
            } else {
                all_unit = false;
                break;
            }
        }

        if (all_unit) {
            SASSERT(!intersection.is_currently_empty());
            // Unit intervals from all constraints
            // => build constraint from intersection of forbidden intervals
            //    z \not\in [l;u[  <=>  z - l >= u - l
            if (intersection.is_proper()) {
                auto c_new = s.ule(intersection.hi() - intersection.lo(), z - intersection.lo());
                out_lits.push_back(c_new.blit());
            }
        } else {
            out_lits.shrink(out_lits_original_size);
            find_implied_constraint_sat(cz, z, z_val, out_lits);
        }
    }

    void simplify_clause::find_implied_constraint_sat(signed_constraints const& cz, pvar z, rational z_val, sat::literal_vector& out_lits)
    {
        unsigned bit_width = s.size(z);
        auto p_factory = mk_univariate_bitblast_factory();
        auto p_us = (*p_factory)(bit_width);
        auto& us = *p_us;

        // Find max z1 such that z1 < z_val and all cz true under z := z1 (and current assignment)
        rational z1 = z_val;

        for (signed_constraint const& c : cz)
            c.add_to_univariate_solver(s, us, 0);
        us.add_ult_const(z_val, false, 0);  // z1 < z_val

        // First check if any such z1 exists
        switch (us.check()) {
        case l_false:
            // No such z1 exists
            z1 = s.m_pdd[z]->max_value();  // -1
            break;
        case l_true:
            // z1 exists. Try to make it as small as possible by setting bits to 0

            for (unsigned j = bit_width; j-- > 0; ) {
                switch (us.check()) {
                case l_true:
                    // TODO
                    break;
                case l_false:
                    // TODO
                    break;
                default:
                    UNREACHABLE();  // TODO: see below
                }
            }

            break;
        default:
            UNREACHABLE();  // TODO: should we link the child solver's resources to polysat's resource counter?
        }

        // Find min z2 such that z2 > z_val and all cz true under z := z2 (and current assignment)
        // TODO
    }
#endif

}
