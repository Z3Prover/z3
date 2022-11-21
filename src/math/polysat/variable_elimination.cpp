/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat variable elimination

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#include "math/polysat/variable_elimination.h"
#include "math/polysat/conflict.h"
#include "math/polysat/clause_builder.h"
#include "math/polysat/solver.h"
#include <algorithm>

namespace polysat {

    void free_variable_elimination::find_lemma(conflict& core) {
        LOG_H1("Free Variable Elimination");
        LOG("core: " << core);
        LOG("Free variables: " << s.m_free_pvars);
        for (pvar v : core.vars_occurring_in_constraints())
            if (!s.is_assigned(v))  // TODO: too restrictive. should also consider variables that will be unassigned only after backjumping (can update this after assignment handling in search state is refactored.)
                find_lemma(v, core);
    }

    void free_variable_elimination::find_lemma(pvar v, conflict& core) {
        LOG_H2("Free Variable Elimination for v" << v);
        // find constraint that allows computing v from other variables
        // (currently, consider only equations that contain v with degree 1)
        for (signed_constraint c : core) {
            if (!c.is_eq())
                continue;
            if (c.eq().degree(v) != 1)
                continue;
            find_lemma(v, c, core);
        }
    }

    void free_variable_elimination::find_lemma(pvar v, signed_constraint c, conflict& core) {
        LOG_H3("Free Variable Elimination for v" << v << " using equation " << c);
        pdd const& p = c.eq();
        SASSERT_EQ(p.degree(v), 1);
        auto& m = p.manager();
        pdd lc = m.zero();
        pdd rest = m.zero();
        p.factor(v, 1, lc, rest);
        if (rest.is_val())
            return;
        // lc * v + rest == p == 0
        // v == -1 * rest * lc^-1

        SASSERT(!lc.free_vars().contains(v));
        SASSERT(!rest.free_vars().contains(v));

        LOG("lc: " << lc);
        LOG("rest: " << rest);

        substitution sub(m);
        pdd const lcs = eval(lc, core, sub);
        LOG("lcs: " << lcs);
        pdd lci = m.zero();
        if (!inv(lcs, lci))
            return;

        pdd const rs = sub.apply_to(rest);
        pdd const vs = -rs * lci;  // this is the polynomial that computes v
        LOG("vs: " << vs);
        SASSERT(!vs.free_vars().contains(v));

        // Find another constraint where we want to substitute v
        for (signed_constraint c_target : core) {
            if (c == c_target)
                continue;
            if (c_target.vars().size() <= 1)
                continue;
            if (!c_target.contains_var(v))
                continue;

            // TODO: helper method constraint::subst(pvar v, pdd const& p)
            //       (or rather, add it on constraint_manager since we need to allocate/dedup the new constraint)
            //  For now, just restrict to ule_constraint.
            if (!c_target->is_ule())
                continue;
            // TODO: maybe apply assignment a here as well
            pdd const lhs = c_target->to_ule().lhs().subst_pdd(v, vs);
            pdd const rhs = c_target->to_ule().rhs().subst_pdd(v, vs);
            signed_constraint c_new = s.ule(lhs, rhs);
            if (c_target.is_negative())
                c_new.negate();
            LOG("c_target: " << lit_pp(s, c_target));
            LOG("c_new:    " << lit_pp(s, c_new));

            // New constraint is already true (maybe we already derived it previously?)
            // TODO: It might make sense to keep different derivations of the same constraint.
            //       E.g., if the new clause could derive c_new at a lower decision level.
            if (c_new.bvalue(s) == l_true)
                continue;

            clause_builder cb(s);
            for (auto [w, wv] : sub)
                cb.insert(~s.eq(s.var(w), wv));
            cb.insert(~c);
            cb.insert(~c_target);
            cb.insert(c_new);
            core.add_lemma(cb.build());
        }
    }

    // Evaluate p under assignments in the core.
    pdd free_variable_elimination::eval(pdd const& p, conflict& core, substitution& out_sub) {
        // TODO: this should probably be a helper method on conflict.
        // TODO: recognize constraints of the form "v1 == 27" to be used in the assignment?
        //       (but maybe useful evaluations are always part of core.vars() anyway?)

        substitution& sub = out_sub;
        SASSERT(sub.empty());

        for (auto v : p.free_vars())
            if (core.contains_pvar(v))
                sub.add(v, s.get_value(v));

        pdd q = sub.apply_to(p);

        // TODO: like in the old conflict::minimize_vars, we can now try to remove unnecessary variables from a.

        return q;
    }

    // Compute the multiplicative inverse of p.
    bool free_variable_elimination::inv(pdd const& p, pdd& out_p_inv) {
        // TODO: in the non-val case, we could introduce an additional variable to represent the inverse
        //       (and a constraint p * p_inv == 1)
        if (!p.is_val())
            return false;
        rational iv;
        if (!p.val().mult_inverse(p.power_of_2(), iv))
            return false;
        out_p_inv = p.manager().mk_val(iv);
        return true;
    }

}
