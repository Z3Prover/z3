/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation by polynomial superposition

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#include "math/polysat/superposition.h"
#include "math/polysat/log.h"
#include "math/polysat/solver.h"

namespace polysat {

    struct inference_sup : public inference {
        const char* name;
        pvar var;
        signed_constraint reduced;
        signed_constraint reducer;
        inference_sup(const char* name, pvar var, signed_constraint reduced, signed_constraint reducer) : name(name), var(var), reduced(reduced), reducer(reducer) {}
        std::ostream& display(std::ostream& out) const override {
            return out << "Superposition (" << name << "), reduced v" << var
                << " in " << reduced.blit() << ": " << reduced
                << " by " << reducer.blit() << ": " << reducer;
        }
    };

    signed_constraint ex_polynomial_superposition::resolve1(pvar v, signed_constraint c1, signed_constraint c2) {
        // c1 is true, c2 is false
        SASSERT(c1.is_currently_true(s));
        SASSERT(c2.is_currently_false(s));
        LOG_H3("Resolving upon v" << v);
        LOG("c1: " << lit_pp(s, c1));
        LOG("c2: " << lit_pp(s, c2));
        pdd a = c1.eq();
        pdd b = c2.eq();
        unsigned degree_a = a.degree();
        unsigned degree_b = b.degree();
        pdd r = a;
        if (!a.resolve(v, b, r) && !b.resolve(v, a, r))
            return {};
        unsigned degree_r = r.degree();
        if (degree_a < degree_r && degree_b < degree_r)
            return {};
        // Only keep result if the degree in c2 was reduced.
        // (this condition might be too strict, but we use it for now to prevent looping)
        if (b.degree(v) <= r.degree(v))
            return {};
        if (a.degree(v) <= r.degree(v))
            return {};
        signed_constraint c = s.eq(r);
        LOG("resolved: " << c << "        currently false? " << c.is_currently_false(s));
        if (!c.is_currently_false(s))
            return {};
        return c;
    }


    // c2 ... constraint that is currently false
    // Try to replace it with a new false constraint (derived from superposition with a true constraint)
    lbool ex_polynomial_superposition::find_replacement(signed_constraint c2, pvar v, conflict& core) {
        for (auto c1 : s.m_viable.get_constraints(v)) {
            if (!c1->contains_var(v))  // side conditions do not contain v; skip them here
                continue;
            if (!c1.is_eq())
                continue;
            SASSERT(c1.is_currently_true(s));
            SASSERT(c2.is_currently_false(s));
            SASSERT_EQ(c1.bvalue(s), l_true);
            SASSERT(c2.bvalue(s) != l_false);

            signed_constraint c = resolve1(v, c1, c2);
            if (!c)
                continue;
            SASSERT(c.is_currently_false(s));

            // char const* inf_name = "?";
            switch (c.bvalue(s)) {
            case l_false:
                core.add_lemma({c, ~c1, ~c2});
                // core.log_inference(inference_sup("l_false", v, c2, c1));
                return l_true;
            case l_undef:
                // inf_name = "l_undef";
                core.add_lemma({c, ~c1, ~c2});
                // core.log_inference(inference_sup("l_undef lemma", v, c2, c1));
                break;
            case l_true:
                break;
            default:
                UNREACHABLE();
                break;
            }
            // // c alone (+ variables) is now enough to represent the conflict.
            // core.log_inference(inference_sup(inf_name, v, c2, c1));
            return c->contains_var(v) ? l_undef : l_true;
        }
        return l_false;
    }

    // true = done, false = abort, undef = continue
    lbool ex_polynomial_superposition::try_explain1(pvar v, conflict& core) {
        for (auto c2 : core) {
            if (!c2.is_eq())
                continue;
            if (!c2->contains_var(v))
                continue;
            if (!c2.is_currently_false(s))
                continue;
            switch (find_replacement(c2, v, core)) {
            case l_undef:
                return l_undef;
            case l_true:
                return l_true;
            case l_false:
                continue;
            }
        }
        return l_false;
    }

#if 0
    void ex_polynomial_superposition::reduce_by(pvar v, conflict& core) {
        bool progress = true;
        while (progress) {
            progress = false;
            for (auto c : core) {
                if (!c->contains_var(v))
                    continue;
                if (!c.is_eq())
                    continue;
#if 0
                if (!c.is_currently_true(s))
                    continue;
#endif

                if (!reduce_by(v, c, core))
                    continue;
                progress = true;
                break;                
            }
        }
    }

    bool ex_polynomial_superposition::reduce_by(pvar v, signed_constraint eq, conflict& core) {
        pdd p = eq.eq();
        LOG("using v" << v << " " << eq);
        for (auto c : core) {
            if (c == eq)
                continue;
            if (!c->contains_var(v))
                continue;
            if (c.is_eq())
                continue;
            LOG("try-reduce: " << c << " " << c.is_currently_false(s));
            if (!c->is_ule())
                continue;
            auto const& lhs = c->to_ule().lhs();
            auto const& rhs = c->to_ule().rhs();
            auto a = lhs.reduce(v, p);
            auto b = rhs.reduce(v, p);
            LOG("try-reduce: " << c << " " << a << " " << b << " vs " << lhs << " " << rhs);
            if (a == lhs && b == rhs)
                continue;
            auto c2 = s.ule(a, b);
            if (!c.is_positive())
                c2 = ~c2;
            if (!c2.is_currently_false(s))
                continue;
            if (c2.is_always_false() || c2.bvalue(s) == l_false)
                return false;
            if (!c2->has_bvar() || l_undef == c2.bvalue(s)) {
                vector<signed_constraint> premises;
                premises.push_back(c);
                premises.push_back(eq);
                core.insert(c2, premises);  // TODO: insert but then we reset? ... (this call does not insert into the core)
            }
            //    core.keep(c2);  // adds propagation of c to the search stack
            core.reset();
            LOG_H3("Polynomial superposition " << eq << " " << c << " reduced to " << c2);
            if (c2.bvalue(s) == l_false) {
                // TODO this loops or crashes depending on whether we
                // return true or false.
                core.insert(eq);
                core.insert(c);
                core.insert(~c2);
                core.log_inference("superposition 4");
                return true;
            }
            core.set(c2);
            core.log_inference(inference_sup("5", v, c, eq));
            return true;
        }
        return false;
    }
#endif

    bool ex_polynomial_superposition::perform(pvar v, conflict& core) {
#if 0
        reduce_by(v, core);
#endif
        lbool result = l_undef;
        while (result == l_undef)
            result = try_explain1(v, core);
        return result == l_true;
    }

}
