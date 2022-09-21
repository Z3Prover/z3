#if 0
/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation / resolution

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#include "math/polysat/explain.h"
#include "math/polysat/log.h"
#include "math/polysat/solver.h"

namespace polysat {

    struct post_propagate2 : public inference {
        const char* name;
        signed_constraint conclusion;
        signed_constraint premise1;
        signed_constraint premise2;
        post_propagate2(const char* name, signed_constraint conclusion, signed_constraint premise1, signed_constraint premise2)
            : name(name), conclusion(conclusion), premise1(premise1), premise2(premise2) {}
        std::ostream& display(std::ostream& out) const override {
            return out << "Post-propagate (by " << name << "), "
                << "conclusion " << conclusion.blit() << ": " << conclusion
                << " from " << premise1.blit() << ": " << premise1
                << " and " << premise2.blit() << ": " << premise2;
        }
    };

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
        LOG("c1: " << c1);
        LOG("c2: " << c2);
        pdd a = c1.eq();
        pdd b = c2.eq();
        pdd r = a;
        if (!a.resolve(v, b, r) && !b.resolve(v, a, r))
            return {};
        // Only keep result if the degree in c2 was reduced.
        // (this condition might be too strict, but we use it for now to prevent looping)
        if (b.degree(v) <= r.degree(v))
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
        vector<signed_constraint> premises;

        for (auto si : s.m_search) {
            if (!si.is_boolean())
                continue;
            if (si.is_resolved())
                continue;
            auto c1 = s.lit2cnstr(si.lit());       
            if (!c1->contains_var(v))
                continue;
            if (!c1.is_eq())
                continue;
            if (!c1.is_currently_true(s))
                continue;
            signed_constraint c = resolve1(v, c1, c2);
            if (!c)
                continue;

            char const* inf_name = "?";
            switch (c.bvalue(s)) {
            case l_false:
                // new conflict state based on propagation and theory conflict
                core.reset();
                core.insert(c1);
                core.insert(c2);
                core.insert(~c);
                core.log_inference(inference_sup("1", v, c2, c1));
                return l_true;
            case l_undef:
#if 0
                core.reset();
                core.insert(c1);
                core.insert(c2);
                core.insert(~c);
                core.log_inference(inference_sup("1b", v, c2, c1));
                return l_true;
#else
                SASSERT(premises.empty());
                // Ensure that c is assigned and justified                    
                premises.push_back(c1);
                premises.push_back(c2);
                // var dependency on c is lost
                // c evaluates to false, when the clause ~c1 or ~c2 or c
                // gets created, c is assigned to false by evaluation propagation
                // It should have been assigned true by unit propagation.
                core.replace(c2, c, premises);
                core.log_inference(post_propagate2("superposition", c, c2, c1));
                inf_name = "2";
                SASSERT_EQ(l_true, c.bvalue(s));
                SASSERT(c.is_currently_false(s));
                break;
#endif
            default:
                break;
            }

            // NOTE: more variables than just 'v' might have been removed here (see polysat::test_p3).
            // c alone (+ variables) is now enough to represent the conflict.
            core.reset();
            core.set(c);
            core.log_inference(inference_sup(inf_name, v, c2, c1));
            return c->contains_var(v) ? l_undef : l_true;
        }
        return l_false;
    }

    // TODO(later): check superposition into disequality again (see notes)
    // true = done, false = abort, undef = continue
    // TODO: can try multiple replacements at once; then the c2 loop needs to be done only once... (requires some reorganization for storing the premises)
    lbool ex_polynomial_superposition::try_explain1(pvar v, conflict& core) {
        for (auto c2 : core) {
            if (!c2->contains_var(v))
                continue;
            if (!c2.is_eq())
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

    bool ex_polynomial_superposition::try_explain(pvar v, conflict& core) {
        reduce_by(v, core);
        lbool result = l_undef;
        while (result == l_undef)
            result = try_explain1(v, core);
        return result == l_true;
    }

}
#endif
