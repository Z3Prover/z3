/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/conflict_core.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"
#include <algorithm>

namespace polysat {

    std::ostream& conflict_core::display(std::ostream& out) const {
        bool first = true;
        for (auto c : m_constraints) {
            if (first)
                first = false;
            else
                out << "  ;  ";
            out << c;
        }
        if (m_needs_model)
            out << "  ;  + current model";
        return out;
    }

    void conflict_core::set(std::nullptr_t) {
        SASSERT(empty());
        m_constraints.push_back({});
        m_needs_model = false;
    }

    void conflict_core::set(signed_constraint c) {
        LOG("Conflict: " << c);
        SASSERT(empty());
        m_constraints.push_back(std::move(c));
        m_needs_model = true;
    }

    void conflict_core::set(pvar v) {
        LOG("Conflict: v" << v);
        SASSERT(empty());
        m_conflict_var = v;
        m_needs_model = true;
    }

    void conflict_core::push(signed_constraint c) {
        SASSERT(!empty());  // should use set() to enter conflict state
        m_constraints.push_back(c);
    }

    void conflict_core::resolve(constraint_manager const& m, sat::bool_var var, clause const& cl) {
        // Note: core: x, y, z; corresponds to clause ~x \/ ~y \/ ~z
        //       clause: x \/ u \/ v
        //       resolvent: ~y \/ ~z \/ u \/ v; as core: y, z, ~u, ~v

        SASSERT(var != sat::null_bool_var);
        DEBUG_CODE({
            bool core_has_pos = std::count_if(begin(), end(), [var](auto c){ return c.blit() == sat::literal(var); }) > 0;
            bool core_has_neg = std::count_if(begin(), end(), [var](auto c){ return c.blit() == ~sat::literal(var); }) > 0;
            bool clause_has_pos = std::count(cl.begin(), cl.end(), sat::literal(var)) > 0;
            bool clause_has_neg = std::count(cl.begin(), cl.end(), ~sat::literal(var)) > 0;
            SASSERT(!core_has_pos || !core_has_neg);  // otherwise core is tautology
            SASSERT(!clause_has_pos || !clause_has_neg);  // otherwise clause is tautology
            SASSERT((core_has_pos && clause_has_pos) || (core_has_neg && clause_has_neg));
        });

        int j = 0;
        for (auto c : m_constraints)
            if (c->bvar() == var)
                m_constraints[j++] = c;
        m_constraints.shrink(j);

        for (sat::literal lit : cl)
            if (lit.var() != var)
                m_constraints.push_back(m.lookup(~lit));
    }

}
