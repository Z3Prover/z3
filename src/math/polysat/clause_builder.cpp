/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat clause builder

Author:

    Jakob Rath 2021-04-6

--*/

#include "math/polysat/clause_builder.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    static_assert(!std::is_copy_assignable_v<clause_builder>);
    static_assert(!std::is_copy_constructible_v<clause_builder>);
    static_assert(std::is_move_assignable_v<clause_builder>);
    static_assert(std::is_move_constructible_v<clause_builder>);

    clause_builder::clause_builder(solver& s):
        m_solver(&s)
    {}

    void clause_builder::reset() {
        m_literals.reset();
        SASSERT(empty());
    }

    clause_ref clause_builder::build() {
        clause_ref cl = clause::from_literals(std::move(m_literals));
        SASSERT(empty());
        return cl;
    }


    void clause_builder::push(sat::literal lit) {
        push(m_solver->m_constraints.lookup(lit));
    }

    void clause_builder::push(signed_constraint c) {
        SASSERT(c);
        SASSERT(c->has_bvar());
        SASSERT(!c.is_always_true());  // clause would be a tautology
        if (c->unit_clause()) {
            return;
        }       
        m_literals.push_back(c.blit());
    }

    void clause_builder::push_new(signed_constraint c) {
        if (c.is_always_false())  // filter out trivial constraints such as "4 < 2" (may come in from forbidden intervals)
            return;
        if (!c->has_bvar())
            m_solver->m_constraints.ensure_bvar(c.get());
        push(c);
    }
}
