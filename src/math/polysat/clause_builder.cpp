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
        m_is_tautology = false;
        SASSERT(empty());
    }

    clause_ref clause_builder::build() {
        if (m_is_tautology) {
            reset();
            return nullptr;
        }
        std::sort(m_literals.data(), m_literals.data() + m_literals.size());
        sat::literal prev = sat::null_literal;
        unsigned j = 0;
        for (unsigned i = 0; i < m_literals.size(); ++i) {
            sat::literal lit = m_literals[i];
            if (prev == lit)
                continue;
            prev = lit;
            m_literals[j++] = lit;
        }
        m_literals.shrink(j);
        clause_ref cl = clause::from_literals(std::move(m_literals));
        SASSERT(empty());
        return cl;
    }


    void clause_builder::push(sat::literal lit) {
        push(m_solver->m_constraints.lookup(lit));
    }

    void clause_builder::push(signed_constraint c) {
        SASSERT(c);
        if (c.is_always_false())  // filter out trivial constraints such as "4 < 2"
            return;
        if (c.is_always_true()) {
            m_is_tautology = true;
            return;
        }
#if 0
        if (c->unit_clause()) {
            return;
        }       
#endif
        m_literals.push_back(c.blit());
    }
}
