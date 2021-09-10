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
        m_solver(&s), m_dep(nullptr, s.m_dm)
    {}

    void clause_builder::reset() {
        m_literals.reset();
        m_level = 0;
        m_dep = nullptr;
        SASSERT(empty());
    }

    clause_ref clause_builder::build() {
        clause_ref cl = clause::from_literals(m_level, std::move(m_dep), std::move(m_literals));
        m_level = 0;
        SASSERT(empty());
        return cl;
    }

    void clause_builder::add_dependency(p_dependency* d) {
        m_dep = m_solver->m_dm.mk_join(m_dep, d);
    }

    void clause_builder::push(sat::literal lit) {
        push(m_solver->m_constraints.lookup(lit));
    }

    void clause_builder::push(signed_constraint c) {
        SASSERT(c);
        SASSERT(c->has_bvar());
        if (c->unit_clause()) {
            add_dependency(c->unit_dep());
            m_level = std::max(m_level, c->unit_clause()->level());
            return;
        }       
        m_literals.push_back(c.blit());
    }

}
