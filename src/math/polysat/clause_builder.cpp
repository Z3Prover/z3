/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat clause builder

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/clause_builder.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    clause_builder::clause_builder(solver& s):
        m_solver(s), m_dep(nullptr, s.m_dm)
    {}

    void clause_builder::reset() {
        m_literals.reset();
        m_new_constraints.reset();
        m_level = 0;
        m_dep = nullptr;
        SASSERT(empty());
    }

    clause_ref clause_builder::build() {
        // TODO: here we could set all the levels of the new constraints. so we do not have to compute the max at every use site.
        clause_ref cl = clause::from_literals(m_level, std::move(m_dep), std::move(m_literals), std::move(m_new_constraints));
        m_level = 0;
        SASSERT(empty());
        return cl;
    }

    void clause_builder::add_dependency(p_dependency* d) {
        m_dep = m_solver.m_dm.mk_join(m_dep, d);
    }

    void clause_builder::push_literal(sat::literal lit) {
        constraint* c = m_solver.m_constraints.lookup(lit.var());
        SASSERT(c);
        if (c->unit_clause()) {
            add_dependency(c->unit_clause()->dep());
            return;
        }
        m_level = std::max(m_level, c->level());
        m_literals.push_back(lit);
    }

    void clause_builder::push_new_constraint(constraint_literal c) {
        // TODO: assert that constraint is new (not 'inserted' into manager yet)
        SASSERT(c);
        SASSERT(c->is_undef());
        tmp_assign _t(c.constraint(), c.literal());
        if (c->is_always_false())
            return;
        m_level = std::max(m_level, c->level());
        m_literals.push_back(c.literal());
        m_new_constraints.push_back(c.detach_constraint());
    }

}
