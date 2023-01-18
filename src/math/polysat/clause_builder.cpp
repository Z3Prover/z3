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
        m_redundant = clause::redundant_default;
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
        SASSERT(cl);
        cl->set_redundant(m_redundant);
        m_redundant = clause::redundant_default;
        SASSERT(empty());
        return cl;
    }


    void clause_builder::insert(sat::literal lit) {
        insert(m_solver->lit2cnstr(lit));
    }

    // TODO: in the final version, we may also skip assumptions (and even literals propagated at the base level),
    //       provided we correctly track external dependencies/level for the clause.
    void clause_builder::insert(signed_constraint c) {
        SASSERT(c);
        if (c.is_always_false())  // filter out trivial constraints such as "4 < 2"
            return;
        if (c.is_always_true()) {
            IF_VERBOSE(10, verbose_stream() << "Clause is tautology because of " << lit_pp(s(), c) << "\n");
            m_is_tautology = true;
            return;
        }
        m_literals.push_back(c.blit());
    }

    void clause_builder::insert_eval(sat::literal lit) {
        insert_eval(m_solver->lit2cnstr(lit));
    }

    void clause_builder::insert_eval(signed_constraint c) {
        if (c.bvalue(*m_solver) == l_undef)
            m_solver->assign_eval(~c.blit());
        insert(c);
    }

    void clause_builder::insert_try_eval(sat::literal lit) {
        insert_eval(m_solver->lit2cnstr(lit));
    }

    void clause_builder::insert_try_eval(signed_constraint c) {
        if (c.bvalue(*m_solver) == l_undef && c.is_currently_false(*m_solver))
            m_solver->assign_eval(~c.blit());
        insert(c);
    }
}
