/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat clauses

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/clause.h"
#include "math/polysat/solver.h"

namespace polysat {

    clause_ref clause::from_unit(unsigned lvl, signed_constraint c, p_dependency_ref d) {
        SASSERT(c->has_bvar());
        sat::literal_vector lits;
        lits.push_back(c.blit());
        return clause::from_literals(lvl, std::move(d), std::move(lits));
    }

    clause_ref clause::from_literals(unsigned lvl, p_dependency_ref d, sat::literal_vector literals) {
        return alloc(clause, lvl, std::move(d), std::move(literals));
    }

    bool clause::is_always_false(solver& s) const {
        return std::all_of(m_literals.begin(), m_literals.end(), [&s](sat::literal lit) {
            signed_constraint c = s.m_constraints.lookup(lit);
            return c.is_always_false();
        });
    }

    bool clause::is_currently_false(solver& s) const {
        return std::all_of(m_literals.begin(), m_literals.end(), [&s](sat::literal lit) {
            signed_constraint c = s.m_constraints.lookup(lit);
            return c.is_currently_false(s);
        });
    }

    std::ostream& clause::display(std::ostream& out) const {
        bool first = true;
        for (auto lit : *this) {
            if (first)
                first = false;
            else
                out << " \\/ ";
            out << lit;
        }
        if (m_dep) {
            ptr_vector<p_dependency> todo;
            todo.push_back(m_dep.get());
            vector<unsigned, false> vs;
            poly_dep_manager::linearize_todo(todo, vs);
            out << " deps ...";
     //       out << "| " << vs;
        }
        return out;
    }

}
