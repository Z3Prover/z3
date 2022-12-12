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

    clause_ref clause::from_unit(signed_constraint c) {
        SASSERT(c->has_bvar());
        sat::literal_vector lits;
        lits.push_back(c.blit());
        return clause::from_literals(std::move(lits));
    }

    clause_ref clause::from_literals(sat::literal_vector literals) {
        return alloc(clause, std::move(literals));
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
        return out;
    }

}
