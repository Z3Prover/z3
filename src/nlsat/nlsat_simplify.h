#pragma once

#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_clause.h"

namespace nlsat {
    class simplify {
        struct imp;
        imp * m_imp;
    public:
        simplify(solver& s, atom_vector& atoms, clause_vector& clauses, pmanager& pm);
        ~simplify();

        bool operator()();
    };
}