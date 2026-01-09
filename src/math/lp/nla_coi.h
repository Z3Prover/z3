
/*++
  Copyright (c) 2025 Microsoft Corporation

  Abstract:
    Class for computing the cone of influence for NL constraints.
    It includes variables that come from monomials that have incorrect evaluation and
    transitively all constraints and variables that are connected.

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)
  --*/

#pragma once

namespace nla {

    class core;

    class coi {
        core& c;
        indexed_uint_set m_mon_set, m_constraint_set;
        indexed_uint_set m_term_set, m_var_set;

        struct occurs {
            unsigned_vector constraints;
            unsigned_vector monics;
            unsigned_vector terms;
        };

    public:
        coi(core& c) : c(c) {}

        void init();        

        indexed_uint_set const& mons() const { return m_mon_set; }
        indexed_uint_set const& constraints() const { return m_constraint_set; }
        indexed_uint_set& terms() { return m_term_set; }
        indexed_uint_set const &vars() { return m_var_set; }

    };
}