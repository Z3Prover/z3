/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

  nla_divisions.h

Author:
  Lev Nachmanson (levnach)
  Nikolaj Bjorner (nbjorner)

Description:
  Check division constraints.
  
--*/

#include "math/lp/nla_types.h"

namespace nla {
    
    class core;
    
    class divisions {
        core& m_core;
        vector<std::tuple<lpvar, lpvar, lpvar, lpvar>> m_idivisions;
        vector<std::tuple<lpvar, lpvar, lpvar, lpvar>> m_rdivisions;
        vector<std::tuple<lpvar, lpvar, lpvar, lpvar>> m_bounded_divisions;
        // mod divisions: (x, y, r) where r = mod(x, y), used by check_mod_mult
        vector<std::tuple<lpvar, lpvar, lpvar>> m_mod_divisions;

    public:
        divisions(core& c):m_core(c) {}
        void add_idivision(lpvar q, lpvar x, lpvar y, lpvar r);
        void add_rdivision(lpvar q, lpvar x, lpvar y, lpvar r);
        void add_bounded_division(lpvar q, lpvar x, lpvar y, lpvar r);
        void add_mod_division(lpvar x, lpvar y, lpvar r);
        void check();
        void check_bounded_divisions();
        void check_mod_mult();
    };
}
