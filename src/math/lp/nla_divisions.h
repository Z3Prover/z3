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
        vector<std::tuple<lpvar, lpvar, lpvar>> m_idivisions;
        vector<std::tuple<lpvar, lpvar, lpvar>> m_rdivisions;
    public:
        divisions(core& c):m_core(c) {}
        void add_idivision(lpvar r, lpvar x, lpvar y);
        void add_rdivision(lpvar r, lpvar x, lpvar y);
        void check(vector<lemma>&);
    };
}
