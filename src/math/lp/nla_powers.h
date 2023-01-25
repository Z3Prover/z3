/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

  nla_powers.h

Author:
  Lev Nachmanson (levnach)
  Nikolaj Bjorner (nbjorner)

Description:
  Refines bounds on powers.
  
--*/

#include "math/lp/nla_types.h"

namespace nla {
    
    class core;
    
    class powers {
        core& m_core;
    public:
        powers(core& c):m_core(c) {}
        lbool check(lpvar r, lpvar x, lpvar y, vector<lemma>&);
    };
}
