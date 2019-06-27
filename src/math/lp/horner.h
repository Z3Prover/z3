/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#pragma once

#include "math/lp/nla_common.h"

namespace nla {
class core;


class horner : common {   
public:
    horner(core *core);
    void horner_lemmas();
    void lemma_on_row(const lp::row_strip<rational>&);
private:    
}; // end of horner
}
