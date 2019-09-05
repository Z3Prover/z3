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
#include "math/lp/nex.h"
namespace nla {
class core;

class nla_grobner : common {
    lp::int_set m_rows;
    lp::int_set m_active_vars;
public:
    nla_grobner(core *core);
    void grobner_lemmas();
private:
    void find_rows();
    void prepare_rows_and_active_vars();
    void add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j,  std::queue<lpvar>& q);
}; // end of grobner
}
