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

#include "math/lp/horner.h"
#include "math/lp/nla_core.h"

namespace nla {

horner::horner(core * c) : common(c) {}

void horner::lemma_on_row(const lp::row_strip<rational>&) {}

void horner::horner_lemmas() {
    if (!c().m_settings.run_horner()) {
        TRACE("nla_solver", tout << "not generating horner lemmas\n";);
        return;
    }

    const auto& m = c().m_lar_solver.A_r();
    unsigned r = random();
    unsigned s = m.row_count();
    for (unsigned i = 0; i < s && !done(); i++) {
        lemma_on_row(m.m_rows[(i%s)]);
    }
    
    SASSERT(false);
}

}
