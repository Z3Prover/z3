/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qe_sat_tactic.h

Abstract:

    Procedure for quantifier satisfiability using quantifier elimination.

Author:

    Nikolaj Bjorner (nbjorner) 2012-02-24

Revision History:


--*/


#ifndef __QE_SAT_H__
#define __QE_SAT_H__

#include"tactic.h"

namespace qe {
        
    tactic * mk_sat_tactic(ast_manager& m, params_ref const& p = params_ref());
    
};
/*
  ADD_TACTIC("qe-sat", "check satisfiability of quantified formulas using quantifier elimination.", "qe::mk_sat_tactic(m, p)")
*/

#endif
