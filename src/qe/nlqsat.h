/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    nlqsat.h

Abstract:

    Quantifier Satisfiability Solver for nlsat

Author:

    Nikolaj Bjorner (nbjorner) 2015-10-17

Revision History:


--*/

#pragma once

#include "tactic/tactic.h"


tactic * mk_nlqsat_tactic(ast_manager & m, params_ref const& p = params_ref());
tactic * mk_nlqe_tactic(ast_manager & m, params_ref const& p = params_ref());


/*
  ADD_TACTIC("nlqsat", "apply a NL-QSAT solver.", "mk_nlqsat_tactic(m, p)") 

*/

// TBD_TACTIC("nlqe", "apply a NL-QE solver.", "mk_nlqe_tactic(m, p)") 

