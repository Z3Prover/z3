/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    pdr_tactic.h

Abstract:

    PDR as a tactic to solve Horn clauses.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-16.

Revision History:

--*/
#ifndef _PDR_TACTIC_H_
#define _PDR_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_pdr_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("pdr", "apply pdr for horn clauses.", "mk_pdr_tactic(m, p)")
*/
#endif
