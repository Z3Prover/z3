/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    quasi_macros_tactic.h

Abstract:

    Quasi-Macros

Author:

    Christoph (cwinter) 2012-10-26

Notes:

--*/
#ifndef QUASI_MACROS_TACTIC_H_
#define QUASI_MACROS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_quasi_macros_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("quasi-macros",  "Identifies and applies quasi-macros.", "mk_quasi_macros_tactic(m, p)")
*/

#endif
