/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_tactic.h

Abstract:

    Tactic for using nonlinear procedure.

Author:

    Leonardo (leonardo) 2012-01-02

Notes:

--*/
#ifndef NLSAT_TACTIC_H_
#define NLSAT_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_nlsat_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC('nlsat', '(try to) solve goal using a nonlinear arithmetic solver.', 'mk_nlsat_tactic(m, p)')
*/

#endif
