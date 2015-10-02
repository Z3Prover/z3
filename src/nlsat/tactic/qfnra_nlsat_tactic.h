/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfnra_nlsat_tactic.h

Abstract:

    Tactic based on nlsat for solving QF_NRA problems

Author:

    Leonardo (leonardo) 2012-01-23

Notes:

--*/
#ifndef QFNRA_NLSAT_TACTIC_H_
#define QFNRA_NLSAT_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_qfnra_nlsat_tactic(ast_manager & m, params_ref const & p = params_ref());

MK_SIMPLE_TACTIC_FACTORY(qfnra_nlsat_fct, mk_qfnra_nlsat_tactic(m, p));

/*
  ADD_TACTIC("qfnra-nlsat", "builtin strategy for solving QF_NRA problems using only nlsat.", "mk_qfnra_nlsat_tactic(m, p)")
*/

#endif
