/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qflia_tactic.h

Abstract:

    Tactic for QF_LRA

Author:

    Leonardo (leonardo) 2012-02-26

Notes:

--*/
#ifndef _QFLIA_TACTIC_
#define _QFLIA_TACTIC_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_qflia_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("qflia", "builtin strategy for solving QF_LIA problems.", "mk_qflia_tactic(m, p)")
*/


probe * mk_is_quasi_pb_probe();

/*
  ADD_PROBE("is-quasi-pb", "true if the goal is quasi-pb.", "mk_is_quasi_pb_probe()")
*/

#endif
