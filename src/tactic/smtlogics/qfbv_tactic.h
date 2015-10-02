/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfbv_tactic.h

Abstract:

    Tactic for QF_BV based on bit-blasting

Author:

    Leonardo (leonardo) 2012-02-22

Notes:

--*/
#ifndef QFBV_TACTIC_H_
#define QFBV_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_qfbv_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("qfbv",  "builtin strategy for solving QF_BV problems.", "mk_qfbv_tactic(m, p)")
*/

tactic * mk_qfbv_preamble(ast_manager& m, params_ref const& p);

tactic * mk_qfbv_tactic(ast_manager & m, params_ref const & p, tactic* sat, tactic* smt);

#endif
