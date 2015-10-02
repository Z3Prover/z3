/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    vsubst_tactic.h

Abstract:

    Check satisfiability of QF_NRA problems using virtual subsititution quantifier-elimination.

Author:

    Nikolaj (nbjorner) 2011-05-16

Notes:


--*/
#ifndef VSUBST_TACTIC_H_
#define VSUBST_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_vsubst_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("vsubst", "checks satsifiability of quantifier-free non-linear constraints using virtual substitution.", "mk_vsubst_tactic(m, p)")
*/

#endif

