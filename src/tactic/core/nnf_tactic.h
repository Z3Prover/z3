/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    nnf_tactic.h

Abstract:

    NNF tactic

Author:

    Leonardo de Moura (leonardo) 2011-12-28.

Revision History:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_snf_tactic(ast_manager & m, params_ref const & p = params_ref());
tactic * mk_nnf_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("snf", "put goal in skolem normal form.", "mk_snf_tactic(m, p)")
  ADD_TACTIC("nnf", "put goal in negation normal form.", "mk_nnf_tactic(m, p)")
*/


