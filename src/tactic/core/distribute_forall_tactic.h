/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    distribute_forall_tactic.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2012-02-18.

--*/
#ifndef DISTRIBUTE_FORALL_TACTIC_H_
#define DISTRIBUTE_FORALL_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_distribute_forall_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("distribute-forall", "distribute forall over conjunctions.", "mk_distribute_forall_tactic(m, p)")
*/

#endif
