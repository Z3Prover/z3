/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    aig_tactic.h

Abstract:

    Tactic for minimizing circuits using AIGs.

Author:

    Leonardo (leonardo) 2011-10-24

Notes:

--*/
#pragma once

#include "util/params.h"
class tactic;

tactic * mk_aig_tactic(params_ref const & p = params_ref());
/*
  ADD_TACTIC("aig", "simplify Boolean structure using AIGs.", "mk_aig_tactic()")
*/
