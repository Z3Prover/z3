/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    reduce_invertible_tactic.h

Abstract:

    Reduce invertible variables.

Author:

    Nuno Lopes (nlopes)         2018-6-30
    Nikolaj Bjorner (nbjorner)

Notes:

--*/

#pragma once
#include "util/params.h"

class tactic;
class ast_manager;

tactic * mk_reduce_invertible_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("reduce-invertible", "reduce invertible variable occurrences.", "mk_reduce_invertible_tactic(m, p)")
*/

