/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_tactic.h

Author:

    Christoph (cwinter) 2012-02-09

Tactic Documentation:

## Tactic fpa2bv

### Short Description
Converts floating points to bit-vector representation.

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_fpa2bv_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("fpa2bv", "convert floating point numbers to bit-vectors.", "mk_fpa2bv_tactic(m, p)")
*/

