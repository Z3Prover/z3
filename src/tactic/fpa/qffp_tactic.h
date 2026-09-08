/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qffp_tactic.h

Abstract:

    Tactic for QF_FP benchmarks.

Author:

    Christoph (cwinter) 2012-01-16

Tactic Documentation:

## Tactic qffp

### Short Description 
Tactic for QF_FP formulas

## Tactic qffpbv

### Short Description 
Tactic for QF_FPBV formulas

--*/
#pragma once

#include "util/params.h"
#include "tactic/probe.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_qffp_tactic(ast_manager & m, params_ref const & p = params_ref());
tactic * mk_qffpbv_tactic(ast_manager & m, params_ref const & p = params_ref());
Z3_ADD_TACTIC(qffp, "qffp", "(try to) solve goal using the tactic for QF_FP.", mk_qffp_tactic(m, p));
Z3_ADD_TACTIC(qffpbv, "qffpbv", "(try to) solve goal using the tactic for QF_FPBV (floats+bit-vectors).", mk_qffpbv_tactic(m, p));

probe * mk_is_qffp_probe();
probe * mk_is_qffpbv_probe();
Z3_ADD_PROBE(is_qffp, "is-qffp", "true if the goal is in QF_FP (floats).", mk_is_qffp_probe());
Z3_ADD_PROBE(is_qffpbv, "is-qffpbv", "true if the goal is in QF_FPBV (floats+bit-vectors).", mk_is_qffpbv_probe());

