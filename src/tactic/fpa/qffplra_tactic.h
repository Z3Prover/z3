#pragma once
/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qffplra_tactic.h

Abstract:

    Tactic for QF_FPLRA benchmarks.

Author:

    Christoph (cwinter) 2018-04-24


## Tactic qffplra


--*/
#pragma once

#include "util/params.h"
#include "tactic/probe.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_qffplra_tactic(ast_manager & m, params_ref const & p = params_ref());
Z3_ADD_TACTIC(qffplra, "qffplra", "(try to) solve goal using the tactic for QF_FPLRA.", mk_qffplra_tactic(m, p));

probe * mk_is_qffplra_probe();
Z3_ADD_PROBE(is_qffplra, "is-qffplra", "true if the goal is in QF_FPLRA.", mk_is_qffplra_probe());

