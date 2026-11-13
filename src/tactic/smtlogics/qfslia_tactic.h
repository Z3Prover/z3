/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    qfslia_tactic.h

Abstract:

    Tactic for QF_SLIA.

--*/
#pragma once

#include "tactic/probe.h"
#include "tactic/tactic.h"

tactic* mk_qfslia_tactic(ast_manager& m, params_ref const& p = params_ref());
probe* mk_is_qfslia_probe();

Z3_ADD_TACTIC(qfslia, "qfslia", "builtin strategy for solving QF_SLIA problems.", mk_qfslia_tactic(m, p));
Z3_ADD_PROBE(is_qfslia, "is-qfslia", "true if the goal contains strings and is in QF_SLIA.", mk_is_qfslia_probe());
