/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff2bv_tactic.h

Abstract:

    Tactic encoding prime-field goals as bounded modular bit-vector goals.

Author:

    Romain Soulat

--*/
#pragma once
#include "util/params.h"
class ast_manager;
class tactic;
class probe;
tactic *mk_ff2bv_tactic(ast_manager &m, params_ref const &p = params_ref());
probe *mk_has_ff_probe();
#include "tactic/tactic.h"
Z3_ADD_TACTIC(ff2bv, "ff2bv", "encode prime fields as bounded modular bit-vectors.", mk_ff2bv_tactic(m, p));
