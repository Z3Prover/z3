/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_tactic_select.h

Abstract:

    Tactic that selects SMT backend.

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-14


--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_smt_tactic_select(ast_manager & m, params_ref const & p);

