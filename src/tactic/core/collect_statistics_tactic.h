/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    collect_statistics_tactic.h

Abstract:

    A tactic for collection of various statistics. 

Author:

    Mikolas Janota (mikjan) 2016-06-03
    Christoph (cwinter) 2016-06-03

Notes:

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_collect_statistics_tactic(ast_manager & m, params_ref const & p = params_ref());
Z3_ADD_TACTIC(collect_statistics, "collect-statistics", "Collects various statistics.", mk_collect_statistics_tactic(m, p));


