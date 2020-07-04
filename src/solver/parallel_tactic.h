/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    parallel_tactic.h

Abstract:

    Parallel tactic in the style of Treengeling.

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-9

Notes:
   
--*/
#pragma once

class tactic;
class solver;

tactic * mk_parallel_tactic(solver* s, params_ref const& p);

