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
#ifndef PARALLEL_TACTIC_H_
#define PARALLEL_TACTIC_H_

class solver;
class tactic;

tactic * mk_parallel_tactic(ast_manager& m, params_ref const& p);

/*
    ADD_TACTIC("qffdp", "builtin strategy for solving QF_FD problems in parallel.", "mk_parallel_tactic(m, p)")
*/

#endif
