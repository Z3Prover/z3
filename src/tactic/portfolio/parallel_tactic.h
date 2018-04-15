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
class solver;

tactic * mk_parallel_tactic(solver* s, params_ref const& p);
tactic * mk_parallel_qffd_tactic(ast_manager& m, params_ref const& p);
tactic * mk_parallel_smt_tactic(ast_manager& m, params_ref const& p);

// create parallel sat/smt tactics if parallel.enable=true, otherwise return sequential versions.
tactic * mk_psat_tactic(ast_manager& m, params_ref const& p);
tactic * mk_psmt_tactic(ast_manager& m, params_ref const& p, symbol const& logic = symbol::null);
tactic * mk_psmt_tactic_using(ast_manager& m, bool auto_config, params_ref const& p, symbol const& logic = symbol::null);

/*
    ADD_TACTIC("pqffd", "builtin strategy for solving QF_FD problems in parallel.", "mk_parallel_qffd_tactic(m, p)")
    ADD_TACTIC("psmt", "builtin strategy for SMT tactic in parallel.", "mk_parallel_smt_tactic(m, p)")
*/

#endif
