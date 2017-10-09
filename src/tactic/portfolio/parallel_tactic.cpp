/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    parallel_solver.cpp

Abstract:

    Parallel solver in the style of Treengeling.

    It assumes a solver that supports good lookaheads.
    

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-9

Notes:
   
--*/

#include "solver/solver.h"
#include "tactic/tactic.h"

class parallel_tactic : public tactic {
    ref<solver> m_solver;
public:
    parallel_tactic(solver* s) : m_solver(s) {}

    void operator ()(const goal_ref & g,goal_ref_buffer & result,model_converter_ref & mc,proof_converter_ref & pc,expr_dependency_ref & dep) {
        NOT_IMPLEMENTED_YET();
    }

    void cleanup() {
        NOT_IMPLEMENTED_YET();
    }

    tactic* translate(ast_manager& m) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }
};

tactic * mk_parallel_tactic(solver* s) {
    return alloc(parallel_tactic, s);
}

