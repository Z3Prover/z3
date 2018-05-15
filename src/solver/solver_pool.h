/**
Copyright (c) 2017 Microsoft Corporation

Module Name:

    solver_pool.h

Abstract:

   Maintain a pool of solvers

Author:

    Nikolaj Bjorner
    Arie Gurfinkel

Notes:

    This is a revision of spacer_virtual_solver by Arie Gurfinkel


it is not quite the same + there are good reasons to do that management at a higher level.
not the same == in spacer, there is an upper bound on the number of base solvers (i.e., number of pools). 
Then the pools are distributed between different predicate transformers. I can't just switch to solver_pool, 
since this, in most configuration, will result in either few solvers (which is bad for most of my benchmarks), 
or one solver per predicate transformer (which is bad for a few benchmarks with many predicates).
 

--*/
#ifndef SOLVER_POOL_H_
#define SOLVER_POOL_H_

#include "solver/solver.h"
#include "solver/solver_na2as.h"
#include "util/stopwatch.h"

class pool_solver;

class solver_pool {

    friend class pool_solver;
    
    struct stats {
        unsigned m_num_checks;
        unsigned m_num_sat_checks;
        unsigned m_num_undef_checks;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };

    ref<solver>         m_base_solver;
    sref_vector<solver> m_solvers;
    stats               m_stats;

    stopwatch m_check_watch;
    stopwatch m_check_sat_watch;
    stopwatch m_check_undef_watch;
    stopwatch m_proof_watch;

    void refresh(solver* s);

    ptr_vector<solver> get_base_solvers() const;
  
public:
    solver_pool(solver* base_solver);

    void collect_statistics(statistics &st) const;
    void reset_statistics();

    // create a fresh pool solver
    solver* mk_solver();

    // clone an existing pool solver
    solver* clone_solver(solver* pool_solver);

    void reset_solver(solver* s);
};


#endif
