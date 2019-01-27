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

    This is a revision of spacer_virtual_solver 
    consolidated with spacer_smt_context_manager
    by Arie Gurfinkel
    Use this module as a replacement for spacer_smt_context_manager.

--*/
#ifndef SOLVER_POOL_H_
#define SOLVER_POOL_H_

#include "solver/solver.h"
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
    unsigned            m_num_pools;
    unsigned            m_current_pool;
    sref_vector<solver> m_solvers;
    stats               m_stats;

    stopwatch m_check_watch;
    stopwatch m_check_sat_watch;
    stopwatch m_check_undef_watch;
    stopwatch m_proof_watch;

    void refresh(solver* s);

    ptr_vector<solver> get_base_solvers() const;
  
public:
    solver_pool(solver* base_solver, unsigned num_pools);

    void collect_statistics(statistics &st) const;
    void reset_statistics();

    solver* mk_solver();

    void reset_solver(solver* s);
    void updt_params(const params_ref &p);

};


#endif
