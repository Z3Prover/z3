/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_solver

Abstract:

    Interface to Concurrent SLS solver
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-02-21

--*/

#include "sat/smt/sls_solver.h"
#include "sat/smt/euf_solver.h"
#include "ast/sls/bv_sls.h"


namespace sls {

    solver::solver(euf::solver& ctx):
        th_euf_solver(ctx, symbol("sls"), ctx.get_manager().mk_family_id("sls")) {}

    solver::~solver() {
        if (m_rlimit) {
            m_rlimit->cancel();
            m_thread.join();
        }
    }

    void solver::push_core() {
        if (s().scope_lvl() == s().search_lvl() + 1)
            init_local_search();
    }
    
    void solver::pop_core(unsigned n) {
        if (s().scope_lvl() - n <= s().search_lvl())
            sample_local_search();
    }

    void solver::simplify() {
    
    }
        

    void solver::init_local_search() {
        if (m_rlimit) {
            m_rlimit->cancel();
            m_thread.join();
        }
        // set up state for local search solver here
        auto* bvsls = alloc(bv::sls, m);
        // walk clauses, add them
        // walk trail stack until search level, add units
        // encapsulate bvsls within the arguments of run-local-search.
        // ensure bvsls does not touch ast-manager.
        m_thread = std::thread([this]() { run_local_search(*this); });
        m_rlimit = alloc(reslimit);
        m_rlimit->push_child(&s().rlimit());
    }

    void solver::sample_local_search() {
    
    }

    void solver::run_local_search(solver& s) {

    }

}
