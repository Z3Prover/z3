/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_local_search.cpp

Abstract:

    Local search dispatch for SMT

Author:

    Nikolaj Bjorner (nbjorner) 2023-02-07

--*/
#include "sat/sat_solver.h"
#include "sat/sat_ddfw.h"
#include "sat/smt/euf_solver.h"


namespace euf {
    
    lbool solver::local_search(bool_vector& phase) {
        scoped_limits scoped_rl(m.limit());
        sat::ddfw bool_search;
        bool_search.reinit(s(), phase);
        bool_search.updt_params(s().params());
        bool_search.set_seed(rand());
        scoped_rl.push_child(&(bool_search.rlimit()));

        for (auto* th : m_solvers)
            th->set_bool_search(&bool_search);

        bool_search.check(0, nullptr, nullptr);        

        auto const& mdl = bool_search.get_model();
        for (unsigned i = 0; i < mdl.size(); ++i)
            phase[i] = mdl[i] == l_true;     

        if (bool_search.unsat_set().empty()) {
            enable_trace("arith");
            enable_trace("sat");
            enable_trace("euf");
            TRACE("sat", s().display(tout));
        }

        return bool_search.unsat_set().empty() ? l_true : l_undef;
    }
}
