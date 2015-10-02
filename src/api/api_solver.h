/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_solver.h

Abstract:
    New solver API

Author:

    Leonardo de Moura (leonardo) 2012-03-07.

Revision History:

--*/
#ifndef API_SOLVER_H_
#define API_SOLVER_H_

#include"api_util.h"
#include"solver.h"

struct Z3_solver_ref : public api::object {
    scoped_ptr<solver_factory> m_solver_factory;
    ref<solver>                m_solver;
    params_ref                 m_params;
    symbol                     m_logic;
    Z3_solver_ref(solver_factory * f):m_solver_factory(f), m_solver(0), m_logic(symbol::null) {}
    virtual ~Z3_solver_ref() {}
};

inline Z3_solver_ref * to_solver(Z3_solver s) { return reinterpret_cast<Z3_solver_ref *>(s); }
inline Z3_solver of_solver(Z3_solver_ref * s) { return reinterpret_cast<Z3_solver>(s); }
inline solver * to_solver_ref(Z3_solver s) { return to_solver(s)->m_solver.get(); }

#endif
