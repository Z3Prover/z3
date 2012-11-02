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
#ifndef _API_SOLVER_H_
#define _API_SOLVER_H_

#include"api_util.h"
#include"solver.h"

struct Z3_solver_ref : public api::object {
    solver *   m_solver;
    params_ref m_params;
    bool       m_initialized;
    symbol     m_logic;
    Z3_solver_ref():m_solver(0), m_initialized(false), m_logic(symbol::null) {}
    Z3_solver_ref(symbol const & logic):m_solver(0), m_initialized(false), m_logic(logic) {}
    virtual ~Z3_solver_ref() { dealloc(m_solver); }
};

inline Z3_solver_ref * to_solver(Z3_solver s) { return reinterpret_cast<Z3_solver_ref *>(s); }
inline Z3_solver of_solver(Z3_solver_ref * s) { return reinterpret_cast<Z3_solver>(s); }
inline solver * to_solver_ref(Z3_solver s) { return to_solver(s)->m_solver; }

#endif
