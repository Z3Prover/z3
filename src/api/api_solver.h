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
#pragma once

#include "util/mutex.h"
#include "api/api_util.h"
#include "solver/solver.h"

struct solver2smt2_pp {
    ast_pp_util     m_pp_util;
    std::ofstream   m_out;
    expr_ref_vector m_tracked;
    unsigned_vector m_tracked_lim;

    solver2smt2_pp(ast_manager& m, const std::string& file);
    void assert_expr(expr* e);
    void assert_expr(expr* e, expr* t);
    void push();
    void pop(unsigned n);
    void reset();
    void check(unsigned n, expr* const* asms);
    void get_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& variables);

};

struct Z3_solver_ref : public api::object {
    scoped_ptr<solver_factory> m_solver_factory;
    ref<solver>                m_solver;
    params_ref                 m_params;
    symbol                     m_logic;
    scoped_ptr<solver2smt2_pp> m_pp;
    mutex                      m_mux;
    event_handler*             m_eh;

    Z3_solver_ref(api::context& c, solver_factory * f): 
        api::object(c), m_solver_factory(f), m_solver(nullptr), m_logic(symbol::null), m_eh(nullptr) {}
    ~Z3_solver_ref() override {}

    void assert_expr(expr* e);
    void assert_expr(expr* e, expr* t);
    void set_eh(event_handler* eh);
    void set_cancel();

};

inline Z3_solver_ref * to_solver(Z3_solver s) { return reinterpret_cast<Z3_solver_ref *>(s); }
inline Z3_solver of_solver(Z3_solver_ref * s) { return reinterpret_cast<Z3_solver>(s); }
inline solver * to_solver_ref(Z3_solver s) { return to_solver(s)->m_solver.get(); }

