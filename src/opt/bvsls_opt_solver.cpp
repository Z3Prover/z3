/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    bvsls_opt_solver.cpp

Abstract:

    Uses the bvsls engine for optimization

Author:

    Christoph (cwinter) 2014-3-28

Notes:

--*/

#include "bvsls_opt_solver.h"

namespace opt {

    bvsls_opt_solver::bvsls_opt_solver(ast_manager & m, params_ref const & p) :
        opt_solver(m, p, symbol("QF_BV")),
        m_manager(m),
        m_params(p),
        m_engine(m, p)
    {
    }

    bvsls_opt_solver::~bvsls_opt_solver()
    {        
    }

    void bvsls_opt_solver::updt_params(params_ref & p)
    {
        opt_solver::updt_params(p);
        m_engine.updt_params(p);
    }

    void bvsls_opt_solver::collect_param_descrs(param_descrs & r)
    {
        opt_solver::collect_param_descrs(r);
    }

    void bvsls_opt_solver::collect_statistics(statistics & st) const
    {
        opt_solver::collect_statistics(st);
    }

    void bvsls_opt_solver::assert_expr(expr * t) {
        m_engine.assert_expr(t);
    }

    void bvsls_opt_solver::push_core()
    {
        opt_solver::push_core();
    }

    void bvsls_opt_solver::pop_core(unsigned n)
    {   
        opt_solver::pop_core(n);
    }

    lbool bvsls_opt_solver::check_sat_core(unsigned num_assumptions, expr * const * assumptions)
    {
        SASSERT(num_assumptions == 0);
        SASSERT(assumptions == 0);        
        return m_engine();
    }

    void bvsls_opt_solver::get_unsat_core(ptr_vector<expr> & r)
    {
        NOT_IMPLEMENTED_YET();
    }

    void bvsls_opt_solver::get_model(model_ref & m)
    {
        NOT_IMPLEMENTED_YET();
    }

    proof * bvsls_opt_solver::get_proof()
    {
        NOT_IMPLEMENTED_YET();
    }

    std::string bvsls_opt_solver::reason_unknown() const
    {
        NOT_IMPLEMENTED_YET();
    }

    void bvsls_opt_solver::get_labels(svector<symbol> & r)
    {
        opt_solver::get_labels(r);
    }

    void bvsls_opt_solver::set_cancel(bool f)
    {
        opt_solver::set_cancel(f);
        m_engine.set_cancel(f);
    }

    void bvsls_opt_solver::set_progress_callback(progress_callback * callback)
    {
        opt_solver::set_progress_callback(callback);
    }

    unsigned bvsls_opt_solver::get_num_assertions() const
    {
        NOT_IMPLEMENTED_YET();
    }

    expr * bvsls_opt_solver::get_assertion(unsigned idx) const
    {
        NOT_IMPLEMENTED_YET();
    }

    void bvsls_opt_solver::display(std::ostream & out) const
    {
        NOT_IMPLEMENTED_YET();
    }
}