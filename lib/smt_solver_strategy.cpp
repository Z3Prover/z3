/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_solver_strategy.cpp

Abstract:

    Strategy for using the SMT solver.
    
Author:

    Leonardo (leonardo) 2011-06-25

Notes:

--*/
#include"smt_solver_strategy.h"
#include"smt_solver_exp.h"

smt_solver_strategy::smt_solver_strategy(ast_manager & _m, params_ref const & p):
    m(_m),
    m_params(p) {
}

smt_solver_strategy::~smt_solver_strategy() {
}

void smt_solver_strategy::init_solver() {
    smt::solver_exp * new_solver = alloc(smt::solver_exp, m, m_params);
    #pragma omp critical (as_st_cancel)
    {
        m_solver = new_solver;
    }
}

void smt_solver_strategy::updt_params(params_ref const & p) {
    m_params = p;
}

void smt_solver_strategy::get_param_descrs(param_descrs & r) {
    // TODO
}

void smt_solver_strategy::operator()(assertion_set & s, model_converter_ref & mc) {
    if (s.m().proofs_enabled())
        throw smt_solver_exception("smt quick solver does not support proof generation");
    mc = 0;
    s.elim_redundancies();
    if (s.inconsistent())
        return;

    init_solver();
    m_solver->assert_set(s);
    s.reset();
    
    lbool r = m_solver->check();
    m_solver->collect_statistics(m_stats);

    if (r == l_false) {
        s.assert_expr(m.mk_false());
    }
    else if (r == l_true) {
        model_ref md;
        m_solver->get_model(md);
        mc = model2model_converter(md.get());
    }
    else {
        // recover simplified assertion set
        m_solver->get_assertions(s);
        m_solver->get_model_converter(mc);
    }
}

void smt_solver_strategy::cleanup() {
    if (m_solver)
        m_solver->collect_statistics(m_stats);
    #pragma omp critical (as_st_cancel)
    {
        m_solver = 0;
    }
}

void smt_solver_strategy::set_cancel(bool f) {
    if (m_solver)
        m_solver->set_cancel(f);
}

void smt_solver_strategy::reset_statistics() {
    m_stats.reset();
}

void smt_solver_strategy::collect_statistics(statistics & st) const {
    st.copy(m_stats);
}
