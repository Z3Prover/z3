/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    bvsls_opt_engine.cpp

Abstract:

    Optimization extensions to bvsls

Author:

    Christoph (cwinter) 2014-03-28

Notes:

--*/
#include "bvsls_opt_engine.h"

bvsls_opt_engine::bvsls_opt_engine(ast_manager & m, params_ref const & p) :
    sls_engine(m, p)
{
}

bvsls_opt_engine::~bvsls_opt_engine()
{    
}

bvsls_opt_engine::optimization_result bvsls_opt_engine::optimize(expr_ref const & objective)
{
    SASSERT(m_bv_util.is_bv(objective));
    m_tracker.initialize(m_assertions);
    m_restart_limit = _RESTART_LIMIT_;

    optimization_result res(m_manager);

    do {
        checkpoint();

        IF_VERBOSE(1, verbose_stream() << "Optimizing... restarts left:" << (m_max_restarts - m_stats.m_restarts) << std::endl; );
        res.is_sat = search();

        if (res.is_sat == l_undef)
        {
#if _RESTART_INIT_
            m_tracker.randomize();
#else
            m_tracker.reset(m_assertions);
#endif
        }
    } while (m_stats.m_stopwatch.get_current_seconds() < _TIMELIMIT_ &&
             res.is_sat != l_true && m_stats.m_restarts++ < m_max_restarts);    

    if (res.is_sat)
        res.optimum = maximize(objective);

    return res;
}

expr_ref bvsls_opt_engine::maximize(expr_ref const & objective)
{
    expr_ref res(m_manager);
    res = m_bv_util.mk_numeral(0, m_bv_util.get_bv_size(objective));

    // TODO.

    return res;
}