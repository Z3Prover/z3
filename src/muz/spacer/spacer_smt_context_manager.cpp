/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_smt_context_manager.cpp

Abstract:

    Manager of smt contexts

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-26.
    Arie Gurfinkel
Revision History:

--*/


#include "ast/ast_pp.h"
#include "ast/ast_pp_util.h"
#include "ast/ast_smt_pp.h"

#include "smt/smt_context.h"
#include "smt/params/smt_params.h"
#include "smt/smt_solver.h"

#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_smt_context_manager.h"
namespace spacer {

smt_context_manager::smt_context_manager(ast_manager &m,
        unsigned max_num_contexts,
        const params_ref &p) :
    m(m),
    m_params(p),
    m_max_num_contexts(max_num_contexts),
    m_num_contexts(0) { m_stats.reset();}


smt_context_manager::~smt_context_manager()
{
    std::for_each(m_solvers.begin(), m_solvers.end(),
                  delete_proc<spacer::virtual_solver_factory>());
    m_solvers.reset();
    m_base_solvers.reset();
}

void smt_context_manager::updt_params(params_ref const &p) {
    m_params.append(p);
    for (auto *s : m_base_solvers) {s->updt_params(m_params);}
}

virtual_solver* smt_context_manager::mk_fresh()
{
    ++m_num_contexts;
    virtual_solver_factory *solver_factory = nullptr;

    if (m_max_num_contexts == 0 || m_solvers.size() < m_max_num_contexts) {
        m_base_solvers.push_back(mk_smt_solver(m, m_params, symbol::null));
        m_solvers.push_back(alloc(spacer::virtual_solver_factory,
                                  *m_base_solvers.back()));
        solver_factory = m_solvers.back();
    }
    else {
        solver_factory = m_solvers[(m_num_contexts - 1) % m_max_num_contexts];
    }

    return solver_factory->mk_solver();
}

void smt_context_manager::collect_statistics(statistics& st) const
{
    for (unsigned i = 0; i < m_solvers.size(); ++i) {
        m_solvers[i]->collect_statistics(st);
    }
}

void smt_context_manager::reset_statistics()
{
    for (unsigned i = 0; i < m_solvers.size(); ++i) {
        m_solvers[i]->reset_statistics();
    }
}


};
