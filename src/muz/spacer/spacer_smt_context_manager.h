/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_smt_context_manager.h

Abstract:

    Manager of smt contexts

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-26.
    Arie Gurfinkel
Revision History:

--*/

#ifndef _SPACER_SMT_CONTEXT_MANAGER_H_
#define _SPACER_SMT_CONTEXT_MANAGER_H_

#include "util/stopwatch.h"

#include "smt/smt_kernel.h"
#include "muz/base/dl_util.h"
#include "muz/spacer/spacer_virtual_solver.h"

namespace spacer {

class smt_context_manager {

    struct stats {
        unsigned m_num_smt_checks;
        unsigned m_num_sat_smt_checks;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };

    smt_params               m_fparams;
    ast_manager&             m;
    unsigned                 m_max_num_contexts;
    ptr_vector<virtual_solver_factory> m_solvers;
    unsigned                 m_num_contexts;


    stats     m_stats;
    stopwatch m_check_watch;
    stopwatch m_check_sat_watch;

public:
    smt_context_manager(ast_manager& m, unsigned max_num_contexts = 1,
                        const params_ref &p = params_ref::get_empty());

    ~smt_context_manager();
    virtual_solver* mk_fresh();

    void collect_statistics(statistics& st) const;
    void reset_statistics();

    void updt_params(params_ref const &p) { m_fparams.updt_params(p); }
    smt_params& fparams() {return m_fparams;}

};

};

#endif
