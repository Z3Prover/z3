/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    bvsls_opt_solver.h

Abstract:

    Uses the bvsls engine for optimization

Author:

    Christoph (cwinter) 2014-3-28

Notes:

--*/
#ifndef _BVSLS_OPT_SOLVER_H_
#define _BVSLS_OPT_SOLVER_H_

#include "bvsls_opt_engine.h"
#include "opt_solver.h"

namespace opt {

    class bvsls_opt_solver : public opt_solver {
        ast_manager       & m_manager;
        params_ref  const & m_params;
        bvsls_opt_engine    m_engine;

    public:
        bvsls_opt_solver(ast_manager & m, params_ref const & p);
        virtual ~bvsls_opt_solver();

        virtual void updt_params(params_ref & p);
        virtual void collect_param_descrs(param_descrs & r);
        virtual void collect_statistics(statistics & st) const;
        virtual void assert_expr(expr * t);
        virtual void push_core();
        virtual void pop_core(unsigned n);
        virtual lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions);
        virtual void get_unsat_core(ptr_vector<expr> & r);
        virtual void get_model(model_ref & m);
        virtual proof * get_proof();
        virtual std::string reason_unknown() const;
        virtual void get_labels(svector<symbol> & r);
        virtual void set_cancel(bool f);
        virtual void set_progress_callback(progress_callback * callback);
        virtual unsigned get_num_assertions() const;
        virtual expr * get_assertion(unsigned idx) const;
        virtual void display(std::ostream & out) const;
    };

}

#endif