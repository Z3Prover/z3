/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_solver.h

Abstract:

    Wraps smt::kernel as a solver for the external API and cmd_context.

Author:

    Leonardo (leonardo) 2012-10-21

Notes:
   
    Variant of smt_solver that exposes kernel object.
--*/
#ifndef _OPT_SOLVER_H_
#define _OPT_SOLVER_H_

#include"ast.h"
#include"params.h"
#include"solver_na2as.h"
#include"smt_kernel.h"
#include"smt_params.h"
#include"smt_types.h"
#include"theory_opt.h"

namespace opt {

    class opt_solver : public solver_na2as {
        smt_params          m_params;
        smt::kernel         m_context;
        progress_callback * m_callback;
        symbol              m_logic;
        bool                m_objective_enabled;
        smt::theory_var     m_objective_var;
    public:
        opt_solver(ast_manager & m, params_ref const & p, symbol const & l);
        virtual ~opt_solver();

        virtual void updt_params(params_ref const & p);
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

        void set_objective(app* term);
        void toggle_objective(bool enable);
    private:
        smt::theory_opt& get_optimizer();
    };
}

#endif
