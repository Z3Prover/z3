/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_solver.h

Abstract:

    Wraps smt::kernel as a solver for optimization

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

    Based directly on smt_solver.
   
--*/
#ifndef _OPT_SOLVER_H_
#define _OPT_SOLVER_H_

#include"inf_rational.h"
#include"inf_eps_rational.h"
#include"ast.h"
#include"params.h"
#include"solver_na2as.h"
#include"smt_kernel.h"
#include"smt_params.h"
#include"smt_types.h"
#include"theory_opt.h"

namespace opt {

    class opt_solver : public solver_na2as {
    public:
        typedef inf_eps_rational<inf_rational> inf_value;
    private:
        smt_params          m_params;
        smt::kernel         m_context;
        progress_callback * m_callback;
        symbol              m_logic;
        bool                m_objective_enabled;
        svector<smt::theory_var>  m_objective_vars;
        vector<inf_value>         m_objective_values;
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

        smt::theory_var add_objective(app* term);
        void reset_objectives();

        vector<inf_value> const& get_objective_values();
        
        class toggle_objective {
            opt_solver& s;
            bool m_old_value;
        public:
            toggle_objective(opt_solver& s, bool new_value);
            ~toggle_objective();
        };
    private:
        smt::theory_opt& get_optimizer();
    };
}

#endif
