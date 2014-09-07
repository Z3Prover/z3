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
#include"filter_model_converter.h"

namespace opt {

    typedef inf_eps_rational<inf_rational> inf_eps;


    class opt_solver : public solver_na2as {
    private:
        smt_params          m_params;
        smt::kernel         m_context;
        ast_manager&        m;
        filter_model_converter& m_fm;
        progress_callback * m_callback;
        symbol              m_logic;
        bool                m_objective_enabled;
        svector<smt::theory_var>  m_objective_vars;
        vector<inf_eps>     m_objective_values;
        bool                m_dump_benchmarks;
        static unsigned     m_dump_count;
        statistics          m_stats;
        bool                m_first;
    public:
        opt_solver(ast_manager & m, params_ref const & p, filter_model_converter& fm);
        virtual ~opt_solver();

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
        void set_logic(symbol const& logic);

        smt::theory_var add_objective(app* term);
        void reset_objectives();
        void maximize_objective(unsigned i, expr_ref& blocker);
        void maximize_objectives(expr_ref_vector& blockers);

        vector<inf_eps> const& get_objective_values();
        inf_eps const & get_objective_value(unsigned obj_index);
        expr_ref mk_ge(unsigned obj_index, inf_eps const& val);

        static opt_solver& to_opt(solver& s);
        bool dump_benchmarks();

        smt::context& get_context() { return m_context.get_context(); } // used by weighted maxsat.
        
        smt::theory_opt& get_optimizer();

        void to_smt2_benchmark(std::ofstream & buffer, 
                               unsigned num_assumptions, expr * const * assumptions,
                               char const * name = "benchmarks", 
                               char const * logic = "", char const * status = "unknown", char const * attributes = "");
    };
}

#endif
