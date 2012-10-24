/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt_solver_exp.h

Abstract:

    SMT solver using strategies and search on top of sat::solver
    This solver uses assertion_set strategies during restarts.
    
    It also uses the sat::solver to handle the Boolean structure of the problem.

Author:

    Leonardo de Moura (leonardo) 2011-06-25.

Revision History:
    This was an experiment to rewrite Z3 kernel.
    It will be deleted after we finish revamping Z3 kernel.
--*/
#ifndef _SMT_SOLVER_EXP_H_
#define _SMT_SOLVER_EXP_H_

#include"smt_solver_types.h"
#include"model.h"
#include"model_converter.h"
#include"smt_formula_compiler.h"
#include"smt_arith.h"
#include"sat_extension.h"
#include"goal.h"

namespace smt {
    
    class solver_exp {
        friend class formula_compiler;

        struct bridge : public sat::extension {
            solver_exp &      s;
            bridge(solver_exp & _s):s(_s) {}
            virtual void propagate(sat::literal l, sat::ext_constraint_idx idx, bool & keep) {}
            virtual void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r);
            virtual void asserted(sat::literal l);
            virtual sat::check_result check();
            virtual void push();
            virtual void pop(unsigned n);
            virtual void simplify();
            virtual void clauses_modifed();
            virtual lbool get_phase(sat::bool_var v);
        };

        // External ASTs are coming from m_ext_mng
        ast_manager &            m_ext_mng;
        // The ASTs are translated into the internal manager for the following reasons:
        //  1. We can run multiple smt::solver_exps in parallel with minimal synchronization
        //  2. Minimize gaps in the AST ids. 
        ast_manager              m;  // internal manager
        params_ref               m_params;
        formula_compiler         m_compiler;

        // Set of asserted expressions.
        // This assertion set belongs to ast_manager m.
        assertion_set            m_assertions;

        model_ref                m_model;
        model_converter_ref     m_mc; // chain of model converters

        atom2bool_var            m_atom2bvar;
        scoped_ptr<sat::solver>  m_sat;
        arith                    m_arith;
        bridge                   m_bridge;

        statistics               m_stats;

        volatile bool            m_cancel;

        void updt_params_core(params_ref const & p);
        void assert_expr_core(expr * t, ast_translation & translator);

        void init();
        void compile();

    public:
        solver_exp(ast_manager & ext_mng, params_ref const & p);
        ~solver_exp();

        void updt_params(params_ref const & p);
        void collect_param_descrs(param_descrs & d);

        void set_cancel(bool f);

        void assert_expr(expr * t);
        void assert_set(assertion_set const & s);
        void assert_goal(goal const & g);

        void get_assertions(assertion_set & r);
        
        // -----------------------
        //
        // Search
        //
        // -----------------------
    public:
        lbool check();
        void get_model(model_ref & m) const { m = m_model.get(); }
        void get_model_converter(model_converter_ref & mc);

        // -----------------------
        //
        // Pretty Printing
        //
        // -----------------------
    public:
        void display(std::ostream & out) const;
        void display_state(std::ostream & out) const;

        // -----------------------
        //
        // Statistics
        //
        // -----------------------
    public:
        void collect_statistics(statistics & st) const;
        void reset_statistics();
    };

};

#endif
