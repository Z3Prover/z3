/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt_formula_compiler.h

Abstract:

    Auxiliary class for smt::solver
    Convert Exprs into Internal data-structures.    
    
Author:

    Leonardo de Moura (leonardo) 2011-06-25.

Revision History:

--*/
#ifndef _SMT_FORMULA_COMPILER_H_
#define _SMT_FORMULA_COMPILER_H_

#include"smt_solver_types.h"
#include"assertion_set_rewriter.h"
#include"elim_term_ite_strategy.h"
#include"arith_decl_plugin.h"
#include"assertion_set2sat.h"

namespace smt {
    
    class formula_compiler {
        solver_exp &           s;
        arith_util             m_a_util;
        assertion_set_rewriter m_normalizer;
        elim_term_ite_strategy m_elim_ite;
        assertion_set2sat      m_to_sat;

        void normalize();
        void elim_term_ite();
        void mark_axioms(assertion_set const & s, expr_fast_mark2 & axioms);
        void unmark_nested_atoms(assertion_set const & s, expr_fast_mark2 & axioms);
        void assert_axiom(expr * f, bool neg);
        void register_atom(expr * f, sat::bool_var p);
        void compile_formulas(assertion_set const & assertions);

    public:
        formula_compiler(solver_exp & s, params_ref const & p);
        ~formula_compiler();

        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);
        
        void operator()(); 
        
        void set_cancel(bool f);

        void collect_statistics(statistics & st);
        void reset_statistics();
    };

};

#endif
