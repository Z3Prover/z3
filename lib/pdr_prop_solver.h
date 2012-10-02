/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    prop_solver.h

Abstract:

    SAT solver abstraction for PDR.

Author:

    Krystof Hoder (t-khoder) 2011-8-17.

Revision History:

--*/

#ifndef _PROP_SOLVER_H_
#define _PROP_SOLVER_H_

#include <map>
#include <string>
#include <utility>
#include "ast.h"
#include "obj_hashtable.h"
#include "smt_solver.h"
#include "util.h"
#include "vector.h"
#include "pdr_manager.h"
#include "pdr_smt_context_manager.h"

namespace pdr {
    class prop_solver {
    private:
        front_end_params&   m_fparams;        
        ast_manager&        m;
        manager&            m_pm;
        symbol              m_name;
        bool                m_try_minimize_core;
        scoped_ptr<pdr::smt_context> m_ctx;
        decl_vector         m_level_preds;      
        app_ref_vector      m_pos_level_atoms;  // atoms used to identify level
        app_ref_vector      m_neg_level_atoms;  // 
        obj_hashtable<expr> m_level_atoms_set;
        app_ref_vector      m_fresh;            // predicates for assumptions
        func_decl_set       m_aux_symbols;      
        bool                m_in_level;         
        unsigned            m_current_level;    // set when m_in_level
        
        /** Add level atoms activating certain level into a vector */
        void push_level_atoms(unsigned level, expr_ref_vector & tgt) const;
        
        void ensure_level(unsigned lvl);
        
        lbool check_safe_assumptions(
            const expr_ref_vector & atoms, 
            expr_ref_vector * core, 
            model_ref * mdl, 
            bool& assumes_level);
        
        class safe_assumptions;
        
    public:
        prop_solver(pdr::manager& pm, symbol const& name);
        
        /** return true is s is a symbol introduced by prop_solver */
        bool is_aux_symbol(func_decl * s) const { 
            return 
                m_aux_symbols.contains(s) ||
                m_ctx->is_aux_predicate(s); 
        }
        
        void add_level();
        unsigned level_cnt() const;
        
        class scoped_level {
            bool& m_lev;
        public:
            scoped_level(prop_solver& ps, unsigned lvl):m_lev(ps.m_in_level) { 
                SASSERT(!m_lev); m_lev = true; ps.m_current_level = lvl; 
            }
                ~scoped_level() { m_lev = false; }
        };
        
        void add_formula(expr * form);
        void add_level_formula(expr * form, unsigned level);
                
        /**
         * Return true iff conjunction of atoms is consistent with the current state of 
         * the solver.
         *
         * If the conjunction of atoms is inconsistent with the solver state and core is non-zero,
         * core will contain an unsatisfiable core of atoms.
         *
         * If the conjunction of atoms is consistent with the solver state and o_model is non-zero,
         * o_model will contain the "o" literals true in the assignment.
         */
        lbool check_assumptions(
            const expr_ref_vector & atoms, 
            expr_ref_vector * core, model_ref * mdl, 
            bool& assumes_level);
        
        lbool check_conjunction_as_assumptions(
            expr * conj, expr_ref_vector * core, 
            model_ref * mdl, bool& assumes_level);
        
        /**
         * Like check_assumptions, except it also asserts an extra formula
         */
        lbool check_assumptions_and_formula(
            const expr_ref_vector & atoms, 
            expr * form, 
            expr_ref_vector * core, 
            model_ref * mdl, 
            bool& assumes_level);
        
        void collect_statistics(statistics& st) const;
        
    };
}


#endif
