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

#ifndef PROP_SOLVER_H_
#define PROP_SOLVER_H_

#include <map>
#include <string>
#include <utility>
#include "ast.h"
#include "obj_hashtable.h"
#include "smt_kernel.h"
#include "util.h"
#include "vector.h"
#include "pdr_manager.h"
#include "pdr_smt_context_manager.h"


namespace pdr {
    class prop_solver {
    
    private:
        smt_params&         m_fparams;        
        ast_manager&        m;
        manager&            m_pm;
        symbol              m_name;
        scoped_ptr<pdr::smt_context> m_ctx;
        decl_vector         m_level_preds;      
        app_ref_vector      m_pos_level_atoms;  // atoms used to identify level
        app_ref_vector      m_neg_level_atoms;  // 
        obj_hashtable<expr> m_level_atoms_set;
        app_ref_vector      m_proxies;          // predicates for assumptions
        expr_ref_vector*    m_core; 
        model_ref*          m_model;
        expr_ref_vector*    m_consequences;
        bool                m_subset_based_core;
        bool                m_assumes_level;
        bool                m_use_farkas;
        func_decl_set       m_aux_symbols;      
        bool                m_in_level;         
        unsigned            m_current_level;    // set when m_in_level
        
        /** Add level atoms activating certain level into a vector */
        void push_level_atoms(unsigned level, expr_ref_vector & tgt) const;
        
        void ensure_level(unsigned lvl);

        class safe_assumptions;

        void extract_theory_core(safe_assumptions& assumptions);

        void extract_subset_core(safe_assumptions& assumptions);
        
        lbool check_safe_assumptions(
            safe_assumptions& assumptions,
            expr_ref_vector const& atoms);
        
        
    public:
        prop_solver(pdr::manager& pm, symbol const& name);
        
        /** return true is s is a symbol introduced by prop_solver */
        bool is_aux_symbol(func_decl * s) const { 
            return 
                m_aux_symbols.contains(s) ||
                m_ctx->is_aux_predicate(s); 
        }

        void set_core(expr_ref_vector* core) { m_core = core; }
        void set_model(model_ref* mdl) { m_model = mdl; }
        void set_subset_based_core(bool f) { m_subset_based_core = f; }
        void set_consequences(expr_ref_vector* consequences) { m_consequences = consequences; }

        bool assumes_level() const { return m_assumes_level; }
        
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
        
        void set_use_farkas(bool f) { m_use_farkas = f; }
        bool get_use_farkas() const { return m_use_farkas; }
        
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
        lbool check_assumptions(const expr_ref_vector & atoms);
        
        lbool check_conjunction_as_assumptions(expr * conj);
        
        /**
         * Like check_assumptions, except it also asserts an extra formula
         */
        lbool check_assumptions_and_formula(
            const expr_ref_vector & atoms, 
            expr * form);
        
        void collect_statistics(statistics& st) const;

        void reset_statistics();
        
    };
}


#endif
