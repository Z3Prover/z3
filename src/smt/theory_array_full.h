/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_array_full.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner 2008-22-10

Revision History:

--*/
#pragma once

#include "smt/theory_array.h"
#include "ast/ast_trail.h"

namespace smt {

    class theory_array_full : public theory_array {
        struct var_data_full {
            ptr_vector<enode>  m_maps;
            ptr_vector<enode>  m_consts;
            ptr_vector<enode>  m_as_arrays;
            ptr_vector<enode>  m_parent_maps;
        };

        ptr_vector<var_data_full> m_var_data_full;

        ast2ast_trailmap<sort, app> m_sort2epsilon;
        ast2ast_trailmap<sort, func_decl> m_sort2diag;
        obj_pair_map<expr, expr, bool> m_eqs;
        
        static unsigned const m_default_map_fingerprint = UINT_MAX - 112;
        static unsigned const m_default_store_fingerprint = UINT_MAX - 113;
        static unsigned const m_default_const_fingerprint = UINT_MAX - 115;
        static unsigned const m_default_as_array_fingerprint = UINT_MAX - 116;

    protected:

        //virtual final_check_status final_check_eh();
        void reset_eh() override;

        void set_prop_upward(theory_var v) override;
        void set_prop_upward(enode* n) override;
        void set_prop_upward(theory_var v, var_data* d) override;
        unsigned get_lambda_equiv_size(theory_var v, var_data* d) override;


        bool internalize_term(app * term) override;
        bool internalize_atom(app * atom, bool gate_ctx) override;
        void pop_scope_eh(unsigned num_scopes) override;
        theory_var mk_var(enode * n) override;
        void relevant_eh(app * n) override;

        bool should_research(expr_ref_vector & unsat_core) override;
        void add_theory_assumptions(expr_ref_vector & assumptions) override;

        void add_const(theory_var v, enode* c);
        void add_map(theory_var v, enode* s);
        void add_parent_map(theory_var v, enode* s);
        void add_as_array(theory_var v, enode* arr);

        void add_parent_select(theory_var v, enode * s) override;
        void add_parent_default(theory_var v);        

        final_check_status assert_delayed_axioms() override;

        bool instantiate_default_const_axiom(enode* cnst);
        bool instantiate_default_store_axiom(enode* store);
        bool instantiate_default_map_axiom(enode* map);
        bool instantiate_default_as_array_axiom(enode* arr);
        bool instantiate_parent_stores_default(theory_var v);

        bool has_large_domain(app* array_term);
        bool has_unitary_domain(app* array_term);
        std::pair<app*,func_decl*> mk_epsilon(sort* s);

        bool instantiate_select_const_axiom(enode* select, enode* cnst);
        bool instantiate_select_as_array_axiom(enode* select, enode* arr);
        bool instantiate_select_map_axiom(enode* select, enode* map);

        bool instantiate_axiom_map_for(theory_var v);


        bool try_assign_eq(expr* n1, expr* n2);
        void assign_eqs();

        
    public:
        theory_array_full(context& ctx);
        ~theory_array_full() override;

        theory * mk_fresh(context * new_ctx) override;

        void merge_eh(theory_var v1, theory_var v2, theory_var, theory_var) override;
        void display_var(std::ostream & out, theory_var v) const override;
        void collect_statistics(::statistics & st) const override;
    };

};


