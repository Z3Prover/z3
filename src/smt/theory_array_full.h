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
#ifndef THEORY_ARRAY_FULL_H_
#define THEORY_ARRAY_FULL_H_

#include "theory_array.h"
#include "simplifier.h"
#include "ast_trail.h"

namespace smt {

    class theory_array_full : public theory_array {
        struct var_data_full {
            ptr_vector<enode>  m_maps;
            ptr_vector<enode>  m_consts;
            ptr_vector<enode>  m_as_arrays;
            ptr_vector<enode>  m_parent_maps;
            var_data_full() {}
        };

        ptr_vector<var_data_full> m_var_data_full;

        ast2ast_trailmap<sort,app> m_sort2epsilon;
        simplifier*                m_simp;
        obj_pair_map<expr,expr,bool> m_eqs;
        svector<literal>             m_eqsv;

    protected:

        //virtual final_check_status final_check_eh();
        virtual void reset_eh();

        virtual void set_prop_upward(theory_var v);
        virtual void set_prop_upward(enode* n);
        virtual void set_prop_upward(theory_var v, var_data* d);
        virtual unsigned get_lambda_equiv_size(theory_var v, var_data* d);


        virtual bool internalize_term(app * term);
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual theory_var mk_var(enode * n);
        virtual void relevant_eh(app * n);

        void add_const(theory_var v, enode* c);
        void add_map(theory_var v, enode* s);
        void add_parent_map(theory_var v, enode* s);
        void add_as_array(theory_var v, enode* arr);

        virtual void add_parent_select(theory_var v, enode * s);
        void add_parent_default(theory_var v);        

        virtual final_check_status assert_delayed_axioms();        

        bool instantiate_default_const_axiom(enode* cnst);
        bool instantiate_default_store_axiom(enode* store);
        bool instantiate_default_map_axiom(enode* map);
        bool instantiate_default_as_array_axiom(enode* arr);

        bool has_large_domain(app* array_term);
        app* mk_epsilon(sort* s);

        bool instantiate_select_const_axiom(enode* select, enode* cnst);
        bool instantiate_select_as_array_axiom(enode* select, enode* arr);
        bool instantiate_select_map_axiom(enode* select, enode* map);

        bool instantiate_axiom_map_for(theory_var v);


        bool try_assign_eq(expr* n1, expr* n2);
        void assign_eqs();

        
    public:
        theory_array_full(ast_manager & m, theory_array_params & params);
        virtual ~theory_array_full();

        virtual theory * mk_fresh(context * new_ctx) { return alloc(theory_array_full, get_manager(), m_params); }

        virtual void merge_eh(theory_var v1, theory_var v2, theory_var, theory_var);
        virtual void display_var(std::ostream & out, theory_var v) const;
        virtual void collect_statistics(::statistics & st) const;
        virtual void init(context* ctx) { 
            // the parent class is theory_array.
            // theory::init(ctx); 
            theory_array::init(ctx); 
            m_simp = &ctx->get_simplifier(); 
        }

    };

};

#endif /* THEORY_ARRAY_H_ */

