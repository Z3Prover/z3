/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_array_base.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-02.

Revision History:

--*/
#ifndef THEORY_ARRAY_BASE_H_
#define THEORY_ARRAY_BASE_H_

#include"smt_theory.h"
#include"array_decl_plugin.h"
#include"array_factory.h"

namespace smt {

    class theory_array_base : public theory {
    protected:
        bool m_found_unsupported_op;

        void found_unsupported_op(expr * n);
        
        bool is_store(app const* n) const { return n->is_app_of(get_id(), OP_STORE); }
        bool is_map(app const* n) const { return n->is_app_of(get_id(), OP_ARRAY_MAP); }
        bool is_select(app const* n) const { return n->is_app_of(get_id(), OP_SELECT); }
        bool is_default(app const* n) const { return n->is_app_of(get_id(), OP_ARRAY_DEFAULT); }
        bool is_const(app const* n) const { return n->is_app_of(get_id(), OP_CONST_ARRAY); }
        bool is_array_ext(app const * n) const { return n->is_app_of(get_id(), OP_ARRAY_EXT); }
        bool is_as_array(app const * n) const { return n->is_app_of(get_id(), OP_AS_ARRAY); }
        bool is_array_sort(sort const* s) const { return s->is_sort_of(get_id(), ARRAY_SORT); }
        bool is_array_sort(app const* n) const { return is_array_sort(get_manager().get_sort(n)); }

        bool is_store(enode const * n) const { return is_store(n->get_owner()); }
        bool is_map(enode const* n) const { return is_map(n->get_owner()); }
        bool is_select(enode const* n) const { return is_select(n->get_owner()); }
        bool is_const(enode const* n) const { return is_const(n->get_owner()); }
        bool is_as_array(enode const * n) const { return is_as_array(n->get_owner()); }
        bool is_default(enode const* n) const { return is_default(n->get_owner()); }
        bool is_array_sort(enode const* n) const { return is_array_sort(n->get_owner()); }


        app * mk_select(unsigned num_args, expr * const * args);
        app * mk_store(unsigned num_args, expr * const * args);
        app * mk_default(expr* a);


        unsigned get_dimension(sort* s) const;
        
        ptr_vector<enode>                   m_axiom1_todo;
        svector<std::pair<enode*, enode*> > m_axiom2_todo;
        svector<std::pair<enode*, enode*> > m_extensionality_todo;

        void assert_axiom(unsigned num_lits, literal * lits);
        void assert_axiom(literal l1, literal l2);
        void assert_axiom(literal l);
        void assert_store_axiom1_core(enode * n);
        void assert_store_axiom2_core(enode * store, enode * select);
        void assert_store_axiom1(enode * n) { m_axiom1_todo.push_back(n); }
        bool assert_store_axiom2(enode * store, enode * select);

        void assert_extensionality_core(enode * a1, enode * a2);
        bool assert_extensionality(enode * a1, enode * a2);

        // --------------------------------------------------
        // Array sort -> extensionality skolems
        // 
        // --------------------------------------------------
        ptr_vector<sort>                     m_sorts_trail;
        obj_map<sort, func_decl_ref_vector*> m_sort2skolem;

        func_decl_ref_vector * register_sort(sort * s_array);

        // --------------------------------------------------
        // array_value table
        //
        // Use select(A, i) nodes to represent an assignment for A.
        // This structure is used to minimize the number of times the
        // extensionality axiom is applied.
        // 
        // --------------------------------------------------
        struct value_chasher {
            unsigned operator()(enode const * n, unsigned idx) const {
                return n->get_arg(idx+1)->get_root()->hash();
            }
        };
        struct value_khasher { unsigned operator()(enode * n) const { return 17; } };
        struct value_hash_proc { 
            unsigned operator()(enode * n) const {
                return get_composite_hash<enode *, value_khasher, value_chasher>(n, n->get_num_args() - 1);
            }
        };
        struct value_eq_proc { bool operator()(enode * n1, enode * n2) const; };
        typedef ptr_hashtable<enode, value_hash_proc, value_eq_proc> array_value;

        array_value m_array_value;
        bool already_diseq(enode * v1, enode * v2);

        // --------------------------------------------------
        // Backtracking
        //
        // 
        // --------------------------------------------------
        struct scope {
            unsigned m_sorts_trail_lim;
            scope(unsigned l):m_sorts_trail_lim(l) {}
        };
        svector<scope>                      m_scopes;
        void restore_sorts(unsigned old_size);
        
        // --------------------------------------------------
        // Interface
        //
        // 
        // --------------------------------------------------
        virtual bool is_shared(theory_var v) const;
        void collect_shared_vars(sbuffer<theory_var> & result);
        unsigned mk_interface_eqs();

        virtual bool can_propagate();
        virtual void propagate();
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual void reset_eh();
        
        void reset_queues();
        // -----------------------------------
        //
        // Model generation
        //
        // -----------------------------------

        
        // I need a set of select enodes where select(A,i) = select(B,j) if i->get_root() == j->get_root()
        struct sel_khasher {
            unsigned operator()(enode const * n) const { return 0; }
        };

        struct sel_chasher {
            unsigned operator()(enode const * n, unsigned idx) const { 
                return n->get_arg(idx+1)->get_root()->hash();
            }
        };
        
        struct sel_hash {
            unsigned operator()(enode * n) const;
        };

        struct sel_eq {
            bool operator()(enode * n1, enode * n2) const;
        };
        
        typedef ptr_hashtable<enode, sel_hash, sel_eq> select_set;

        array_factory *              m_factory;
        ptr_vector<enode>            m_defaults;       // temporary field for model construction
        ptr_vector<void>             m_else_values;    // tagged pointer: expr or extra_fresh_value
        svector<int>                 m_parents;        // temporary field for model construction
        obj_map<enode, select_set*>  m_selects;        // mapping from array -> relevant selects
        ptr_vector<enode>            m_selects_domain; 
        ptr_vector<select_set>       m_selects_range;
        bool                         m_use_unspecified_default;  // temporary field for model construction

        theory_var mg_find(theory_var v);
        void mg_merge(theory_var n, theory_var m);

        void set_default(theory_var v, enode* n);
        enode* get_default(theory_var v);

        virtual void init_model(model_generator & m);
        bool is_unspecified_default_ok() const;
        void collect_defaults();
        void collect_selects();
        void propagate_select_to_store_parents(enode * r, enode * sel, svector<enode_pair> & todo);
        void propagate_selects_to_store_parents(enode * r, svector<enode_pair> & todo);
        void propagate_selects();
        select_set * get_select_set(enode * n);
        virtual void finalize_model(model_generator & m);
        virtual model_value_proc * mk_value(enode * n, model_generator & m);
        
    public:
        theory_array_base(ast_manager & m);
        virtual ~theory_array_base() { restore_sorts(0); }
    };

};

#endif /* THEORY_ARRAY_BASE_H_ */

