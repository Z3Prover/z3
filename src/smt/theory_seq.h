/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    theory_seq.h

Abstract:

    Native theory solver for sequences.

Author:

    Nikolaj Bjorner (nbjorner) 2015-6-12

Revision History:

--*/
#ifndef THEORY_SEQ_H_
#define THEORY_SEQ_H_

#include "smt_theory.h"
#include "seq_decl_plugin.h"
#include "theory_seq_empty.h"
#include "th_rewriter.h"
#include "union_find.h"

namespace smt {

    class theory_seq : public theory {
        struct config {
            static const bool preserve_roots   = true;
            static const unsigned max_trail_sz = 16;
            static const unsigned factor       = 2;
            typedef small_object_allocator   allocator;
        };
        typedef scoped_dependency_manager<enode_pair> enode_pair_dependency_manager;
        typedef enode_pair_dependency_manager::dependency enode_pair_dependency;
        struct enode_pair_dependency_array_config : public config {
            typedef enode_pair_dependency*      value;
            typedef dummy_value_manager<value>  value_manager;
            static const bool ref_count = false;
        };
        typedef parray_manager<enode_pair_dependency_array_config> enode_pair_dependency_array_manager;
        typedef enode_pair_dependency_array_manager::ref enode_pair_dependency_array;
        
        typedef union_find<theory_seq> th_union_find;
        typedef trail_stack<theory_seq> th_trail_stack;
        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(stats)); }
            unsigned m_num_splits;
        };
        ast_manager&                        m;
        small_object_allocator              m_alloc;
        enode_pair_dependency_array_config::value_manager m_dep_array_value_manager;
        enode_pair_dependency_manager       m_dm;
        enode_pair_dependency_array_manager m_dam;
        expr_ref_vector                     m_rep;        // unification representative.
        vector<expr_array>                  m_lhs, m_rhs; // persistent sets of equalities.
        vector<enode_pair_dependency_array> m_deps;

        unsigned                            m_eqs_head;   // index of unprocessed equation. deprecate
        


        expr_ref_vector m_ineqs;      // inequalities to check
        expr_ref_vector m_axioms;     
        unsigned        m_axioms_head;        
        bool            m_incomplete; 
        th_rewriter     m_rewrite;
        seq_util        m_util;
        arith_util      m_autil;
        th_trail_stack  m_trail_stack;
        th_union_find   m_find;
        stats           m_stats;

        virtual final_check_status final_check_eh();
        virtual bool internalize_atom(app*, bool);
        virtual bool internalize_term(app*);
        virtual void new_eq_eh(theory_var, theory_var);
        virtual void new_diseq_eh(theory_var, theory_var);
        virtual void assign_eq(bool_var v, bool is_true);
        virtual bool can_propagate();
        virtual void propagate();
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual void restart_eh();
        virtual void relevant_eh(app* n);
        virtual theory* mk_fresh(context* new_ctx) { return alloc(theory_seq, new_ctx->get_manager()); }
        virtual char const * get_name() const { return "seq"; }
        virtual theory_var mk_var(enode* n);

        bool check_ineqs();
        bool pre_process_eqs(bool simplify_or_solve);
        bool simplify_eqs();
        bool simplify_eq(expr* l, expr* r, enode_pair_dependency* deps);
        bool solve_unit_eq(expr* l, expr* r, enode_pair_dependency* deps);
        bool solve_basic_eqs();
        bool simplify_and_solve_eqs();
        bool occurs(expr* a, expr* b);
        bool is_var(expr* b);
        void add_solution(expr* l, expr* r, enode_pair_dependency* dep);

        final_check_status add_axioms();

        void assert_axiom(expr_ref& e);
        void create_axiom(expr_ref& e);
        expr_ref canonize(expr* e, enode_pair_dependency*& eqs);
        expr_ref expand(expr* e, enode_pair_dependency*& eqs);
        void add_dependency(enode_pair_dependency*& dep, enode* a, enode* b);
        enode_pair_dependency* leaf(enode* a, enode* b);
        enode_pair_dependency* join(enode_pair_dependency* a, enode_pair_dependency* b);

        void propagate_eq(bool_var v, expr* e1, expr* e2);
        expr_ref mk_skolem(char const* name, expr* e1, expr* e2);

        void set_incomplete(app* term);
    public:
        theory_seq(ast_manager& m);
        virtual void init_model(model_generator & mg) {
            mg.register_factory(alloc(seq_factory, get_manager(), get_family_id(), mg.get_model()));
        }

        th_trail_stack & get_trail_stack() { return m_trail_stack; }
        virtual void merge_eh(theory_var v1, theory_var v2, theory_var, theory_var);
        static void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) {}
        void unmerge_eh(theory_var v1, theory_var v2);

    };
};

#endif /* THEORY_SEQ_H_ */

