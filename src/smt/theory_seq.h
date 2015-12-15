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
#include "ast_trail.h"
#include "scoped_vector.h"

namespace smt {

    class theory_seq : public theory {
        typedef scoped_dependency_manager<enode_pair> enode_pair_dependency_manager;
        typedef enode_pair_dependency_manager::dependency enode_pair_dependency;
        
        typedef trail_stack<theory_seq> th_trail_stack;
        typedef std::pair<expr*, enode_pair_dependency*> expr_dep;
        typedef obj_map<expr, expr_dep> eqdep_map_t; 

        // cache to track evaluations under equalities
        class eval_cache {
            eqdep_map_t             m_map;
            expr_ref_vector         m_trail;
        public:
            eval_cache(ast_manager& m): m_trail(m) {}
            bool find(expr* v, expr_dep& r) const { return m_map.find(v, r); }
            void insert(expr* v, expr_dep& r) { m_trail.push_back(v); m_trail.push_back(r.first); m_map.insert(v, r); }
            void reset() { m_map.reset(); m_trail.reset(); }
        };
        
        // map from variables to representatives 
        // + a cache for normalization.
        class solution_map {
            enum map_update { INS, DEL };
            ast_manager&                      m;
            enode_pair_dependency_manager&    m_dm;
            eqdep_map_t                       m_map;            
            eval_cache                        m_cache;
            expr_ref_vector                   m_lhs, m_rhs;
            ptr_vector<enode_pair_dependency> m_deps;
            svector<map_update>               m_updates;
            unsigned_vector                   m_limit;

            void add_trail(map_update op, expr* l, expr* r, enode_pair_dependency* d);
        public:
            solution_map(ast_manager& m, enode_pair_dependency_manager& dm): 
                m(m),  m_dm(dm), m_cache(m), m_lhs(m), m_rhs(m) {}
            bool empty() const { return m_map.empty(); }
            void  update(expr* e, expr* r, enode_pair_dependency* d);
            void  add_cache(expr* v, expr_dep& r) { m_cache.insert(v, r); }
            bool  find_cache(expr* v, expr_dep& r) { return m_cache.find(v, r); }
            expr* find(expr* e, enode_pair_dependency*& d);
            void  cache(expr* e, expr* r, enode_pair_dependency* d);
            void push_scope() { m_limit.push_back(m_updates.size()); }
            void pop_scope(unsigned num_scopes);
            void display(std::ostream& out) const;
        };

        // Table of current disequalities
        class exclusion_table {
            typedef obj_pair_hashtable<expr, expr> table_t;
            ast_manager&                      m;
            table_t                           m_table;
            expr_ref_vector                   m_lhs, m_rhs;
            unsigned_vector                   m_limit;
        public:
            exclusion_table(ast_manager& m): m(m), m_lhs(m), m_rhs(m) {}
            ~exclusion_table() { }
            bool empty() const { return m_table.empty(); }
            void update(expr* e, expr* r);
            bool contains(expr* e, expr* r) const;
            void push_scope() { m_limit.push_back(m_lhs.size()); }
            void pop_scope(unsigned num_scopes);
            void display(std::ostream& out) const;            
        };

        // Asserted or derived equality with dependencies
        struct eq {
            expr_ref               m_lhs;
            expr_ref               m_rhs;
            enode_pair_dependency* m_dep;
            eq(expr_ref& l, expr_ref& r, enode_pair_dependency* d):
                m_lhs(l), m_rhs(r), m_dep(d) {}
            eq(eq const& other): m_lhs(other.m_lhs), m_rhs(other.m_rhs), m_dep(other.m_dep) {}
            eq& operator=(eq const& other) { m_lhs = other.m_lhs; m_rhs = other.m_rhs; m_dep = other.m_dep; return *this; }
        };

        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(stats)); }
            unsigned m_num_splits;
            unsigned m_num_reductions;
        };
        ast_manager&                        m;
        enode_pair_dependency_manager       m_dm;
        solution_map                        m_rep;        // unification representative.
        scoped_vector<eq>                   m_eqs;        // set of current equations.

        seq_factory*    m_factory;               // value factory
        expr_ref_vector m_ineqs;                 // inequalities to check solution against
        exclusion_table m_exclude;               // set of asserted disequalities.
        expr_ref_vector m_axioms;                // list of axioms to add.
        unsigned        m_axioms_head;           // index of first axiom to add.
        unsigned        m_branch_variable_head;  // index of first equation to examine.
        bool            m_incomplete;            // is the solver (clearly) incomplete for the fragment.
        bool            m_has_length;            // is length applied
        bool            m_model_completion;      // during model construction, invent values in canonizer
        th_rewriter     m_rewrite;
        seq_util        m_util;
        arith_util      m_autil;
        th_trail_stack  m_trail_stack;
        stats           m_stats;
        symbol          m_prefix_sym;
        symbol          m_suffix_sym;
        symbol          m_contains_left_sym;
        symbol          m_contains_right_sym;
        symbol          m_left_sym;               // split variable left part
        symbol          m_right_sym;              // split variable right part

        virtual final_check_status final_check_eh();
        virtual bool internalize_atom(app*, bool);
        virtual bool internalize_term(app*);
        virtual void internalize_eq_eh(app * atom, bool_var v);
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
        virtual void apply_sort_cnstr(enode* n, sort* s);
        virtual void display(std::ostream & out) const;        
        virtual void collect_statistics(::statistics & st) const;
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);
        virtual void init_model(model_generator & mg);

        // final check 
        bool check_ineqs();              // check if inequalities are violated.
        bool simplify_and_solve_eqs();   // solve unitary equalities
        bool branch_variable();          // branch on a variable
        bool split_variable();           // split a variable
        bool is_solved(); 
        bool check_length_coherence();  
        bool check_length_coherence_tbd();  
        bool check_ineq_coherence(); 

        bool pre_process_eqs(bool simplify_or_solve);
        bool simplify_eqs();
        bool simplify_eq(expr* l, expr* r, enode_pair_dependency* dep);
        bool solve_unit_eq(expr* l, expr* r, enode_pair_dependency* dep);
        bool solve_basic_eqs();

        // asserting consequences
        void propagate_lit(enode_pair_dependency* dep, literal lit);
        void propagate_eq(enode_pair_dependency* dep, enode* n1, enode* n2);
        void propagate_eq(bool_var v, expr* e1, expr* e2);
        void set_conflict(enode_pair_dependency* dep);

        bool find_branch_candidate(expr* l, ptr_vector<expr> const& rs);
        bool assume_equality(expr* l, expr* r);

        // variable solving utilities
        bool occurs(expr* a, expr* b);
        bool is_var(expr* b);
        void add_solution(expr* l, expr* r, enode_pair_dependency* dep);
        bool is_left_select(expr* a, expr*& b);
        bool is_right_select(expr* a, expr*& b);
        expr_ref canonize(expr* e, enode_pair_dependency*& eqs);
        expr_ref expand(expr* e, enode_pair_dependency*& eqs);
        void add_dependency(enode_pair_dependency*& dep, enode* a, enode* b);

    
        // terms whose meaning are encoded using axioms.
        void enque_axiom(expr* e);
        void deque_axiom(expr* e);
        void add_axiom(literal l1, literal l2 = null_literal, literal l3 = null_literal, literal l4 = null_literal);        
        void add_indexof_axiom(expr* e);
        void add_replace_axiom(expr* e);
        void add_extract_axiom(expr* e);
        void add_length_axiom(expr* n);
        void add_length_unit_axiom(expr* n);
        void add_length_empty_axiom(expr* n);
        void add_length_concat_axiom(expr* n);
        void add_length_string_axiom(expr* n);
        void add_elim_string_axiom(expr* n);
        void add_at_axiom(expr* n);
        literal mk_literal(expr* n);
        void tightest_prefix(expr* s, expr* x, literal lit, literal lit2 = null_literal);
        expr* mk_sub(expr* a, expr* b);
        enode* ensure_enode(expr* a);

        expr_ref mk_skolem(symbol const& s, expr* e1, expr* e2 = 0, expr* e3 = 0, sort* range = 0);

        void set_incomplete(app* term);

        // diagnostics
        void display_equations(std::ostream& out) const;
        void display_deps(std::ostream& out, enode_pair_dependency* deps) const;
    public:
        theory_seq(ast_manager& m);
        virtual ~theory_seq();

    };
};

#endif /* THEORY_SEQ_H_ */

