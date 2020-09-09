/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    array_solver.h

Abstract:

    Theory plugin for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/
#pragma once

#include "ast/ast_trail.h"
#include "sat/smt/sat_th.h"
#include "ast/array_decl_plugin.h"

namespace euf {
    class solver;
}

namespace array {

    class solver : public euf::th_euf_solver {
        typedef euf::theory_var theory_var;
        typedef euf::theory_id theory_id;
        typedef sat::literal literal;
        typedef sat::bool_var bool_var;
        typedef sat::literal_vector literal_vector;
        typedef union_find<solver, euf::solver>  array_union_find;


        struct stats {
            unsigned   m_num_store_axiom1, m_num_store_axiom2a, m_num_axiom2b, m_num_extensionality_axiom, m_num_eq_splits;
            unsigned   m_num_map_axiom, m_num_default_map_axiom;
            unsigned   m_num_select_const_axiom, m_num_default_store_axiom, m_num_default_const_axiom, m_num_default_as_array_axiom;
            unsigned   m_num_select_as_array_axiom;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        // void log_drat(array_justification const& c);

        struct var_data {
            bool               m_prop_upward { false };
            bool               m_is_array { false };
            bool               m_is_select { false };
            var_data() {}
        };
        
 
        array_util        a;
        stats             m_stats;
        sat::solver*      m_solver { nullptr };
        scoped_ptr_vector<var_data>          m_var_data;
        ast2ast_trailmap<sort, app>          m_sort2epsilon;
        ast2ast_trailmap<sort, func_decl>    m_sort2diag;
        obj_map<sort, func_decl_ref_vector*> m_sort2diff;
        array_union_find                     m_find;

        sat::solver& s() { return *m_solver;  }
        theory_var find(theory_var v) { return m_find.find(v); }

        // internalize
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        void ensure_var(euf::enode* n);
        void internalize_store(euf::enode* n); 
        void internalize_select(euf::enode* n);
        void internalize_const(euf::enode* n); 
        void internalize_ext(euf::enode* n); 
        void internalize_default(euf::enode* n); 
        void internalize_map(euf::enode* n); 
        void internalize_as_array(euf::enode* n); 

        // axioms
        struct axiom_record {
            enum class kind_t {
                is_store,
                is_select,
                is_extensionality, 
                is_default                    
            };
            kind_t      m_kind;
            euf::enode* n;
            euf::enode* select;           
            axiom_record(kind_t k, euf::enode* n, euf::enode* select = nullptr): m_kind(k), n(n), select(select) {}
        };
        svector<axiom_record> m_axiom_trail;
        void push_axiom(axiom_record const& r) { m_axiom_trail.push_back(r); }
        void assert_axiom(axiom_record const& r);

        axiom_record select_axiom(euf::enode* s, euf::enode* n) { return axiom_record(axiom_record::kind_t::is_select, n, s); }
        axiom_record default_axiom(euf::enode* n) { return axiom_record(axiom_record::kind_t::is_default, n); }
        axiom_record store_axiom(euf::enode* n) { return axiom_record(axiom_record::kind_t::is_store, n); }
        axiom_record extensionality_axiom(euf::enode* n) { return axiom_record(axiom_record::kind_t::is_extensionality, n); }
        

        sat::ext_justification_idx array_axiom() { return 0; }
        sat::ext_justification_idx store_axiom() { return array_axiom(); }
        sat::ext_justification_idx select_store_axiom() { return array_axiom(); }
        sat::ext_justification_idx select_const_axiom() { return array_axiom(); }
        sat::ext_justification_idx select_as_array_axiom() { return array_axiom(); }
        sat::ext_justification_idx select_map_axiom() { return array_axiom(); }
        sat::ext_justification_idx map_axiom() { return array_axiom(); }
        sat::ext_justification_idx default_map_axiom() { return array_axiom(); }
        sat::ext_justification_idx default_const_axiom() { return array_axiom(); }
        sat::ext_justification_idx default_store_axiom() { return array_axiom(); }


        void assert_store_axiom(app* _e);
        void assert_select_store_axiom(app* select, app* store);
        void assert_select_const_axiom(app* select, app* cnst);
        void assert_select_as_array_axiom(app* select, app* arr);
        void assert_select_map_axiom(app* select, app* map);
        void assert_extensionality(expr* e1, expr* e2);        
        void assert_default_map_axiom(app* map);
        void assert_default_const_axiom(app * cnst);
        
        void assert_default_store_axiom(app* store);
        void assert_default_as_array_axiom(app* as_array);
        

        bool has_unitary_domain(app* array_term);
        bool has_large_domain(app* array_term);
        std::pair<app*,func_decl*> mk_epsilon(sort* s);

        // solving
        void add_parent(euf::enode* child, euf::enode* parent);
        var_data& get_var_data(euf::enode* n) { return get_var_data(n->get_th_var(get_id())); }
        var_data& get_var_data(theory_var v) { return *m_var_data[find(v)]; }

        // invariants
       
    public:
        solver(euf::solver& ctx, theory_id id);
        ~solver() override {}
        void set_solver(sat::solver* s) override { m_solver = s; }
        bool is_external(bool_var v) override;
        bool propagate(literal l, sat::ext_constraint_idx idx) override;
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector & r, bool probing) override;
        void asserted(literal l) override;
        sat::check_result check() override;
        void push() override;
        void pop(unsigned n) override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        euf::th_solver* fresh(sat::solver* s, euf::solver& ctx) override;
        void new_eq_eh(euf::th_eq const& eq) override;
        bool unit_propagate() override;
        void add_value(euf::enode* n, expr_ref_vector& values) override;
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override;
        euf::theory_var mk_var(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode * n, sort * s) override;        

        void merge_eh(theory_var, theory_var, theory_var v1, theory_var v2);
        // trail_stack<euf::solver>& get_trail_stack();
    };
}
