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

        struct stats {
            unsigned   m_num_store_axiom1, m_num_store_axiom2a, m_num_axiom2b, m_num_extensionality_axiom, m_num_eq_splits;
            unsigned   m_num_map_axiom, m_num_default_map_axiom;
            unsigned   m_num_select_const_axiom, m_num_default_store_axiom, m_num_default_const_axiom, m_num_default_as_array_axiom;
            unsigned   m_num_select_as_array_axiom;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        // void log_drat(array_justification const& c);

        
 
        array_util        a;
        stats             m_stats;
        sat::solver*      m_solver { nullptr };
        ast2ast_trailmap<sort, app> m_sort2epsilon;
        ast2ast_trailmap<sort, func_decl> m_sort2diag;
        obj_map<sort, func_decl_ref_vector*> m_sort2diff;

        sat::solver& s() { return *m_solver;  }

        // internalize

        // axioms
        sat::ext_justification_idx array_axiom() { return 0; }
        sat::ext_justification_idx store_axiom1() { return array_axiom(); }
        sat::ext_justification_idx store_axiom2() { return array_axiom(); }
        sat::ext_justification_idx select_const_axiom() { return array_axiom(); }
        sat::ext_justification_idx map_axiom() { return array_axiom(); }
        sat::ext_justification_idx default_map_axiom() { return array_axiom(); }
        sat::ext_justification_idx default_const_axiom() { return array_axiom(); }
        sat::ext_justification_idx default_store_axiom() { return array_axiom(); }
        sat::ext_justification_idx select_as_array_axiom() { return array_axiom(); }

        void assert_store_axiom1(expr* _e);
        void assert_store_axiom2(expr* _store, expr* _select);
        void assert_select_const_axiom(expr* cnts, expr* _select);
        void assert_extensionality(expr* e1, expr* e2);
        void assert_map(expr* _select, expr* _map);
        void assert_default_map(expr* _map);
        void assert_default_const(expr * cnst);
        void assert_select_as_array_axiom(expr* _select, expr* _arr);
        void assert_default_store_axiom(expr* _store);

        bool has_unitary_domain(app* array_term);
        bool has_large_domain(app* array_term);
        std::pair<app*,func_decl*> mk_epsilon(sort* s);

        // solving
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
    };
}
