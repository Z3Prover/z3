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
            unsigned m_num_store_axiom, m_num_extensionality_axiom;
            unsigned m_num_eq_splits, m_num_congruence_axiom;
            unsigned m_num_select_store_axiom, m_num_select_as_array_axiom, m_num_select_map_axiom;
            unsigned m_num_select_const_axiom, m_num_select_store_axiom_delayed;
            unsigned m_num_default_store_axiom, m_num_default_map_axiom;
            unsigned m_num_default_const_axiom, m_num_default_as_array_axiom;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        // void log_drat(array_justification const& c);

        struct var_data {
            bool                   m_prop_upward{ false };            
            bool                   m_is_array{ false };
            bool                   m_is_select{ false };
            ptr_vector<euf::enode> m_parents;
            var_data() {}
        };


        array_util        a;
        stats             m_stats;
        sat::solver*      m_solver{ nullptr };
        scoped_ptr_vector<var_data>          m_var_data;
        ast2ast_trailmap<sort, app>          m_sort2epsilon;
        ast2ast_trailmap<sort, func_decl>    m_sort2diag;
        obj_map<sort, func_decl_ref_vector*> m_sort2diff;
        array_union_find                     m_find;

        sat::solver& s() { return *m_solver; }
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
                is_default,
                is_congruence
            };
            kind_t      m_kind;
            euf::enode* n;
            euf::enode* select;
            axiom_record(kind_t k, euf::enode* n, euf::enode* select = nullptr) : m_kind(k), n(n), select(select) {}

            struct hash {
                solver& s;
                hash(solver& s) :s(s) {}
                unsigned operator()(unsigned idx) const {
                    auto const& r = s.m_axiom_trail[idx];
                    return mk_mix(r.n->get_expr_id(), (unsigned)r.m_kind, r.select ? r.select->get_expr_id() : 1);
                }
            };

            struct eq {
                solver& s;
                eq(solver& s) :s(s) {}
                unsigned operator()(unsigned a, unsigned b) const {
                    auto const& p = s.m_axiom_trail[a];
                    auto const& r = s.m_axiom_trail[b];
                    return p.n == r.n && p.select == r.select && p.m_kind == r.m_kind;
                }
            };
        };
        typedef hashtable<unsigned, axiom_record::hash, axiom_record::eq> axiom_table_t;
        axiom_record::hash    m_hash;
        axiom_record::eq      m_eq;
        axiom_table_t         m_axioms;
        svector<axiom_record> m_axiom_trail;
        unsigned              m_qhead { 0 };
        void push_axiom(axiom_record const& r);
        bool assert_axiom(unsigned idx);

        axiom_record select_axiom(euf::enode* s, euf::enode* n) { return axiom_record(axiom_record::kind_t::is_select, n, s); }
        axiom_record default_axiom(euf::enode* n) { return axiom_record(axiom_record::kind_t::is_default, n); }
        axiom_record store_axiom(euf::enode* n) { return axiom_record(axiom_record::kind_t::is_store, n); }
        axiom_record extensionality_axiom(euf::enode* n) { return axiom_record(axiom_record::kind_t::is_extensionality, n); }
        axiom_record congruence_axiom(euf::enode* a, euf::enode* b) { return axiom_record(axiom_record::kind_t::is_congruence, a, b); }

        scoped_ptr<sat::constraint_base> m_constraint;

        sat::ext_justification_idx array_axiom() { return m_constraint->to_index(); }

        bool assert_store_axiom(app* _e);
        bool assert_select_store_axiom(app* select, app* store);
        bool assert_select_const_axiom(app* select, app* cnst);
        bool assert_select_as_array_axiom(app* select, app* arr);
        bool assert_select_map_axiom(app* select, app* map);
        bool assert_select_lambda_axiom(app* select, expr* lambda);
        bool assert_extensionality(expr* e1, expr* e2);
        bool assert_default_map_axiom(app* map);
        bool assert_default_const_axiom(app* cnst);
        bool assert_default_store_axiom(app* store);
        bool assert_default_as_array_axiom(app* as_array);
        bool assert_congruent_axiom(expr* e1, expr* e2);
        bool add_delayed_axioms();
        
        bool has_unitary_domain(app* array_term);
        bool has_large_domain(app* array_term);
        std::pair<app*, func_decl*> mk_epsilon(sort* s);
        void collect_shared_vars(sbuffer<theory_var>& roots);
        bool add_interface_equalities();
        bool is_select_arg(euf::enode* r);

        // solving
        void add_parent(theory_var v_child, euf::enode* parent);
        void add_parent(euf::enode* child, euf::enode* parent) { add_parent(child->get_th_var(get_id()), parent); }
        void add_store(theory_var v, euf::enode* store);        
        void set_prop_upward(theory_var v);
        void set_prop_upward(var_data& d);
        void set_prop_upward(euf::enode* n);
        void push_parent_select_store_axioms(theory_var v);
        unsigned get_lambda_equiv_size(var_data const& d);

        var_data& get_var_data(euf::enode* n) { return get_var_data(n->get_th_var(get_id())); }
        var_data& get_var_data(theory_var v) { return *m_var_data[v]; }
        

        // invariants

    public:
        solver(euf::solver& ctx, theory_id id);
        ~solver() override {}
        void set_solver(sat::solver* s) override { m_solver = s; }
        bool is_external(bool_var v) override { return false; }
        bool propagate(literal l, sat::ext_constraint_idx idx) override { UNREACHABLE(); return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) override {}
        void asserted(literal l) override {}
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
        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        void add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override;
        euf::theory_var mk_var(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override;

        void merge_eh(theory_var, theory_var, theory_var v1, theory_var v2);
        void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) {}
        void unmerge_eh(theory_var v1, theory_var v2);
    };
}
