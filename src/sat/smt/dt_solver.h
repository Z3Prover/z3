/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    dt_solver.h

Abstract:

    Theory plugin for altegraic datatypes

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/array_decl_plugin.h"

namespace euf {
    class solver;
}

namespace dt {

    class solver : public euf::th_euf_solver {
        typedef euf::theory_var theory_var;
        typedef euf::theory_id theory_id;
        typedef euf::enode enode;
        typedef euf::enode_pair enode_pair;
        typedef euf::enode_pair_vector enode_pair_vector;
        typedef sat::bool_var bool_var;
        typedef sat::literal literal;
        typedef sat::literal_vector literal_vector;
        typedef union_find<solver, euf::solver>  dt_union_find;

        struct var_data {
            ptr_vector<enode> m_recognizers; //!< recognizers of this equivalence class that are being watched.
            enode *           m_constructor; //!< constructor of this equivalence class, 0 if there is no constructor in the eqc.
            var_data():
                m_constructor(nullptr) {
            }
        };

        // class for managing state of final_check
        class final_check_st {
            solver& s;
        public:
            final_check_st(solver& s);
            ~final_check_st();
        };

        struct stats {
            unsigned   m_occurs_check, m_splits;
            unsigned   m_assert_cnstr, m_assert_accessor, m_assert_update_field;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        mutable datatype_util dt;
        array_util            m_autil;
        stats                 m_stats;
        ptr_vector<var_data>  m_var_data;
        dt_union_find         m_find;
        expr_ref_vector       m_args;

        bool is_constructor(expr * f) const { return dt.is_constructor(f); }
        bool is_recognizer(expr * f) const { return dt.is_recognizer(f); }
        bool is_accessor(expr * f) const { return dt.is_accessor(f); }
        bool is_update_field(expr * f) const { return dt.is_update_field(f); }

        bool is_constructor(enode * n) const { return is_constructor(n->get_expr()); }
        bool is_recognizer(enode * n) const { return is_recognizer(n->get_expr()); }
        bool is_accessor(enode * n) const { return is_accessor(n->get_expr()); }
        bool is_update_field(enode * n) const { return dt.is_update_field(n->get_expr()); }

        bool is_datatype(expr* e) const { return dt.is_datatype(e->get_sort()); }
        bool is_datatype(enode* n) const { return is_datatype(n->get_expr()); }

        void assert_eq_axiom(enode * lhs, expr * rhs, literal antecedent = sat::null_literal);
        void assert_is_constructor_axiom(enode * n, func_decl * c, literal antecedent = sat::null_literal);
        void assert_accessor_axioms(enode * n);
        void assert_update_field_axioms(enode * n);
        void add_recognizer(theory_var v, enode * recognizer);
        void propagate_recognizer(theory_var v, enode * r);
        void sign_recognizer_conflict(enode * c, enode * r);

        typedef enum { ENTER, EXIT } stack_op;
        typedef obj_map<enode, enode*> parent_tbl;
        typedef std::pair<stack_op, enode*> stack_entry;

        ptr_vector<enode>     m_to_unmark1;
        ptr_vector<enode>     m_to_unmark2;
        enode_pair_vector     m_used_eqs; // conflict, if any
        parent_tbl            m_parent; // parent explanation for occurs_check
        svector<stack_entry>  m_dfs; // stack for DFS for occurs_check
        sat::literal_vector   m_lits;

        void clear_mark();

        void oc_mark_on_stack(enode * n);
        bool oc_on_stack(enode * n) const { return n->get_root()->is_marked1(); }

        void oc_mark_cycle_free(enode * n);
        bool oc_cycle_free(enode * n) const { return n->get_root()->is_marked2(); }

        void oc_push_stack(enode * n);
        ptr_vector<enode> m_array_args;
        ptr_vector<enode> const& get_array_args(enode* n);

        void pop_core(unsigned n) override;

        enode * oc_get_cstor(enode * n);
        bool occurs_check(enode * n);
        bool occurs_check_enter(enode * n);
        void occurs_check_explain(enode * top, enode * root);
        void explain_is_child(enode* parent, enode* child);

        void mk_split(theory_var v, bool is_final);
        void mk_enum_split(theory_var v);

        void display_var(std::ostream & out, theory_var v) const;

        // internalize
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        void clone_var(solver& src, theory_var v);

        sat::literal mk_recognizer_constructor_literal(func_decl* c, euf::enode* n);
        
    public:
        solver(euf::solver& ctx, theory_id id);
        ~solver() override;

        bool is_external(bool_var v) override { return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) override;
        void asserted(literal l) override;
        sat::check_result check() override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return euf::th_explain::from_index(idx).display(out); }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return display_justification(out, idx); }
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(euf::solver& ctx) override;
        void new_eq_eh(euf::th_eq const& eq) override;
        bool unit_propagate() override { return false; }
        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;
        bool include_func_interp(func_decl* f) const override;
        sat::literal internalize(expr* e, bool sign, bool root, bool redundant) override;
        void internalize(expr* e, bool redundant) override;
        euf::theory_var mk_var(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override;
        bool is_shared(theory_var v) const override { return false; }
        lbool get_phase(bool_var v) override { return l_true; }
        bool enable_self_propagate() const override { return true; }

        void merge_eh(theory_var, theory_var, theory_var v1, theory_var v2);
        void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) {}
        void unmerge_eh(theory_var v1, theory_var v2) {}
    };
}
