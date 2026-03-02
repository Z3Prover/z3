/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    nseq_state.h

Abstract:

    State management for the Nielsen-based string theory solver.
    Tracks word equations, disequalities, regex memberships,
    and string predicates with backtrackable scope management.

Author:

    Clemens Eisenhofer
    Nikolaj Bjorner (nbjorner) 2025-2-28

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_trail.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "util/obj_hashtable.h"
#include "smt/smt_theory.h"
#include "smt/nseq_constraint.h"

namespace smt {

    class theory_nseq;

    // Union-find for tracking equivalence classes of string variables.
    typedef union_find<theory_nseq> nseq_union_find;

    // Statistics for the nseq solver.
    struct nseq_stats {
        unsigned m_num_eqs;
        unsigned m_num_neqs;
        unsigned m_num_memberships;
        unsigned m_num_predicates;
        unsigned m_num_conflicts;
        unsigned m_num_propagations;
        unsigned m_num_splits;
        unsigned m_num_axioms;
        nseq_stats() { reset(); }
        void reset() { memset(this, 0, sizeof(nseq_stats)); }
    };

    // Core state for the nseq solver.
    // All collections use scoped_vector for automatic backtracking.
    class nseq_state {
        ast_manager&             m;
        seq_util&                m_util;
        nseq_dep_manager         m_dm;

        // Constraint stores (backtrackable)
        unsigned                 m_eq_id;
        scoped_vector<nseq_eq>   m_eqs;
        scoped_vector<nseq_ne>   m_neqs;
        scoped_vector<nseq_mem>  m_mems;
        scoped_vector<nseq_pred> m_preds;
        unsigned                 m_preds_head;

        // Axiom queue
        expr_ref_vector          m_axioms;
        obj_hashtable<expr>      m_axiom_set;
        unsigned                 m_axioms_head;
        unsigned                 m_axioms_size_at_push { 0 }; // saved on push, restored on pop

        // Length tracking
        obj_hashtable<expr>      m_has_length;
        expr_ref_vector          m_length_apps;
        expr_ref_vector          m_length_exprs;  // corresponding string exprs

        // Trail for undo
        trail_stack              m_trail;

        nseq_stats               m_stats;

    public:
        nseq_state(ast_manager& m, seq_util& u);

        // Scope management
        void push_scope();
        void pop_scope(unsigned num_scopes);
        void reset();

        // Dependency manager access
        nseq_dep_manager& dm() { return m_dm; }
        nseq_dependency* mk_dep(enode* n1, enode* n2) { return m_dm.mk_leaf(nseq_assumption(n1, n2)); }
        nseq_dependency* mk_dep(literal lit) { return m_dm.mk_leaf(nseq_assumption(lit)); }
        nseq_dependency* mk_join(nseq_dependency* a, nseq_dependency* b) { return m_dm.mk_join(a, b); }

        // Add constraints
        unsigned add_eq(expr* l, expr* r, nseq_dependency* dep);
        void add_ne(expr* l, expr* r, nseq_dependency* dep);
        void add_mem(expr* s, expr* re, bool sign, nseq_dependency* dep);
        void add_pred(nseq_pred_kind kind, expr* a1, expr* a2, bool sign, nseq_dependency* dep);

        // Axiom management
        bool enqueue_axiom(expr* e);
        bool has_pending_axioms() const { return m_axioms_head < m_axioms.size(); }
        unsigned axioms_head() const { return m_axioms_head; }
        void set_axioms_head(unsigned h) { m_axioms_head = h; }
        expr_ref_vector const& axioms() const { return m_axioms; }

        // Length tracking
        bool has_length(expr* e) const { return m_has_length.contains(e); }
        void add_length(expr* len_app, expr* e, trail_stack& ts);
        unsigned length_count() const { return m_length_apps.size(); }

        struct length_pair { expr* len_app; expr* str_expr; };
        class length_pair_iter {
            expr_ref_vector const& m_apps;
            expr_ref_vector const& m_exprs;
        public:
            length_pair_iter(expr_ref_vector const& a, expr_ref_vector const& e) : m_apps(a), m_exprs(e) {}
            struct iterator {
                expr_ref_vector const& m_apps;
                expr_ref_vector const& m_exprs;
                unsigned m_idx;
                iterator(expr_ref_vector const& a, expr_ref_vector const& e, unsigned i) : m_apps(a), m_exprs(e), m_idx(i) {}
                length_pair operator*() const { return { m_apps[m_idx], m_exprs[m_idx] }; }
                iterator& operator++() { ++m_idx; return *this; }
                bool operator!=(iterator const& o) const { return m_idx != o.m_idx; }
            };
            iterator begin() const { return iterator(m_apps, m_exprs, 0); }
            iterator end() const { return iterator(m_apps, m_exprs, m_apps.size()); }
        };
        length_pair_iter length_pairs() const { return length_pair_iter(m_length_apps, m_length_exprs); }

        // Accessors
        scoped_vector<nseq_eq> const& eqs() const { return m_eqs; }
        scoped_vector<nseq_ne> const& neqs() const { return m_neqs; }
        scoped_vector<nseq_mem> const& mems() const { return m_mems; }
        scoped_vector<nseq_pred> const& preds() const { return m_preds; }
        scoped_vector<nseq_pred>& preds() { return m_preds; }
        unsigned preds_head() const { return m_preds_head; }
        void set_preds_head(unsigned h) { m_preds_head = h; }
        trail_stack& trail() { return m_trail; }
        nseq_stats& stats() { return m_stats; }
        nseq_stats const& stats() const { return m_stats; }

        // Linearize dependencies for conflict/propagation
        void linearize(nseq_dependency* dep, enode_pair_vector& eqs, literal_vector& lits) const;

        // Display
        std::ostream& display(std::ostream& out) const;
    };
}
