/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_nseq.h

Abstract:

    Theory plugin for string and sequence constraints driven by the
    modular `stx::search_tree` engine and the facets under `ast/seq`.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/expr_substitution.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_power_facet.h"
#include "ast/seq/seq_mem_facet.h"
#include "ast/seq/seq_monadic.h"
#include "ast/seq/seq_ncontains_facet.h"
#include "ast/seq/seq_req_facet.h"
#include "ast/seq/seq_lex_facet.h"
#include "ast/seq/seq_stoi_facet.h"
#include "ast/seq/seq_ho_facet.h"
#include "ast/seq/seq_regex_live.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "smt/seq_solver_facet.h"
#include "smt/seq_axioms.h"
#include "model/seq_factory.h"
#include "util/trail.h"

namespace seq {
    class theory_nseq_ambient_context;
}

namespace smt {

    /**
     * `smt::theory` subclass driving `seq::eq_tree`.
     *
     * The search tree is rebuilt at each `final_check_eh` from the
     * current SMT assignment. Tree dependencies are stored as `unsigned`
     * leaves and mapped back through `m_assumptions` when a tree-level
     * conflict is reported to the SMT core.
     */
    class theory_nseq : public theory {
        friend class seq::theory_nseq_ambient_context;
        class seq_model_value_proc;

        // One SMT-level justification backing a single dependency leaf.
        // Equality and disequality assumptions are represented by enodes;
        // the corresponding equality literal is internalized lazily only
        // if it is needed in a conflict clause.
        struct assumption {
            enode* n1 = nullptr, *n2 = nullptr;
            bool is_diseq = false;
            literal lit = null_literal;
            assumption() = default;
            assumption(enode* n1, enode* n2, bool is_diseq = false) : n1(n1), n2(n2), is_diseq(is_diseq) {}
            assumption(literal lit) : lit(lit) {}
        };

        seq_util           m_seq;
        arith_util          m_autil;
        seq_rewriter        m_rewriter;
        th_rewriter         m_th_rewriter; // normalize arithmetic terms before querying m_arith_value
        arith_value         m_arith_value;
        expr_ref_vector     m_pin; // owns fresh helper terms built while adding constraints

        // Axiomatization of string operations reduced to simpler
        // constraints. The queue is drained eagerly via
        // can_propagate/propagate.
        smt::seq_axioms     m_ax;
        seq::skolem         m_sk; // recognizes internal equality atoms
        expr_ref_vector     m_axioms;      // queue of terms awaiting axiomatization
        obj_hashtable<expr> m_axiom_set;   // dedup guard for m_axioms enqueues
        unsigned            m_axioms_head = 0; // index of first axiom still to add

        // Index of the first assigned literal not yet forwarded to
        // flush_assigned_literals(). Trailed so backtracking rewinds it.
        unsigned            m_lits_qhead = 0;

        seq::eq_tree                     m_tree;
        seq::eq_tree::node*              m_root = nullptr;
        seq::sub_solver             m_solver;
        scoped_ptr<seq::theory_nseq_ambient_context> m_ambient;
        // Non-owning handle used to reset per-solve mem_leaf state.
        seq::mem_leaf_split*             m_mem_leaf = nullptr;
        seq_factory*                     m_factory = nullptr; // owned by the model's plugin_manager once registered
        obj_map<expr, expr*>             m_model_subst;
        // Keeps witness terms referenced by m_model_subst alive.
        expr_ref_vector                  m_model_pin;

        // Counter for distinct marker characters used in fresh model values.
        unsigned                         m_next_fresh_len_marker = 0;

        // Facet ids live in m_ambient; plugins are owned by m_tree.

        // Constraints are fed into facets as soon as the SMT core reports
        // them. Facet state and m_assumptions are trailed with the shared
        // SMT trail stack.
        vector<assumption> m_assumptions;

        // Assumptions required by the current SAT snapshot but not yet
        // assigned true in the ambient context.
        literal_vector m_pending_assumptions;

        unsigned m_num_conflicts = 0;
        unsigned m_num_final_checks = 0;

        // required virtual methods
        bool internalize_atom(app* atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        theory_var mk_var(enode* n) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        theory* mk_fresh(context* new_ctx) override;
        void display(std::ostream& out) const override;

        // optional overrides
        void init() override;
        void assign_eh(bool_var v, bool is_true) override;
        void relevant_eh(expr* n) override;
        bool can_propagate() override;
        void propagate() override;
        final_check_status final_check_eh(unsigned) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void collect_statistics(::statistics& st) const override;
        void init_model(model_generator& mg) override;
        void finalize_model(model_generator& mg) override;
        model_value_proc* mk_value(enode* n, model_generator& mg) override;

        // Build models from the SAT snapshot left by the search tree.
        bool build_models() const override { return true; }

        char const* get_name() const override { return "nseq"; }

        // helpers
        void report_conflict(seq::eq_tree::dep_tracker dep);
        unsigned mk_dep(assumption const& a);
        void pin(expr* e) { m_pin.push_back(e); ctx.push_trail(push_back_vector(m_pin)); }
        void enqueue_axiom(expr* e);
        void dequeue_axiom(expr* e);

        // Forward relevant assigned literals into solver_facet's backend,
        // skipping sequence-theory atoms already handled by assign_eh.
        // The cursor is trailed so backtracking replays literals in sync
        // with solver_facet's backend scopes.
        void flush_assigned_literals();

        // Propagate e1 = e2 into the SMT core, justified by `lit`.
        bool propagate_eq(literal lit, expr* e1, expr* e2);

        bool get_num_value(expr* e, rational& val);
        bool lower_bound(expr* e, rational& lo);
        bool upper_bound(expr* e, rational& hi);

        // Ask stoi_facet to instantiate any newly enabled coherence axioms.
        bool check_stoi_coherence();
        bool add_ho_eq(expr* lhs, expr* rhs);
        bool find_ho_elaboration(expr* term, expr*& elaboration) const;
        void ensure_length_var(expr* e) const;

    public:
        theory_nseq(context& ctx);
        ~theory_nseq() override = default;
    };

}
