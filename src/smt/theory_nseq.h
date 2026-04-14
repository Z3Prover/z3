/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_nseq.h

Abstract:

    ZIPT string solver theory for Z3.
    Implements theory_nseq, a theory plugin for string/sequence constraints
    using the Nielsen transformation graph (Nielsen graph).

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_axioms.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "smt/seq/seq_nielsen.h"
#include "smt/seq/seq_state.h"   // tracked_str_eq, tracked_str_mem
#include "smt/seq/seq_regex.h"
#include "smt/seq_model.h"
#include "smt/nseq_context_solver.h"

namespace smt {

    class theory_nseq : public theory {
        seq_util       m_seq;
        arith_util     m_autil;
        th_rewriter    m_th_rewriter;
        seq_rewriter   m_rewriter;
        arith_value    m_arith_value;
        euf::egraph    m_egraph;  // private egraph (not shared with smt context)
        euf::sgraph    m_sgraph;  // private sgraph
        // m_context_solver must be declared before m_nielsen: its address is passed
        // to the m_nielsen constructor and must remain stable for the object's lifetime.
        context_solver m_context_solver;
        context_solver m_core_solver;
        seq::nielsen_graph m_nielsen;
        seq::axioms m_axioms;
        seq::seq_regex     m_regex;   // regex membership pre-processing
        seq_model     m_model;   // model construction helper

        // propagation queue items (variant over the distinct propagation cases)
        using eq_item   = tracked_str_eq;    // string equality
        using mem_item  = tracked_str_mem;   // regex membership
        struct axiom_item { expr* e; };      // structural axiom for term e

        // TODO: Track unit disequalities and add them to Nielsen graph
        using prop_item = std::variant<eq_item, mem_item, axiom_item>;

        vector<prop_item>       m_prop_queue;
        unsigned                m_prop_qhead = 0;
        unsigned                m_next_mem_id = 0;     // monotone counter for tracked_str_mem ids
        obj_hashtable<expr>     m_axiom_set;   // dedup guard for axiom_item enqueues
        obj_hashtable<expr>     m_no_diseq_set;     // track expressions that should not trigger new disequality axioms
        expr_ref_vector         m_relevant_lengths;     // track variables whose lengths are relevant
        obj_map<expr, unsigned> m_gradient_cache;
        sat::literal_vector     m_nielsen_literals;   // literals created by a Nilsen check

        // statistics
        unsigned m_num_conflicts        = 0;
        unsigned m_num_final_checks     = 0;
        unsigned m_num_length_axioms    = 0;
        bool     m_digits_initialized   = false;

        // map from context enode to private sgraph snode
        obj_map<expr, euf::snode*> m_expr2snode;


        // higher-order terms (seq.map, seq.mapi, seq.foldl, seq.foldli)
        ptr_vector<app>  m_ho_terms;
        unsigned         m_num_ho_unfolds = 0;

        // unhandled boolean string predicates (prefixof, suffixof, contains, etc.)
        unsigned         m_num_unhandled_bool = 0;

        bool has_unhandled_preds() const { return m_num_unhandled_bool > 0; }
        void push_unhandled_pred();

        // required virtual methods
        bool internalize_atom(app* a, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        theory_var mk_var(enode* n) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        theory* mk_fresh(context* ctx) override;
        void display(std::ostream& out) const override;

        // optional overrides
        bool can_propagate() override;
        void propagate() override;
        void init() override;
        void assign_eh(bool_var v, bool is_true) override;
        void relevant_eh(app* n) override;
        final_check_status final_check_eh(unsigned) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void init_model(model_generator& mg) override;
        model_value_proc* mk_value(enode* n, model_generator& mg) override;
        void finalize_model(model_generator& mg) override;
        void validate_model(proto_model& mdl) override;
        void collect_statistics(::statistics& st) const override;

        char const* get_name() const override { return "nseq"; }

        // private helpers
        void populate_nielsen_graph();
        void explain_nielsen_conflict();
        void set_conflict(enode_pair_vector const& eqs, literal_vector const& lits);
        void add_nielsen_assumptions();
        euf::snode* get_snode(expr* e);

        // propagation dispatch helpers
        void propagate_eq(tracked_str_eq const& eq);
        void propagate_pos_mem(tracked_str_mem const& mem);
        void enqueue_axiom(expr* e);
        void dequeue_axiom(expr* e);
        void ensure_length_var(expr* e);

        // higher-order term unfolding
        bool unfold_ho_terms();

        // arithmetic value queries for length reasoning
        bool get_num_value(expr* e, rational& val) const;
        bool lower_bound(expr* e, rational& lo) const;
        bool upper_bound(expr* e, rational& hi) const;
        bool get_length(expr* e, rational& val);
        void add_length_axiom(literal lit);
        bool propagate_length_lemma(literal lit, seq::length_constraint const& lc);
        bool assert_nonneg_for_all_vars();
        bool assert_length_constraints();

        // Regex membership pre-check: for each variable with regex constraints,
        // check intersection emptiness before running DFS.
        //   l_true  → found empty intersection, conflict asserted, return FC_CONTINUE
        //   l_false → all variables' regex constraints satisfiable and no word
        //             equations / disequalities, return FC_DONE (SAT)
        //   l_undef → inconclusive, proceed to DFS
        lbool check_regex_memberships_precheck();

        bool check_length_coherence();

    public:
        theory_nseq(context& ctx);
    };

}
