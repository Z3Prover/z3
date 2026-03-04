/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_nseq.h

Abstract:

    ZIPT string solver theory for Z3.
    Implements theory_nseq, a theory plugin for string/sequence constraints
    using the Nielsen transformation graph (Nielsen graph).

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "smt/seq/seq_nielsen.h"
#include "smt/nseq_state.h"
#include "smt/nseq_regex.h"
#include "smt/nseq_model.h"

namespace smt {

    class theory_nseq : public theory {
        seq_util       m_seq;
        arith_util     m_autil;
        seq_rewriter   m_rewriter;
        arith_value    m_arith_value;
        euf::egraph    m_egraph;  // private egraph (not shared with smt context)
        euf::sgraph    m_sgraph;  // private sgraph
        seq::nielsen_graph m_nielsen;
        nseq_state     m_state;
        nseq_regex     m_regex;   // regex membership pre-processing
        nseq_model     m_model;   // model construction helper

        // propagation queue
        struct prop_item {
            enum kind_t { eq_prop, diseq_prop, pos_mem_prop, neg_mem_prop } m_kind;
            unsigned m_idx;
        };
        svector<prop_item>  m_prop_queue;
        unsigned            m_prop_qhead = 0;
        unsigned_vector     m_prop_lim;   // saved queue sizes for push/pop

        // statistics
        unsigned m_num_conflicts        = 0;
        unsigned m_num_final_checks     = 0;
        unsigned m_num_length_axioms    = 0;

        // map from context enode to private sgraph snode
        obj_map<expr, euf::snode*> m_expr2snode;

        // mapping from nielsen mem index to state mem index
        // (populated during populate_nielsen_graph, used in deps_to_lits)
        unsigned_vector m_nielsen_to_state_mem;

        // higher-order terms (seq.map, seq.mapi, seq.foldl, seq.foldli)
        ptr_vector<app>  m_ho_terms;
        unsigned_vector  m_ho_lim;        // push/pop limits for m_ho_terms
        unsigned         m_num_ho_unfolds = 0;

        // unhandled boolean string predicates (prefixof, suffixof, contains, etc.)
        unsigned         m_num_unhandled_bool = 0;
        unsigned_vector  m_unhandled_bool_lim;

        bool has_unhandled_preds() const { return m_num_unhandled_bool > 0; }

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
        void deps_to_lits(seq::dep_tracker const& deps, enode_pair_vector& eqs, literal_vector& lits);
        void add_conflict_clause(seq::dep_tracker const& deps);
        void set_conflict(enode_pair_vector const& eqs, literal_vector const& lits);
        euf::snode* get_snode(expr* e);

        // propagation dispatch helpers
        void propagate_eq(unsigned idx);
        void propagate_diseq(unsigned idx);
        void propagate_pos_mem(unsigned idx);
        void propagate_neg_mem(unsigned idx);
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

    public:
        theory_nseq(context& ctx);
    };

}
