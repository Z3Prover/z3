/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_nseq.h

Abstract:

    Theory plugin for string/sequence constraints driven by the modular
    `stx::search_tree` engine (util/stx_search_tree.h) with the facets and
    plugins implemented under `ast/seq` and `smt/seq_solver_facet.h`.

    This is modeled after the c3 branch's `theory_nseq` (Nielsen-graph based),
    but replaces the Nielsen-graph/sgraph end-game machinery with the
    `stx::search_tree<unsigned>` engine (`seq::eq_tree`) that is already used
    by the `ast/seq` facet unit tests: `eq_facet`/`deq_facet`/`power_facet`/
    `mem_facet`/`ncontains_facet`/`solver_facet`, propagated/split by the
    already-implemented plugin classes.

    Split-plugin registration order mirrors the priority order in which the
    c3 branch's `nielsen_graph::generate_extensions`
    (smt/seq/seq_nielsen_search.cpp) applies its corresponding rules, for
    every plugin that currently has an analog implemented under `ast/seq`.

    Model construction and other c3-era features that have no analog yet
    (regex factorization, monadic-leaf/landing decomposition beyond
    `mem_monadic_split`, signature split, variable-power-unwinding for
    membership, cycle subsumption, ...) are intentionally deferred/stubbed.

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
     * `smt::theory` subclass driving `seq::eq_tree` (`stx::search_tree<unsigned>`)
     * with the `ast/seq` facets/plugins in place of the c3 branch's
     * Nielsen-graph based end-game.
     *
     * Constraints asserted by the SMT core (`new_eq_eh`/`new_diseq_eh`, and
     * `str.in_re` atoms via `assign_eh`) are queued (mirroring the c3 branch's
     * `m_prop_queue`/`m_prop_qhead`), and drained into a freshly-populated
     * `seq::eq_tree` at each `final_check_eh`: the tree's own facets/plugins
     * are stateless w.r.t. earlier final checks, so the tree is rebuilt (not
     * incrementally reused) each time - this keeps the translation from
     * "current SMT-context assignment" to "search-tree root state" simple and
     * avoids depending on `stx::search_tree`'s push/pop machinery across
     * distinct final-check calls (that machinery is used internally, within
     * one `solve()` call, to support the DFS itself).
     *
     * Because every facet class in `ast/seq` is written directly against the
     * concrete `seq::eq_tree` alias (`stx::search_tree<unsigned>`, not a
     * template parameter), the dependency leaves recorded while populating
     * the tree are plain `unsigned` indices; `theory_nseq` maintains its own
     * side table (`m_assumptions`) mapping each such index back to the real
     * SMT assumption (an enode-equality or a literal) that justified it, so
     * that a tree-level `unsat` conflict can be translated into a genuine
     * SMT conflict clause via `dep_mgr().linearize(...)` + this table.
     */
    class theory_nseq : public theory {
        friend class seq::theory_nseq_ambient_context;

        // One real SMT-level justification underlying a single `unsigned`
        // dependency-leaf value recorded in `seq::eq_tree`'s dependency
        // manager. Mirrors `theory_seq::assumption`.
        //
        // `n1`/`n2` together with `is_diseq` represent either "n1 and n2
        // are equal" (is_diseq == false, from new_eq_eh - already true in
        // the ambient context, since they share an enode class) or "n1
        // and n2 are distinct" (is_diseq == true, from new_diseq_eh -
        // already true in the ambient context, since they are in
        // different enode classes). Neither case needs (or eagerly
        // creates) an equality literal: the corresponding
        // `mk_eq(n1,n2)` atom is only internalized lazily, in
        // report_conflict, if this assumption actually participates in
        // a conflict.
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
        th_rewriter         m_th_rewriter; // band-aid: normalizes `e` (e.g. folds
                                            // str.len(unit(a)++x) into 1 + str.len(x))
                                            // before querying m_arith_value, so bound/
                                            // value queries reach the same term shape
                                            // the SMT core's own preprocessing produced
                                            // and internalized.
        arith_value         m_arith_value;
        expr_ref_vector     m_pin; // pins fresh terms (e.g. complemented regexes, Skolem
                                   // fresh existentials for prefix/suffix/contains
                                   // axiomatization) built while adding constraints that
                                   // are not otherwise owned by the calling context.

        // Axiomatization of string operations that are reduced to more
        // basic constraints (length/index/replace/extract/at/nth/itos/
        // stoi/lt/le/unit/is_digit/from_code/to_code, and negated
        // prefix/suffix, following theory_seq's m_ax/enque_axiom/
        // deque_axiom pattern - see theory_seq.h/.cpp). Unlike
        // theory_seq, axioms are drained via can_propagate/propagate
        // (not final_check_eh), consistent with the rest of theory_nseq's
        // "apply as soon as noticed" style; the axioms themselves are
        // solver-independent term rewrites (m_ax.add_*), so draining them
        // eagerly rather than at final_check has no effect on soundness.
        smt::seq_axioms     m_ax;
        seq::skolem         m_sk; // recognizes m_sk.is_eq-tagged internal equality
                                   // atoms (see assign_eh's m_sk.is_eq branch);
                                   // shares no state with m_ax's own private skolem
                                   // instance, matching theory_seq's own separate
                                   // m_sk member.
        expr_ref_vector     m_axioms;      // queue of terms awaiting axiomatization
        obj_hashtable<expr> m_axiom_set;   // dedup guard for m_axioms enqueues
        unsigned            m_axioms_head = 0; // index of first axiom still to add

        seq::eq_tree                     m_tree;
        seq::eq_tree::node*              m_root = nullptr;
        seq::sub_solver             m_solver;
        scoped_ptr<seq::theory_nseq_ambient_context> m_ambient;
        scoped_ptr<seq_factory>          m_factory;
        obj_map<expr, expr*>             m_model_subst;

        // Facet ids are registered once in the constructor and handed to
        // m_ambient (set_eq_id() etc.); they are not kept as members
        // here - all facet access goes through m_ambient's own id
        // accessors / facet_as-style helpers (e.g. m_ambient->eq_facet(n)).

        // Propagation and split plugins are no longer stored as members:
        // `stx::search_tree::add_propagation_plugin`/`add_split_plugin`
        // now take ownership of a heap-allocated plugin (stored in the
        // tree's own `scoped_ptr_vector`s, deallocated with the tree), so
        // the constructor allocates each with `alloc(...)` and hands it
        // straight to the tree - see theory_nseq.cpp. Registration order
        // (in the constructor) mirrors the priority order of
        // `nielsen_graph::generate_extensions` (seq_nielsen_search.cpp)
        // for every plugin that has a current analog:
        //   priority 2   apply_power_epsilon        -> (folded into power_propagation)
        //   (refutation gate)  seq_eq_approx (view-segment intersection) -> eq_approx_split
        //   (refutation gate)  seq_parikh (length/period feasibility)    -> mem_parikh_split
        //   priority 3   apply_num_cmp               -> power_num_cmp
        //   priority 3b  apply_split_power_elim       -> power_split_elim
        //   priority 3c  apply_fine_wilf              -> power_fine_wilf
        //   priority 4   apply_const_num_unwinding    -> power_var_peel
        //   priority 5   apply_eq_split               -> eq_split
        //   priority 5d  apply_monadic_landing        -> mem_monadic_split
        //   priority 7   apply_gpower_intr            -> power_gpower_intro
        //   priority 8b  apply_const_nielsen          -> word_eq_split (const/var)
        //   priority 9   apply_regex_if_split         -> (removed; ite tokens treated as ordinary Nielsen variables, see ambient_context_i::is_var)
        //   priority 10  apply_regex_var_split        -> (removed; see mem_var_split removal note in seq_mem_facet.h)
        //   priority 11  apply_power_split            -> power_split
        //   priority 12  apply_var_nielsen            -> word_eq_split (var/var)
        //   (disequality unwinding)                   -> deq_split
        //   (membership power peel)                   -> power_var_peel_mem


        // Constraints are added directly to the ambient facets as soon as
        // the SMT core notifies us (new_eq_eh/new_diseq_eh/assign_eh), not
        // queued and drained at final_check_eh time: every facet's own
        // trail is the shared `ctx.get_trail_stack()` (see m_tree's
        // constructor), so a constraint added at scope level `k` is
        // automatically retracted on pop_scope_eh back below `k`, exactly
        // like any other trailed mutation. `m_assumptions` (below) is the
        // corresponding side table and is itself scoped the same way, via
        // `push_back_vector` in `mk_dep`.
        vector<assumption> m_assumptions;

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

        // Model construction reads the SAT snapshot left by the search
        // tree: eq_facet supplies the accumulated triangular
        // substitutions, while mem_facet/seq_monadic-simplified views
        // provide regex witnesses for any variable left unsolved by the
        // equational part. Remaining unconstrained variables receive a
        // fresh sequence value from seq_factory.
        bool build_models() const override { return true; }

        char const* get_name() const override { return "nseq"; }

        // helpers
        void report_conflict(seq::eq_tree::dep_tracker dep);
        unsigned mk_dep(assumption const& a);
        void pin(expr* e) { m_pin.push_back(e); ctx.push_trail(push_back_vector(m_pin)); }
        void enqueue_axiom(expr* e);
        void dequeue_axiom(expr* e);

        // Mirrors theory_seq::propagate_eq: propagates an equality
        // e1 = e2 directly into the SMT core (ctx.assign_eq), justified
        // by lit (the m_sk.is_eq-tagged atom's literal, now true). Returns
        // false (no-op) if e1/e2 already share an enode root. Since
        // theory_nseq has no `new_eq_eh`-fed solved-form bookkeeping of
        // its own beyond the eq_tree/facet machinery (already driven by
        // the ordinary new_eq_eh callback once ctx.assign_eq triggers
        // congruence closure), no separate "add_to_eqs" step is needed
        // here (unlike theory_seq's own bookkeeping-heavy variant).
        bool propagate_eq(literal lit, expr* e1, expr* e2);

        bool get_num_value(expr* e, rational& val) const;
        bool lower_bound(expr* e, rational& lo) const;
        bool upper_bound(expr* e, rational& hi) const;

    public:
        theory_nseq(context& ctx);
        ~theory_nseq() override = default;
    };

}
