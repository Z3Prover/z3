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

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_power_facet.h"
#include "ast/seq/seq_mem_facet.h"
#include "ast/seq/seq_ncontains_facet.h"
#include "ast/seq/seq_regex_live.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "smt/seq_solver_facet.h"
#include "util/trail.h"
#include <variant>

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
        struct assumption {
            enode* n1 = nullptr, *n2 = nullptr;
            literal lit = null_literal;
            assumption() = default;
            assumption(enode* n1, enode* n2) : n1(n1), n2(n2) {}
            assumption(literal lit) : lit(lit) {}
        };

        seq_util           m_seq;
        arith_util          m_autil;
        seq_rewriter        m_rewriter;
        arith_value         m_arith_value;
        seq::live_states    m_live;

        seq::eq_tree                     m_tree;
        seq::eq_tree::node*              m_root = nullptr;
        seq::arith_sub_solver             m_solver;
        scoped_ptr<seq::theory_nseq_ambient_context> m_ambient;

        stx::facet_id m_eq_id = 0;
        stx::facet_id m_deq_id = 0;
        stx::facet_id m_arith_id = 0;
        stx::facet_id m_pow_id = 0;
        stx::facet_id m_mem_id = 0;
        stx::facet_id m_nc_id = 0;

        // propagation plugins (priority 1-ish, deterministic; order among
        // these does not matter to `stx::search_tree`, which runs
        // propagation to fixpoint before ever consulting a split plugin).
        seq::eq_propagation          m_eq_prop;
        seq::deq_propagation         m_deq_prop;
        seq::arith_propagation       m_arith_prop;
        seq::power_propagation       m_pow_prop;
        seq::mem_propagation         m_mem_prop;
        seq::mem_bounds_propagation  m_mem_bounds_prop;
        seq::ncontains_propagation   m_nc_prop;

        // split plugins, members so `add_split_plugin` pointers stay valid
        // across final checks; registration order (in the constructor)
        // mirrors the priority order of `nielsen_graph::generate_extensions`
        // (seq_nielsen_search.cpp) for every plugin that has a current analog:
        //   priority 2   apply_power_epsilon        -> (folded into power_propagation)
        //   priority 3   apply_num_cmp               -> power_num_cmp
        //   priority 3b  apply_split_power_elim       -> power_split_elim
        //   priority 3c  apply_fine_wilf              -> power_fine_wilf
        //   priority 4   apply_const_num_unwinding    -> power_var_peel
        //   priority 5   apply_eq_split               -> eq_split
        //   priority 5d  apply_monadic_landing        -> mem_monadic_split
        //   priority 7   apply_gpower_intr            -> power_gpower_intro
        //   priority 8b  apply_const_nielsen          -> word_eq_split (const/var)
        //   priority 9   apply_regex_if_split         -> ite_split
        //   priority 10  apply_regex_var_split        -> (removed; see mem_var_split removal note in seq_mem_facet.h)
        //   priority 11  apply_power_split            -> power_split
        //   priority 12  apply_var_nielsen            -> word_eq_split (var/var)
        //   (disequality unwinding)                   -> deq_split
        //   (membership power peel)                   -> power_var_peel_mem
        seq::power_num_cmp        m_pow_num_cmp;
        seq::power_split_elim     m_pow_split_elim;
        seq::power_fine_wilf      m_pow_fine_wilf;
        seq::power_var_peel       m_pow_var_peel;
        seq::eq_split             m_eq_split;
        seq::mem_monadic_split    m_mem_monadic_split;
        seq::power_gpower_intro   m_pow_gpower_intro;
        seq::word_eq_split        m_word_eq_split;
        seq::ite_split            m_ite_split;
        seq::power_split          m_pow_split;
        seq::power_var_decompose  m_pow_var_decompose;
        seq::power_var_peel_mem   m_pow_var_peel_mem;
        seq::deq_split            m_deq_split;

        // pending-assertion queue, drained into the tree at final_check_eh.
        struct eq_item   { enode* n1, *n2; };
        struct deq_item  { enode* n1, *n2; literal lit; };
        struct mem_item  { enode* s, *re; literal lit; bool positive; };
        using prop_item = std::variant<eq_item, deq_item, mem_item>;
        vector<prop_item>  m_prop_queue;
        unsigned           m_prop_qhead = 0;

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
        final_check_status final_check_eh(unsigned) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void collect_statistics(::statistics& st) const override;

        // model construction is deferred: no facilities exist yet to turn a
        // `seq::eq_tree` sat-snapshot into a `smt::model`. `build_models()`
        // returning false tells `model_generator::mk_value_procs` to *not*
        // dispatch to `mk_value` for enodes owning an `nseq` theory_var
        // (which would otherwise assert/crash, since no `mk_value` override
        // exists); the core instead synthesizes an arbitrary fresh value for
        // them, matching the `theory_dummy` convention for theories that do
        // not (yet) build models.
        bool build_models() const override { return false; }

        char const* get_name() const override { return "nseq"; }

        // helpers
        void enqueue(prop_item const& item);
        void populate_tree();
        unsigned mk_dep(assumption const& a);
        void report_conflict(seq::eq_tree::dep_tracker dep);

        bool get_num_value(expr* e, rational& val) const;
        bool lower_bound(expr* e, rational& lo) const;
        bool upper_bound(expr* e, rational& hi) const;

    public:
        theory_nseq(context& ctx);
        ~theory_nseq() override = default;
    };

}
