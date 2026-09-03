/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_mem_facet.h

Abstract:

    Positive regular-expression membership facet ("Phase 5" of the modular
    plugin-based search tree design, following `stx::` in
    util/stx_search_tree.h and the `eq_facet`/`deq_facet` and `arith_facet`
    modules).

    A `str_mem` constrains one sequence term against a `seq::view`: either a
    plain membership `<state,null>` meaning the whole term is in the language
    of `state`, or a reach view `<state,target>` meaning the term drives the
    derivative automaton from `state` to `target`.

    This port deliberately keeps the facet small and delegates regex-specific
    search to already-existing components:
      - deterministic discharge / conflict checks use `seq::accepts`,
        `seq::is_dead`, and `seq::live_states`;
      - multi-view landing splits are delegated to `seq_monadic`;
      - substitutions chosen by `word_eq_split` are broadcast here through
        `subst_sink_i`, so pending memberships stay synchronized with the
        shared variable pool.

    Scope note / simplifications relative to the full design:
      - regex factorization (�4.2 of facet-membership.md) is NOT implemented
        in this pass;
      - the variable split is implemented soundly for the `x -> epsilon`
        branch, and the second branch narrows through `seq_monadic` rather
        than porting Nielsen's historical minterm-based partial-automaton
        machinery; this keeps the implementation alphabet-agnostic and
        buildable without introducing a new guard-splitting substrate;
      - monadic landing is implemented for the conjunction of memberships
        currently present in `mem_facet`; it narrows views reported by
        `seq_monadic::iterate()` and leaves exact witness materialization to
        `seq_monadic` itself.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_view.h"
#include "ast/seq/seq_regex_live.h"
#include "ast/seq/seq_monadic.h"
#include "ast/seq/seq_power_facet.h"
#include "ast/seq/seq_arith_facet_i.h"
#include "ast/rewriter/seq_rewriter.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"

namespace seq {

    struct str_mem {
        expr_ref            m_str;
        view                m_view;
        eq_tree::dep_tracker m_dep = nullptr;

        str_mem(ast_manager& m, expr* s, view const& v, eq_tree::dep_tracker dep = nullptr) :
            m_str(s, m), m_view(v), m_dep(dep) {}

        bool is_plain() const { return m_view.is_membership(); }
        bool is_view() const { return m_view.is_reach(); }
    };

    class mem_facet : public stx::facet_i, public subst_sink_i {
        ast_manager&      m;
        seq_util&         u;
        eq_tree::dep_manager_t& m_dm;
        vector<str_mem>   m_mems;

    public:
        mem_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }
        vector<str_mem> const& memberships() const { return m_mems; }

        void add(str_mem const& sm);
        void narrow(unsigned idx, view const& new_view);
        void remove(unsigned idx);
        // Replace `idx`'s own string term wholesale (as opposed to
        // `apply_subst`'s global variable-keyed rewrite): used by
        // plugins that peel/rewrite a single membership's string
        // in-place, e.g. `power_var_num_unwinding_mem`'s power-token
        // peel at a directional end of `m_str`, where the change is not
        // a substitution for some other facet's variable but a direct
        // edit of this one membership's own term.
        void replace(unsigned idx, expr* new_str, eq_tree::dep_tracker dep = nullptr);
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        stx::facet_i* clone(trail_stack& trail) const override;
        unsigned hash() const override;
        bool similar(facet_i const& other) const override;
        bool is_satisfied() const override { return m_mems.empty(); }
    };

    class mem_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&    m;
        seq_util&       u;
        stx::facet_id   m_mem_id;
        seq_rewriter&   m_rw;
        live_states&    m_live;
    public:
        mem_propagation(ast_manager& m, seq_util& u, stx::facet_id mem_id, seq_rewriter& rw, live_states& live) :
            m(m), u(u), m_mem_id(mem_id), m_rw(rw), m_live(live) {}
        char const* name() const override { return "mem-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
    };

    class mem_var_split : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        stx::facet_id m_mem_id;
        stx::facet_id m_eq_id;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            stx::facet_id  m_mem_id;
            stx::facet_id  m_eq_id;
            unsigned       m_mem_index;
            expr*          m_var;
            eq_tree::dep_tracker m_dep;
            bool           m_done = false;
        public:
            iterator(eq_tree::node& n, stx::facet_id mem_id, stx::facet_id eq_id, unsigned mem_index, expr* var, eq_tree::dep_tracker dep = nullptr) :
                m_n(n), m_mem_id(mem_id), m_eq_id(eq_id), m_mem_index(mem_index), m_var(var), m_dep(dep) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        mem_var_split(ast_manager& m, seq_util& u, stx::facet_id mem_id, stx::facet_id eq_id) : m(m), u(u), m_mem_id(mem_id), m_eq_id(eq_id) {}
        char const* name() const override { return "mem-var-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
    };

    // Membership-side analog of `power_var_peel` (seq_power_facet.h),
    // ported from the c3 branch's `seq_nielsen_modifiers.cpp`
    // `apply_var_num_unwinding_mem` (facet-eq-deq.md /
    // facet-membership.md). Trigger pattern: some mem_facet membership's
    // own flattened string has a power token `U^n` at a directional end
    // (front or back) - unlike the eq-side rule, no "opposite side is a
    // variable" check applies, since a membership has only one string
    // operand (see class comment on power_var_peel for the shared
    // two-branch structure this mirrors). Skipped if `n` is already a
    // resolved numeral (power_propagation's known-exponent branch
    // handles that case directly).
    //
    // Branch 1 (n=0): U^n -> epsilon, single side constraint `n=0`
    // (c3's mem-variant uses one `mk_eq(exp_n, zero)` clause, not the
    // eq-variant's two-clause `n>=0 /\ n<=0` - preserved faithfully per
    // rule variant, see facet-eq-deq.md).
    // Branch 2 (n>=1): peel one copy, U^n -> U . U^(n-1) (or reversed,
    // matching directional end), spliced directly into the
    // membership's own string via `mem_facet::replace` (not
    // `broadcast_subst`, since the power token here may be a sub-token
    // of a larger concatenation on the membership's string, and
    // `mem_facet::apply_subst`'s exact-whole-string-match semantics
    // cannot splice a sub-token in place).
    class power_var_peel_mem : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;
        stx::facet_id m_pow_id;
        stx::facet_id m_mem_id;
        stx::facet_id m_arith_id;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            stx::facet_id  m_pow_id;
            stx::facet_id  m_mem_id;
            stx::facet_id  m_arith_id;
            unsigned       m_mem_idx;
            bool           m_fwd;
            unsigned       m_pow_idx;
            eq_tree::dep_tracker m_dep;
            bool           m_done = false;
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
        public:
            iterator(eq_tree::node& n, stx::facet_id pow_id, stx::facet_id mem_id, stx::facet_id arith_id,
                      unsigned mem_idx, bool fwd, unsigned pow_idx,
                      eq_tree::dep_tracker dep, ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n), m_pow_id(pow_id), m_mem_id(mem_id), m_arith_id(arith_id),
                m_mem_idx(mem_idx), m_fwd(fwd), m_pow_idx(pow_idx),
                m_dep(dep), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_var_peel_mem(ast_manager& m, seq_util& u, arith_util& a, stx::facet_id pow_id, stx::facet_id mem_id, stx::facet_id arith_id) :
            m(m), u(u), a(a), m_pow_id(pow_id), m_mem_id(mem_id), m_arith_id(arith_id) {}
        char const* name() const override { return "power-var-peel-mem"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
    };

    class mem_monadic_split : public eq_tree::split_plugin_i {
        ast_manager&      m;
        seq_util&         u;
        stx::facet_id     m_mem_id;
        seq_rewriter&     m_rw;
        trail_stack&      m_trail;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node&             m_n;
            stx::facet_id              m_mem_id;
            seq_monadic                m_mon;
            seq_monadic::iterator      m_it;
            bool                       m_first_pending = true;
            obj_map<expr, seq::view_vector> m_first;

            bool apply_solution(obj_map<expr, seq::view_vector>& sol, eq_tree::edge& out);
        public:
            iterator(eq_tree::node& n, stx::facet_id mem_id, seq_rewriter& rw, trail_stack& trail,
                     vector<str_mem> const& mems);
            bool next(eq_tree::edge& out) override;
            bool has_first() const { return !m_first.empty(); }
        };

    public:
        mem_monadic_split(ast_manager& m, seq_util& u, stx::facet_id mem_id, seq_rewriter& rw, trail_stack& trail) :
            m(m), u(u), m_mem_id(mem_id), m_rw(rw), m_trail(trail) {}
        char const* name() const override { return "mem-monadic"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
    };

}
