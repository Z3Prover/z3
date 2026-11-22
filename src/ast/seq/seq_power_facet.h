/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_power_facet.h

Abstract:

    Sequence power operator (`s^n`, `seq.power`) facet.

    `power_facet` stores pending obligations `e = s^n`. Deterministic
    propagation unfolds small known exponents and adds length-only
    consequences for the remaining powers. `power_split` performs the bounded
    case split for symbolic exponents by branching over `n <= 0`,
    `n = 1..bound`, and a residual `n > bound` case.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include <algorithm>

namespace seq {

    // One pending power obligation `m_e = m_s ^ m_n`, with its own derivation.
    struct str_power {
        expr_ref             m_e;
        expr_ref             m_s;
        expr_ref             m_n;
        eq_tree::dep_tracker  m_dep;
        proof_ref            m_proof;
        // Set once this obligation's length axioms have
        // been asserted into `solver_facet`.
        bool                 m_axiomatized = false;

        // power_split has taken its residual `n > bound` branch: the obligation stays
        // pending for the other rules, power_split does not re-enumerate it. Trailed.
        bool                 m_split_exhausted = false;

        // Append-only representation: removing an obligation just flips
        // `m_active`, so stored indices remain valid across iterator
        // resumptions. Consumers must skip inactive entries.
        bool                 m_active = true;

        str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr, proof* pr = nullptr) :
            m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep), m_proof(pr, m) {}
        expr_ref fact(seq_util& u) const;
        bool active() const { return m_active; }
    };

    /**
     * Facet holding a set of pending `s^n` obligations. See module
     * comment for the propagation/split responsibilities.
     */
    class power_facet : public stx::facet_i, public subst_sink_i {
        ast_manager&    m;
        seq_util&       u;
        arith_util&     a;
        eq_tree::dep_manager_t& m_dm;
        vector<str_power> m_pows;
        unsigned        m_max_unfold = 5; // bound on power_split's case-split unfolding, see module comment

    public:
        power_facet(trail_stack& trail, ast_manager& m, seq_util& u, arith_util& a, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), a(a), m_dm(dm) { dm.set_manager(m); }

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }
        arith_util& get_arith_util() const { return a; }
        eq_tree::dep_manager_t& dm() const { return m_dm; }

        unsigned max_unfold() const { return m_max_unfold; }
        void set_max_unfold(unsigned k) { m_max_unfold = k; }

        // Trailed and idempotent: obligations are keyed by the power term.
        void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr, proof* pr = nullptr, symbol rule = symbol("power-input")) {
            unsigned idx;
            if (find_power(e, idx))
                return;
            str_power p(m, e, s, n, dep, pr);
            if (!pr && m_dm.proofs_enabled())
                p.m_proof = m_dm.mk_proof(rule, p.fact(u));
            m_pows.push_back(p);
            m_trail.push(push_back_trail<str_power>(m_pows));
        }
        // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
        // otherwise. Convenience wrapper for callers scanning terms.
        bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr, proof* pr = nullptr, symbol rule = symbol("power-token-definition")) {
            expr* s = nullptr, *n = nullptr;
            if (!u.str.is_power(e, s, n))
                return false;
            add_power(e, s, n, dep, pr, rule);
            return true;
        }

        vector<str_power> const& powers() const { return m_pows; }

        // Locate the pending obligation whose power term is `e`. Plugins use
        // this to recover the base, exponent, and dependency of an opaque
        // `seq.power` token inside an equation.
        bool find_power(expr* e, unsigned& idx) const {
            for (unsigned i = 0; i < m_pows.size(); ++i) {
                if (!m_pows[i].active())
                    continue;
                if (m_pows[i].m_e.get() == e) {
                    idx = i;
                    return true;
                }
            }
            return false;
        }

        // Drop `idx`'s obligation by flipping `m_active`. Trailed.
        void remove(unsigned idx, symbol rule = symbol("power-discharge"), proof* pr = nullptr);

        // Set one of `str_power`'s flags. Trailed.
        void mark(unsigned idx, bool str_power::* flag);

        // -- subst_sink_i --
        // Register power tokens in `repl`, discharge `var` if it is a power
        // token, and rebase obligations whose base mentions `var`.
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        // -- stx::facet_i --
        stx::facet_i* clone(trail_stack& trail) const override;
        // A standalone power obligation never blocks satisfaction; only a
        // power that still appears in a string constraint does.
        bool is_satisfied() const override { return true; }
        std::ostream& display(std::ostream& out) const override;
    };

    // Deterministic propagation: small known-exponent obligations are
    // unfolded and discharged; remaining obligations get length-only
    // axioms asserted into solver_facet (once). See module comment.
    class power_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;
        struct stats {
            unsigned m_num_propagate = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        power_propagation(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-power-propagate num calls", m_stats.m_num_propagate); }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Unfold a power whose exponent arithmetic has fixed. This is a
    // single-branch split so the model query runs once per node.
    class power_fixed_exp : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        power_fixed_exp(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-fixed-exp"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-power-fixed-exp num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Bounded case-split completeness driver for symbolic exponents: see
    // module comment. A final residual branch `n > bound` (obligation left
    // pending) keeps the split exhaustive.
    class power_split : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            unsigned       m_pow_index;
            unsigned       m_next_j; // next exponent to try (1..bound)
            unsigned       m_bound;
            eq_tree::dep_tracker m_dep;
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
        public:
            iterator(eq_tree::node& n,
                      unsigned pow_index, unsigned bound, eq_tree::dep_tracker dep,
                      ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n),
                m_pow_index(pow_index), m_next_j(1), m_bound(bound), m_dep(dep), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_split(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-power-split num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

    // `X^M . V = Y^N . Z` with two leading powers: for the shorter side,
    // `Y^N = X^M . z` holds iff one of five forms (empty, f1..f4) does.
    class power_trichotomy : public eq_tree::split_plugin_i {
        struct trigger {
            unsigned    m_x_idx;    // power_facet index of the lhs head
            unsigned    m_y_idx;    // power_facet index of the rhs head
            eq_tree::dep_tracker m_dep;
        };
        using branches = svector<std::pair<unsigned, unsigned>>; // (branch 0..9, parameter)

        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        class iterator : public eq_tree::split_iterator_i {
            power_trichotomy const& m_owner;
            eq_tree::node&          m_n;
            trigger                 m_t;
            branches                m_branches;
            unsigned                m_next = 1; // branch 0 is applied by split()
        public:
            iterator(power_trichotomy const& owner, eq_tree::node& n, trigger const& t, branches const& bs) :
                m_owner(owner), m_n(n), m_t(t), m_branches(bs) {}
            bool next(eq_tree::edge& out) override;
        };

        bool find_trigger(eq_tree::node& n, trigger& t) const;
        void enumerate(eq_tree::node& n, trigger const& t, branches& out) const;
        void apply(eq_tree::node& n, trigger const& t, unsigned b, unsigned param) const;

        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

    public:
        power_trichotomy(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-trichotomy"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-power-trichotomy num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Power `U^e` at one end of an equation side whose other side begins,
    // in the same direction, with copies of `U`. Split on `e < count` vs
    // `e >= count` and cancel the common prefix.
    struct elim_trigger {
        unsigned      m_eq_idx = 0;
        bool          m_pow_on_lhs = true;
        bool          m_fwd = true;
        unsigned      m_pow_idx = 0;
        unsigned      m_consumed = 0;
        expr_ref      m_count;
        eq_tree::dep_tracker m_dep;
        elim_trigger(ast_manager& m) : m_count(m) {}
    };

    class power_split_elim : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            elim_trigger   m_t;
            bool           m_done = false;
        public:
            iterator(eq_tree::node& n, elim_trigger const& t) : m_n(n), m_t(t) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_split_elim(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-split-elim"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-power-split-elim num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

    // Peel one copy off a power at a directional end of an equation:
    // `n <= 0` gives `epsilon`; `n >= 1` gives `U . U^(n-1)`. The exposed
    // head of `U` is then handled by the ordinary rules.
    class power_peel : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            unsigned       m_eq_idx;
            bool           m_fwd;
            unsigned       m_pow_idx;
            eq_tree::dep_tracker m_dep;
            bool           m_done = false;
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
        public:
            iterator(eq_tree::node& n, unsigned eq_idx, bool fwd, unsigned pow_idx,
                      eq_tree::dep_tracker dep, ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n), m_eq_idx(eq_idx), m_fwd(fwd), m_pow_idx(pow_idx), m_dep(dep), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_peel(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-peel"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-power-peel num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

    // Variable-vs-power decomposition. Trigger: an equation has a variable
    // `v` at one end of one side and a power token `U^n` at the matching
    // end of the other side, where `U`'s base has decomposable structure.
    //
    // Unlike `power_peel`, which removes only one copy of `U`, this rule
    // decomposes `U`'s base at every possible position and also offers a
    // final branch where `v` extends past the whole power term.
    //
    // Let `t_0, ..., t_{k-1}` be `U`'s base tokens in the direction `v`
    // faces `U^n`. One branch is generated per decomposition position `i`
    // in `0..k-1`, except when position `i-1` is itself a power token and
    // already covers the same boundary:
    //   - if `t_i` is a plain (non-power) token:
    //       `v := U^m . t_0 . t_1 . ... . t_{i-1}`,  side constraint `m>=0`
    //   - if `t_i` is itself a power token `w^e` (base `w`, exponent `e`):
    //       `v := U^m . t_0 . ... . t_{i-1} . w^m'`, fresh `m'` per
    //       target variable, side constraints `m>=0`, `0<=m'<=e`
    // plus one final "extend past the power" branch (non-progress,
    // required for completeness - without it, solutions where `v`'s
    // value is strictly longer than `U^n` itself are unreachable):
    //   `v := U^n . v'` for a fresh `v'`, side constraint `len(v')>=0`
    // (all branches, and the fresh skolems' side constraints, are
    // justified by the equation's own dependency).
    class power_var_decompose : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            expr_ref       m_var;
            expr_ref       m_pow_e;      // the U^n token being decomposed
            expr_ref_vector m_base_toks; // U's own flattened base tokens, in the direction v faces U^n
            expr_ref       m_fresh_m;    // U^m skolem exponent (shared across all branches below)
            bool           m_fwd;
            eq_tree::dep_tracker m_dep;
            unsigned       m_pos = 0;    // next decomposition position to offer, or m_base_toks.size() once exhausted
            bool           m_extend_done = false; // whether the final "extend past" branch has been offered
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
        public:
            iterator(eq_tree::node& n,
                      expr* var, expr* pow_e, expr_ref_vector const& base_toks, expr* fresh_m, bool fwd,
                      eq_tree::dep_tracker dep, ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n), m_var(var, m), m_pow_e(pow_e, m),
                m_base_toks(base_toks), m_fresh_m(fresh_m, m), m_fwd(fwd), m_dep(dep), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_var_decompose(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-var-decompose"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-power-var-decompose num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

    // Generalized power introduction. Trigger: an equation has a variable
    // `v` at one end of one side, and the other side consists of a
    // non-empty ground run followed by the same variable `v` again.
    //
    // The ground run is compressed to its minimal repeating period, then
    // turned into a fresh `base^n`. As in `power_var_decompose`, one
    // branch is generated per decomposition position of the compressed
    // base. There is no separate "extend past" branch here because the
    // reappearance of `v` already closes the cycle.
    class power_gpower_intro : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        arith_util&   a;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            expr_ref       m_var;
            expr_ref       m_pow_e;       // the fresh base^n power token
            expr_ref_vector m_base_toks;  // compressed ground-prefix base tokens, in the direction v faces the cycle
            expr_ref       m_fresh_n;     // base^n skolem exponent (shared across all branches below)
            bool           m_fwd;
            eq_tree::dep_tracker m_dep;
            unsigned       m_pos = 0;
            ast_manager&   m;
            seq_util&      u;
            arith_util&    a;
        public:
            iterator(eq_tree::node& n,
                      expr* var, expr* pow_e, expr_ref_vector const& base_toks, expr* fresh_n, bool fwd,
                      eq_tree::dep_tracker dep, ast_manager& m, seq_util& u, arith_util& a) :
                m_n(n), m_var(var, m), m_pow_e(pow_e, m),
                m_base_toks(base_toks), m_fresh_n(fresh_n, m), m_fwd(fwd), m_dep(dep), m(m), u(u), a(a) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        power_gpower_intro(ast_manager& m, seq_util& u, arith_util& a) :
            m(m), u(u), a(a) {}
        char const* name() const override { return "power-gpower-intro"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-power-gpower-intro num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    private:
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    };

} // namespace seq
