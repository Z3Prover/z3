/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic.h

Abstract:

    Continuation-regex split service and intersection non-emptiness for regular
    expressions, following the design sketched in
    paper/bench/eval/monadic-vs-nielsen-eval.md.

      * A continuation regex  <R, N>  (seq::cont_regex) is a pair of regexes.  R is
        the start state and N is the accept state.  A word w is accepted iff
        delta_w(R) == N, with one distinguished case: when N is the epsilon regex
        (the regex accepting the empty sequence) acceptance is ordinary membership
        w in L(R), i.e. delta_w(R) is nullable.  This is because the Brzozowski
        derivative folds the epsilon tail into nullability (the epsilon state is not
        structurally reachable for looping nullable regexes).  Every regex R is
        embedded as the continuation regex  <R.epsilon, epsilon>.

      * seq::split exposes, for a continuation regex, an (opaque) iterator of
        seq::split_pair splits:   uv in <R,N>  ==>  u in <R,R'> /\ v in <R',N>,
        where R' ranges over the live cofactors of R that can still reach N.

      * seq::split_manager owns the live-state / reachability machinery shared across
        regexes, and decides emptiness of an intersection of continuation regexes.
        It maintains one global derivative-transition graph and recycles the states
        (and their computed nullability / cofactor successors) across every regex it
        processes, so the same derivative is never recomputed.

    The module is element-sort agnostic: it does NOT hard-code any character
    reasoning.  Guard feasibility and successor computation are delegated entirely
    to the symbolic derivative engine (seq_rewriter::brz_derivative_cofactors, which
    prunes infeasible guards internally and, on an re.inter, yields the product
    successor in source order) and to th_rewriter for normalization.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/
#pragma once

#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "util/lbool.h"
#include "util/obj_hashtable.h"
#include "util/vector.h"
#include <utility>

namespace seq {

    // A continuation regex <R, N>: start state R, accept state N.  A word w is
    // accepted iff delta_w(R) == N.  When N is the epsilon regex (or null), the
    // accept condition is ordinary membership (delta_w(R) is nullable).
    typedef std::pair<expr_ref, expr_ref> cont_regex;

    // A split of  uv in <R,N>  into  u in <R,R'>  and  v in <R',N>.
    typedef std::pair<cont_regex, cont_regex> split_pair;

    class split_manager;

    // Opaque, lazy iterator over the splits of a continuation regex.  The internal
    // state (the enumerated midpoints R') is computed on construction.  `failed()`
    // reports a non-ground regex or a resource limit reached while computing
    // derivatives.
    class split_iterator {
        friend class split;
        split_manager*   m_sm = nullptr;
        expr*            m_R = nullptr;     // start state of the continuation regex
        expr*            m_N = nullptr;     // accept state (epsilon/null => membership)
        ptr_vector<expr> m_mids;            // enumerated live midpoints R'
        unsigned         m_pos = 0;         // current midpoint index
        bool             m_failed = false;  // non-ground regex / resource limit

        split_iterator(split_manager& sm, cont_regex const& cr);   // begin

        bool at_end() const { return m_failed || m_pos >= m_mids.size(); }

    public:
        split_iterator() = default;                                // end sentinel

        split_pair operator*() const;
        split_iterator& operator++();
        bool operator==(split_iterator const& other) const { return at_end() && other.at_end(); }
        bool operator!=(split_iterator const& other) const { return !(*this == other); }
        bool failed() const { return m_failed; }
    };

    // A continuation regex together with the manager that can split it.
    class split {
        split_manager& m_sm;
        expr_ref       m_R;
        expr_ref       m_N;
    public:
        split(split_manager& sm, expr* r);
        split(split_manager& sm, cont_regex const& cr);
        split_iterator begin();
        split_iterator end() { return split_iterator(); }
    };

    // Manages live states / abstract reachability across the regexes it processes,
    // and decides emptiness of intersections of continuation regexes.  One global
    // derivative-transition graph is grown lazily and shared across every regex, so
    // states, their nullability and their cofactor successors are computed once.
    class split_manager {
        friend class split;
        friend class split_iterator;

        // A cofactor transition of the global graph: on a guard (a predicate over the
        // element variable (:var 0)) the derivative moves to the target state.
        struct gedge { expr* guard; unsigned target; };

        ast_manager&    m;
        seq_rewriter&   m_rw;
        th_rewriter     m_th;                   // regex normalization (element-sort agnostic)
        expr_ref_vector m_pin;                  // keeps interned states / guards alive

        // Global reachability graph, reused across every processed regex.
        obj_map<expr, unsigned> m_state_id;     // regex state -> global id
        ptr_vector<expr>        m_gstate;       // global id  -> state
        bool_vector             m_gmaybe_null;  // per state: !is_false(is_nullable)
        bool_vector             m_gexpanded;    // per state: cofactor successors computed
        vector<svector<gedge>>  m_gsucc;        // per state: (guard, target) edges

        seq_util&      u() const { return m_rw.u(); }
        seq_util::rex& re() const { return m_rw.u().re; }

        // Tri-state nullability of a state: l_true / l_false when the derivative
        // engine decides it, l_undef when it cannot.
        lbool nullable(expr* s);

        // Intern a state into the global graph (recycles an existing global state),
        // computing its nullability lazily.  Returns its global id.
        unsigned intern_state(expr* s);

        // Compute (once) the cofactor successors of the global state `i`, recycling
        // any target states already present in the graph.  Sets `ok` false on a
        // resource limit.
        void expand_state(unsigned i, bool& ok);

        // Reachable derivative states of R with their transition graph and per-state
        // (possible) nullability, projected out of the global graph.  Sets `ok` false
        // on cap overrun / resource limit.
        void build_graph(expr* R, ptr_vector<expr>& states,
                         vector<svector<unsigned>>& succ, bool_vector& maybe_null, bool& ok);

        // Live reachable derivative states of R (can reach a nullable state).
        void live_states(expr* R, ptr_vector<expr>& out, bool& ok);

        // Reachable derivative states of R from which the state N is reachable.
        void reaching_states(expr* R, expr* N, ptr_vector<expr>& out, bool& ok);

        // Non-emptiness of an all-membership intersection: BFS over the normalized
        // product state inter(R_0,...,R_{n-1}) with an is_nullable acceptance test.
        lbool intersect_membership(vector<cont_regex> const& crs, unsigned lo, unsigned hi,
                                   expr_ref_vector& seq);

        // Product-reachability of a tuple of continuation regexes (handles general N,
        // i.e. reach targets N != epsilon), decomposing the engine's product successor.
        lbool intersect_product(vector<cont_regex> const& crs, unsigned lo, unsigned hi,
                                expr_ref_vector& seq);

    public:
        split_manager(seq_rewriter& rw)
            : m(rw.m()), m_rw(rw), m_th(rw.m()), m_pin(rw.m()) {}

        ast_manager&   mgr() const { return m; }
        seq_rewriter&  rw() const { return m_rw; }

        void pin(expr* e) { m_pin.push_back(e); }

        // Embed a regex R as the continuation regex <R.epsilon, epsilon>.  The
        // epsilon accept-state marks the membership (nullable) case uniformly.
        cont_regex embed(expr* r) {
            sort* ss = nullptr;
            VERIFY(u().is_re(r, ss));
            expr_ref eps(re().mk_epsilon(ss), m);
            expr_ref start(re().mk_concat(r, eps), m);
            return cont_regex(start, eps);
        }

        split mk_split(expr* r) { return split(*this, r); }
        split mk_split(cont_regex const& cr) { return split(*this, cr); }

        // Emptiness of the intersection of the continuation regexes `crs`, restricted
        // to words of at least `lo` and at most `hi` elements (hi == UINT_MAX for no
        // upper bound).  A component <R_i, N_i> accepts a word w iff delta_w(R_i) == N_i,
        // where an epsilon (or null) N_i means the nullable/membership case.  Feasibility
        // is decided by the derivative engine (element-sort agnostic).  On l_true a
        // witness is returned in `seq`: one guard predicate over (:var 0) per position.
        //   l_false = empty, l_true = non-empty, l_undef = gave up
        //   (cap overrun, undecidable nullability, or a product target that could not
        //    be decomposed).
        lbool intersect(vector<cont_regex> const& crs, unsigned lo, unsigned hi, expr_ref_vector& seq);

        // Cheap, sound one-sided partial check: false only when the intersection is
        // certainly empty; true otherwise (may be a false positive).
        bool test_intersect(vector<cont_regex> const& crs);
    };
}
