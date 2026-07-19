/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic.cpp

Abstract:

    Continuation-regex split service and intersection non-emptiness.  See
    seq_monadic.h.

    Automaton-based (product/derivative reachability) and element-sort agnostic:
    guard feasibility and successor states are computed entirely by the symbolic
    derivative engine (seq_rewriter::brz_derivative_cofactors, which prunes
    infeasible guards internally), so there is no character-specific reasoning in
    this module.  A single global derivative-transition graph is grown lazily and
    recycled across every regex, so no derivative is computed twice.  th_rewriter is
    used to normalize the intersection regex.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

Shady parts:

- witness extraction is buggy. It should generally rely on a choice function that takes a
  Boolean expression F[(:var 0)] with a single free variable and synthesize a value for the free
  variable such that the expression is true. 
  For character predicates we can assume that the Boolean expressions are range predicates and we can 
  use utilities for range predicates. For other types use some best effort, say F is of the form (= (:var 0) value).
  Expose the witness function in a self-contained module outside of this file.

- checking intersections with continuation regexes is shady. The nullability check is now really about
  whether there is an epsilon transition to the accepting state N. The copilot-generated code ignores this.
  Generally, dealing with epsilon state is shady. There are many equivalent ways a state can be epsilon, such
  as epsilon*, or comp(.+), etc.

--*/

#include "ast/rewriter/seq_monadic.h"
#include <set>
#include <vector>
#include <climits>

namespace seq {

    // ------------------------------------------------------------------
    //  global derivative-transition graph (shared / recycled across regexes)
    // ------------------------------------------------------------------

    unsigned split_manager::intern_state(expr* s) {
        unsigned id;
        if (m_state_id.find(s, id))
            return id;                            // recycle the global state
        id = m_gstate.size();
        m_state_id.insert(s, id);
        m_gstate.push_back(s);
        m_pin.push_back(s);
        expr_ref nb = m_rw.is_nullable(s);
        m_gmaybe_null.push_back(!m.is_false(nb)); // unknown nullability => keep (conservative)
        m_gexpanded.push_back(false);
        m_gsucc.push_back(svector<gedge>());
        return id;
    }

    void split_manager::expand_state(unsigned i, bool& ok) {
        ok = true;
        if (m_gexpanded[i])
            return;                               // successors already computed once
        if (!m.inc()) { ok = false; return; }
        expr* s = m_gstate[i];                    // captured before any interning realloc
        expr_ref_pair_vector cof(m);
        m_rw.brz_derivative_cofactors(s, cof);
        svector<gedge> edges;
        for (auto const& [g, t] : cof) {
            if (re().is_empty(t)) continue;       // engine already pruned infeasible guards
            unsigned k = intern_state(t);         // may realloc m_gsucc: collect edges first
            m_pin.push_back(g);
            edges.push_back(gedge{ g, k });
        }
        for (gedge const& e : edges)              // m_gsucc stable now (no more interning)
            m_gsucc[i].push_back(e);
        m_gexpanded[i] = true;
    }

    // ------------------------------------------------------------------
    //  live-state / reachability machinery (projected out of the global graph)
    // ------------------------------------------------------------------

    void split_manager::build_graph(expr* R, ptr_vector<expr>& states,
                                    vector<svector<unsigned>>& succ,
                                    bool_vector& maybe_null, bool& ok) {
        ok = true;
        states.reset();
        succ.reset();
        maybe_null.reset();
        obj_map<expr, unsigned> local;            // state expr -> local index
        svector<unsigned> l2g;                    // local index -> global id
        auto local_of = [&](expr* s) -> unsigned {
            unsigned li;
            if (local.find(s, li)) return li;
            unsigned gid = intern_state(s);
            li = states.size();
            local.insert(s, li);
            l2g.push_back(gid);
            states.push_back(s);
            maybe_null.push_back(m_gmaybe_null[gid]);
            succ.push_back(svector<unsigned>());
            return li;
        };
        local_of(R);
        const unsigned STATE_CAP = 1u << 12;
        for (unsigned i = 0; i < states.size(); ++i) {
            if (states.size() > STATE_CAP || !m.inc()) { ok = false; return; }
            unsigned gid = l2g[i];
            expand_state(gid, ok);
            if (!ok) return;
            svector<unsigned> tgts;               // snapshot: local_of may realloc m_gsucc
            for (edge const& e : m_gsucc[gid])
                tgts.push_back(e.target);
            for (unsigned t : tgts)
                succ[i].push_back(local_of(m_gstate[t]));
        }
    }

    void split_manager::live_states(expr* R, ptr_vector<expr>& out, bool& ok) {
        ptr_vector<expr> states;
        vector<svector<unsigned>> succ;
        bool_vector maybe_null;
        build_graph(R, states, succ, maybe_null, ok);
        if (!ok) return;
        unsigned n = states.size();
        bool_vector live;
        live.resize(n, false);
        for (unsigned i = 0; i < n; ++i)
            live[i] = maybe_null[i];
        for (bool ch = true; ch; ) {
            ch = false;
            for (unsigned i = 0; i < n; ++i)
                if (!live[i])
                    for (unsigned j : succ[i])
                        if (live[j]) { live[i] = true; ch = true; break; }
        }
        for (unsigned i = 0; i < n; ++i)
            if (live[i]) out.push_back(states.get(i));
    }

    void split_manager::reaching_states(expr* R, expr* N, ptr_vector<expr>& out, bool& ok) {
        ptr_vector<expr> states;
        vector<svector<unsigned>> succ;
        bool_vector maybe_null;
        build_graph(R, states, succ, maybe_null, ok);
        if (!ok) return;
        unsigned n = states.size();
        unsigned tgt = UINT_MAX;
        for (unsigned i = 0; i < n; ++i)
            if (states.get(i) == N) { tgt = i; break; }
        if (tgt == UINT_MAX) return;              // N unreachable => no midpoints
        bool_vector reach;
        reach.resize(n, false);
        reach[tgt] = true;
        for (bool ch = true; ch; ) {
            ch = false;
            for (unsigned i = 0; i < n; ++i)
                if (!reach[i])
                    for (unsigned j : succ[i])
                        if (reach[j]) { reach[i] = true; ch = true; break; }
        }
        for (unsigned i = 0; i < n; ++i)
            if (reach[i]) out.push_back(states.get(i));
    }

    // ------------------------------------------------------------------
    //  intersection non-emptiness
    // ------------------------------------------------------------------

    // A component <R_i, N_i> is a membership (nullable) component when N_i is null or
    // the epsilon regex; otherwise it is a reach component with structural target N_i.
    static bool is_membership(seq_util::rex& re, cont_regex const& cr) {
        expr* N = cr.second.get();
        return N == nullptr || re.is_epsilon(N);
    }

    // Flatten the operands of a (possibly nested) re.inter into `out`.
    static void flatten_inter(seq_util::rex& re, expr* e, ptr_vector<expr>& out) {
        expr* a = nullptr, * b = nullptr;
        if (re.is_intersection(e, a, b)) {
            flatten_inter(re, a, out);
            flatten_inter(re, b, out);
        }
        else
            out.push_back(e);
    }

    lbool split_manager::intersect(vector<cont_regex> const& crs, unsigned lo, unsigned hi,
                                   expr_ref_vector& seq) {
        seq.reset();
        unsigned n = crs.size();
        if (n == 0) {
            // universal language: contains a word of every length; non-empty iff lo <= hi
            if (lo > hi) return l_false;
            for (unsigned k = 0; k < lo; ++k)
                seq.push_back(m.mk_true());       // trivial guard: any element admissible
            return l_true;
        }
        // Fast, robust path when every component is a membership (nullable) component:
        // the intersection is non-empty iff some reachable product state is nullable.
        bool all_memb = true;
        for (auto const& cr : crs)
            if (!is_membership(re(), cr)) { all_memb = false; break; }
        if (all_memb)
            return intersect_membership(crs, lo, hi, seq);

        // General case: a tuple product search that also handles reach targets
        // N != epsilon via structural target matching.
        return intersect_product(crs, lo, hi, seq);
    }

    lbool split_manager::intersect_membership(vector<cont_regex> const& crs, unsigned lo,
                                              unsigned hi, expr_ref_vector& seq) {
        unsigned n = crs.size();
        // The normalized intersection regex; the derivative engine handles guard
        // feasibility and successor computation internally.
        expr_ref P(crs[0].first.get(), m);
        for (unsigned i = 1; i < n; ++i)
            P = re().mk_inter(P, crs[i].first.get());
        m_th(P);
        unsigned r0 = intern_state(P.get());

        // Search node with witness reconstruction: `guard` is the derivative path
        // condition on the incoming edge (a predicate over the element (:var 0)).
        struct node { unsigned st; unsigned depth; int parent; expr* guard; };
        std::vector<node> nodes;

        // Beyond `cap` elements the length no longer changes acceptance, so we cap
        // the depth in the visited key to keep the state space finite.
        unsigned cap = (hi == UINT_MAX) ? lo : hi;
        auto key = [&](unsigned st, unsigned depth) {
            return std::make_pair(st, depth < cap ? depth : cap);
        };

        std::set<std::pair<unsigned, unsigned>> visited;
        nodes.push_back(node{ r0, 0, -1, nullptr });
        visited.insert(key(r0, 0));

        bool undecided = false;
        for (size_t head = 0; head < nodes.size(); ++head) {
            if (!m.inc()) return l_undef;
            int cur = (int) head;
            unsigned st = nodes[cur].st;          // note: `nodes` may grow below
            unsigned depth = nodes[cur].depth;

            if (depth >= lo && depth <= hi && m_gmaybe_null[st]) {
                expr_ref nb = m_rw.is_nullable(m_gstate[st]);
                if (m.is_true(nb)) {
                    ptr_vector<expr> gs;
                    for (int j = cur; j >= 0 && nodes[j].parent >= 0; j = nodes[j].parent)
                        gs.push_back(nodes[j].guard);
                    for (unsigned k = gs.size(); k-- > 0; )
                        seq.push_back(gs[k]);
                    return l_true;
                }
                if (!m.is_false(nb))
                    undecided = true;             // undecidable nullability => cannot claim l_false
            }
            if (depth >= hi)
                continue;                          // cannot extend further
            bool ok = true;
            expand_state(st, ok);
            if (!ok) return l_undef;
            for (edge const& e : m_gsucc[st])     // no interning here => m_gsucc stable
                if (visited.insert(key(e.target, depth + 1)).second)
                    nodes.push_back(node{ e.target, depth + 1, cur, e.guard });
        }
        return undecided ? l_undef : l_false;
    }

    lbool split_manager::intersect_product(vector<cont_regex> const& crs, unsigned lo,
                                           unsigned hi, expr_ref_vector& seq) {
        unsigned n = crs.size();

        bool_vector memb;                         // per component: membership (nullable) vs reach
        ptr_vector<expr> tgt;                     // per component: reach target (or null)
        svector<expr*> start;                     // start tuple
        for (auto const& cr : crs) {
            bool mb = is_membership(re(), cr);
            memb.push_back(mb);
            tgt.push_back(mb ? nullptr : cr.second.get());
            start.push_back(cr.first.get());
            m_pin.push_back(cr.first.get());
            if (!mb) m_pin.push_back(cr.second.get());
        }

        // Search node: a product tuple, its depth, its parent, and the joint guard on
        // the incoming edge (a predicate over the element variable (:var 0)).
        struct node { svector<expr*> st; unsigned depth; int parent; expr* guard; };
        std::vector<node> nodes;

        // Beyond `cap` elements the length no longer changes acceptance, so we cap the
        // depth in the visited key to keep the state space finite.
        unsigned cap = (hi == UINT_MAX) ? lo : hi;
        auto key = [&](svector<expr*> const& st, unsigned depth) {
            std::vector<unsigned> k;
            k.reserve(st.size() + 1);
            for (expr* e : st) k.push_back(e->get_id());
            k.push_back(depth < cap ? depth : cap);
            return k;
        };

        auto is_accept = [&](svector<expr*> const& st, bool& undecided) -> bool {
            for (unsigned i = 0; i < n; ++i) {
                if (memb[i]) {
                    expr_ref nb = m_rw.is_nullable(st[i]);
                    if (m.is_true(nb)) continue;
                    if (m.is_false(nb)) return false;
                    undecided = true; return false;
                }
                else if (st[i] != tgt[i])
                    return false;                 // reach component: structural target match
            }
            return true;
        };

        std::set<std::vector<unsigned>> visited;
        nodes.push_back(node{ start, 0, -1, nullptr });
        visited.insert(key(start, 0));

        bool undecided = false;
        for (size_t head = 0; head < nodes.size(); ++head) {
            if (!m.inc()) return l_undef;
            int cur = (int) head;
            svector<expr*> st = nodes[cur].st;    // copy: `nodes` may grow below
            unsigned depth = nodes[cur].depth;

            if (depth >= lo && depth <= hi) {
                bool u2 = false;
                if (is_accept(st, u2)) {
                    ptr_vector<expr> gs;          // reconstruct the per-position guards
                    for (int j = cur; j >= 0 && nodes[j].parent >= 0; j = nodes[j].parent)
                        gs.push_back(nodes[j].guard);
                    for (unsigned k = gs.size(); k-- > 0; )
                        seq.push_back(gs[k]);
                    return l_true;
                }
                if (u2) undecided = true;
            }
            if (depth >= hi)
                continue;                          // cannot extend further

            // Joint transitions: cofactors of inter(st_0,...,st_{n-1}).  The engine
            // prunes infeasible joint guards and yields the product successor as an
            // re.inter in source order, which we decompose positionally.
            expr_ref P(st[0], m);
            for (unsigned i = 1; i < n; ++i)
                P = re().mk_inter(P, st[i]);
            expr_ref_pair_vector cof(m);
            m_rw.brz_derivative_cofactors(P, cof);
            for (auto const& [g, t] : cof) {
                if (re().is_empty(t)) continue;
                svector<expr*> nst;
                if (n == 1)
                    nst.push_back(t);
                else {
                    ptr_vector<expr> ops;
                    flatten_inter(re(), t, ops);
                    if (ops.size() != n) {         // engine collapsed the product: give up soundly
                        undecided = true;
                        continue;
                    }
                    for (unsigned i = 0; i < n; ++i) nst.push_back(ops[i]);
                }
                for (expr* s : nst) m_pin.push_back(s);
                m_pin.push_back(g);
                if (visited.insert(key(nst, depth + 1)).second)
                    nodes.push_back(node{ nst, depth + 1, cur, g });
            }
        }
        return undecided ? l_undef : l_false;
    }

    bool split_manager::test_intersect(vector<cont_regex> const& crs) {
        // one-sided cheap check: an obviously-empty start (or reach target) state
        // certainly makes the intersection empty.  Normalize via th_rewriter first so
        // that e.g. concat(empty, epsilon) collapses to the empty regex.
        expr_ref tmp(m);
        for (auto const& cr : crs) {
            m_th(cr.first, tmp);
            if (re().is_empty(tmp))
                return false;
            if (cr.second.get()) {
                m_th(cr.second, tmp);
                if (re().is_empty(tmp))
                    return false;
            }
        }
        return true;
    }

    // ------------------------------------------------------------------
    //  seq::split / seq::split_iterator
    // ------------------------------------------------------------------

    split_iterator::split_iterator(split_manager& sm, cont_regex const& cr) {
        m_sm = &sm;
        m_R = cr.first.get();
        m_N = cr.second.get();
        bool ok = true;
        bool membership = (m_N == nullptr) || sm.re().is_epsilon(m_N);
        if (membership)
            sm.live_states(m_R, m_mids, ok);
        else
            sm.reaching_states(m_R, m_N, m_mids, ok);
        if (!ok) { m_failed = true; m_mids.reset(); }
    }

    split_pair split_iterator::operator*() const {
        ast_manager& m = m_sm->mgr();
        expr* mid = m_mids[m_pos];
        cont_regex left(expr_ref(m_R, m), expr_ref(mid, m));
        cont_regex right(expr_ref(mid, m), m_N ? expr_ref(m_N, m) : expr_ref(m));
        return split_pair(left, right);
    }

    split_iterator& split_iterator::operator++() {
        if (m_pos < m_mids.size()) ++m_pos;
        return *this;
    }

    split::split(split_manager& sm, expr* r)
        : m_sm(sm), m_R(r, sm.mgr()), m_N(sm.mgr()) {}

    split::split(split_manager& sm, cont_regex const& cr)
        : m_sm(sm), m_R(cr.first), m_N(cr.second) {}

    split_iterator split::begin() {
        return split_iterator(m_sm, cont_regex(m_R, m_N));
    }
}
