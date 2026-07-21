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

- epsilon transitions appear not accounted for when computing reaching states.
  If a regex R contains N by taking a set of epsilon transitions, then it is nullable relative 
  to N. It suggests a use for a version of nullability that is relative to N.
  Deal also with when N itself has epsilon transitions to N1, .., Nk.

- witness extraction is plain wrong. It should generally rely on a choice function that takes a
  Boolean expression F[(:var 0)] with a single free variable and synthesize a value for the free
  variable such that the expression is true. 
  For character predicates we can assume that the Boolean expressions are range predicates and we can 
  use utilities for range predicates. For other types use some best effort, say F is of the form (= (:var 0) value).
  Expose the witness function in a self-contained module outside of this file.

- checking intersections with continuation regexes is shady. The nullability check is now really about
  whether there is an epsilon transition to the accepting state N. The copilot-generated code ignores this.
  Generally, dealing with epsilon state is shady. There are many equivalent ways a state can be epsilon, such
  as epsilon*, or comp(.+), etc.

- I don't think there should be a special case for when N is epsilon and having N being nullptr
  is uneven.
  The code uses "live_states" and "reaching_states" for two cases.

- The code in test_intersect shouldn't be relying on a rewriter. Anything that can be rewritten
  could be done prior.

- Remove hard-wired constants such as STATE_CAP.

--*/

#include "ast/rewriter/seq_monadic.h"
#include "ast/ast_util.h"
#include <set>
#include <vector>
#include <climits>

namespace seq {

    // ------------------------------------------------------------------
    //  global derivative-transition graph (shared / recycled across regexes)
    // ------------------------------------------------------------------

    lbool split_manager::nullable(expr* s) {
        expr_ref nb = m_rw.is_nullable(s);
        return m.is_true(nb) ? l_true : m.is_false(nb) ? l_false : l_undef;
    }

    unsigned split_manager::intern_state(expr* s) {
        unsigned id;
        if (m_state_id.find(s, id))
            return id;                            // recycle the global state
        id = m_gstate.size();
        m_state_id.insert(s, id);
        m_gstate.push_back(s);
        m_pin.push_back(s);
        m_gmaybe_null.push_back(nullable(s) != l_false); // unknown nullability => keep (conservative)
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
            for (gedge const& e : m_gsucc[gid])
                tgts.push_back(e.target);
            for (unsigned t : tgts) {
                // hoist local_of out of the subscript: it may push_back onto succ
                // (reallocating it), which would dangle a succ[i] taken first.
                unsigned li = local_of(m_gstate[t]);
                succ[i].push_back(li);
            }
        }
    }

    // Backward closure of `seed` over the transition graph `succ`: mark every
    // state that can reach an already-marked one, then collect the marked states
    // into `out`.  `seed` is used in place as the working set.
    static void collect_backward_closure(vector<svector<unsigned>> const& succ, bool_vector& seed,
                                         ptr_vector<expr> const& states, ptr_vector<expr>& out) {
        const unsigned n = states.size();
        for (bool ch = true; ch; ) {
            ch = false;
            for (unsigned i = 0; i < n; ++i)
                if (!seed[i])
                    for (unsigned j : succ[i])
                        if (seed[j]) { seed[i] = true; ch = true; break; }
        }
        for (unsigned i = 0; i < n; ++i)
            if (seed[i]) out.push_back(states.get(i));
    }

    void split_manager::reachable_states(expr* R, expr* accept_target,
                                         ptr_vector<expr>& out, bool& ok) {
        ptr_vector<expr> states;
        vector<svector<unsigned>> succ;
        bool_vector maybe_null;                   // membership acceptance seed
        build_graph(R, states, succ, maybe_null, ok);
        if (!ok) return;
        if (!accept_target) {                     // membership: seed = nullable states
            collect_backward_closure(succ, maybe_null, states, out);
            return;
        }
        bool_vector reach;                        // reach: seed = the target state N
        reach.resize(states.size(), false);
        bool found = false;
        for (unsigned i = 0; i < states.size(); ++i)
            if (states.get(i) == accept_target) { reach[i] = true; found = true; break; }
        if (found)                                // N unreachable => no midpoints
            collect_backward_closure(succ, reach, states, out);
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

    // Beyond `depth_cap` elements the length no longer changes acceptance, so the
    // BFS caps the depth component of its visited key there to stay finite.
    static unsigned depth_cap(unsigned lo, unsigned hi) { return hi == UINT_MAX ? lo : hi; }

    // Reconstruct the per-position guard sequence of the accepting node `cur` by
    // walking its parent chain and reversing.  `Node` has `.parent` (int) and
    // `.guard` (expr*); the root (parent < 0) contributes no guard.
    template<typename Node>
    static void emit_witness(std::vector<Node> const& nodes, int cur, expr_ref_vector& seq) {
        ptr_vector<expr> gs;
        for (int j = cur; j >= 0 && nodes[j].parent >= 0; j = nodes[j].parent)
            gs.push_back(nodes[j].guard);
        for (unsigned k = gs.size(); k-- > 0; )
            seq.push_back(gs[k]);
    }

    // Shared bounded BFS with witness reconstruction, used by both the membership
    // and the product intersection search.  It explores states of type `State` up
    // to depth `hi`, deduping on (key_of(state), min(depth, depth_cap)) so the walk
    // stays finite even for hi == UINT_MAX.  The callbacks abstract the two engines:
    //   key_of(state)          -- comparable dedup key for the state
    //   accept(state) -> lbool -- l_true accepting / l_false not / l_undef unknown
    //   expand(state, out)     -- append (successor, incoming-guard) pairs; return
    //                             false on a resource limit
    // Returns l_true with the per-position guard witness in `seq`, l_false, or
    // l_undef (resource limit or an undecidable acceptance encountered en route).
    template<typename State, typename KeyOf, typename Accept, typename Expand>
    static lbool bounded_search(ast_manager& m, State const& start, unsigned lo, unsigned hi,
                                KeyOf key_of, Accept accept, Expand expand, expr_ref_vector& seq) {
        struct node { State st; unsigned depth; int parent; expr* guard; };
        std::vector<node> nodes;
        const unsigned cap = depth_cap(lo, hi);
        auto vkey = [&](State const& s, unsigned d) {
            return std::make_pair(key_of(s), d < cap ? d : cap);
        };
        std::set<decltype(vkey(start, 0u))> visited;
        nodes.push_back(node{ start, 0, -1, nullptr });
        visited.insert(vkey(start, 0));
        bool undecided = false;
        for (size_t head = 0; head < nodes.size(); ++head) {
            if (!m.inc()) return l_undef;
            int cur = (int) head;
            State st = nodes[cur].st;             // copy: `nodes` may grow below
            unsigned depth = nodes[cur].depth;
            if (depth >= lo && depth <= hi) {
                switch (accept(st)) {
                case l_true:  emit_witness(nodes, cur, seq); return l_true;
                case l_undef: undecided = true; break;   // cannot claim l_false
                case l_false: break;
                }
            }
            if (depth >= hi)
                continue;                          // cannot extend further
            std::vector<std::pair<State, expr*>> next;
            if (!expand(st, next)) return l_undef;
            for (auto const& [ns, g] : next)
                if (visited.insert(vkey(ns, depth + 1)).second)
                    nodes.push_back(node{ ns, depth + 1, cur, g });
        }
        return undecided ? l_undef : l_false;
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
        // feasibility and successor computation internally.  A single (interned,
        // globally cached) state is searched: acceptance is nullability, successors
        // are the cached cofactor edges.
        expr_ref P(crs[0].first.get(), m);
        for (unsigned i = 1; i < n; ++i)
            P = re().mk_inter(P, crs[i].first.get());
        m_th(P);
        unsigned r0 = intern_state(P.get());

        auto key_of = [](unsigned st) { return st; };
        auto accept = [&](unsigned st) {
            return m_gmaybe_null[st] ? nullable(m_gstate[st]) : l_false;
        };
        auto expand = [&](unsigned st, std::vector<std::pair<unsigned, expr*>>& out) {
            bool ok = true;
            expand_state(st, ok);
            if (!ok) return false;
            for (gedge const& e : m_gsucc[st])     // no interning here => m_gsucc stable
                out.push_back({ e.target, e.guard });
            return true;
        };
        return bounded_search<unsigned>(m, r0, lo, hi, key_of, accept, expand, seq);
    }

    lbool split_manager::intersect_product(vector<cont_regex> const& crs, unsigned lo,
                                           unsigned hi, expr_ref_vector& seq) {
        unsigned n = crs.size();

        bool_vector mem;
        ptr_vector<expr> tgt;
        svector<expr*> start;
        for (auto const& cr : crs) {
            bool mb = is_membership(re(), cr);
            mem.push_back(mb);
            tgt.push_back(mb ? nullptr : cr.second.get());
            start.push_back(cr.first.get());
            m_pin.push_back(cr.first.get());
            if (!mb)
                m_pin.push_back(cr.second.get());
        }

        // Search state is the product tuple; acceptance is per-component (nullable
        // for membership, structural target match for reach); successors are the
        // cofactors of inter(st_0,...,st_{n-1}) decomposed positionally.
        auto key_of = [](svector<expr*> const& st) {
            std::vector<unsigned> k;
            k.reserve(st.size());
            for (const expr * e : st) {
                k.push_back(e->get_id());
            }
            return k;
        };
        auto accept = [&](svector<expr*> const& st) -> lbool {
            for (unsigned i = 0; i < n; ++i) {
                if (!mem[i]) {
                    if (st[i] != tgt[i]) return l_false;   // reach: structural target
                    continue;
                }
                switch (nullable(st[i])) {
                case l_true:  continue;
                case l_false: return l_false;
                case l_undef: return l_undef;
                }
            }
            return l_true;
        };
        sort* seq_sort = nullptr, * ele_sort = nullptr;
        VERIFY(u().is_re(crs[0].first.get(), seq_sort));
        VERIFY(u().is_seq(seq_sort, ele_sort));
        expr_ref ele(m.mk_var(0, ele_sort), m);
        expr_ref eps_re(re().mk_epsilon(seq_sort), m);
        expr_ref empty_re(re().mk_empty(crs[0].first.get()->get_sort()), m);
        
        auto feasible = [&](expr* cond) -> bool {
            if (m.is_true(cond))
                return true;
            const expr_ref tr(m.mk_ite(cond, eps_re, empty_re), m);
            expr_ref_pair_vector res(m);
            m_rw.get_cofactors(ele, tr, res);
            for (auto const& [g, t] : res) {
                if (!re().is_empty(t))
                    return true;
            }
            return false;
        };
        auto expand = [&](svector<expr*> const& st, std::vector<std::pair<svector<expr*>, expr*>>& out) {
            std::vector<ptr_vector<expr>> comp_succ(n);
            vector<svector<expr*>> cg, ct;
            cg.resize(n);
            ct.resize(n);
            for (unsigned i = 0; i < n; ++i) {
                expr_ref_pair_vector ci(m);
                m_rw.brz_derivative_cofactors(st[i], ci);
                for (auto const& [gi, ti] : ci) {
                    if (re().is_empty(ti))
                        continue;
                    cg[i].push_back(gi);
                    ct[i].push_back(ti);
                    m_pin.push_back(gi);
                    m_pin.push_back(ti);
                }
                if (ct[i].empty())
                    return true;
            }
            
            svector<unsigned> idx;
            idx.resize(n, 0);
            svector<expr*> tuple;
            tuple.resize(n, nullptr);
            while (true) {
                expr_ref_vector gs(m);
                for (unsigned i = 0; i < n; ++i) {
                    tuple[i] = ct[i][idx[i]];
                    gs.push_back(cg[i][idx[i]]);
                }
                expr_ref g = mk_and(gs);
                if (n == 1 || feasible(g)) {
                    for (expr* s : tuple) {
                        m_pin.push_back(s);
                    }
                    m_pin.push_back(g);
                    out.push_back({ tuple, g });
                }
                unsigned k = 0;
                for (; k < n; ++k) {
                    idx[k]++;
                    if (idx[k] < ct[k].size())
                        break;
                    idx[k] = 0;
                }
                if (k == n)
                    break;
                if (!m.inc())
                    return false;
            }
            return true;
        };
        return bounded_search<svector<expr*>>(m, start, lo, hi, key_of, accept, expand, seq);
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
        sm.reachable_states(m_R, membership ? nullptr : m_N, m_mids, ok);
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
