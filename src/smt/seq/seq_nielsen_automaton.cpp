/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen_automaton.cpp

Abstract:

    Nielsen graph: the derivative automaton -- the global partial DFA,
    the nu-indexed explored regions Q backing land-state views, view
    length abstraction, frontier computation, and the synchronous
    product engines deciding emptiness / building witnesses.


Author:

    Clemens Eisenhofer 2026-03-02
    Nikolaj Bjorner (nbjorner) 2026-03-02

--*/

#include "smt/seq/seq_nielsen_internal.h"

namespace seq {

    uint_set const* nielsen_graph::projection_region(unsigned nu) const {
        if (nu == 0)
            return nullptr;
        // Exact semantics: ν names the state set recorded when the view was
        // created (paper: a view is identified by ν AND its recorded state
        // set Q; see mark_reachable_projection_edges).  Every minted ν has a
        // snapshot; an unknown ν denotes the empty region.
        const auto sit = m_projection_snapshots.find(nu);
        SASSERT(sit != m_projection_snapshots.end());
        return sit == m_projection_snapshots.end() ? nullptr : &sit->second.m_ids;
    }

    bool nielsen_graph::projection_state_in_Q(expr* state, unsigned nu) {
        if (!state)
            return false;
        uint_set const* Q = projection_region(nu);
        return Q && Q->contains(state->get_id());
    }

    void nielsen_graph::record_partial_derivative_edge(euf::snode const* src_re, euf::snode const* dst_re) {
        SASSERT(src_re && dst_re);
        if (!src_re->is_ground() || !dst_re->is_ground())
            return;
        if (src_re->is_fail() || dst_re->is_fail())
            return;

        expr* src_e = src_re->get_expr();
        expr* dst_e = dst_re->get_expr();

        // Deduplicate transitions by (src, dst) only — NOT by label.  The
        // Brzozowski automaton is deterministic, so the only a-transition out of
        // a state is to δ_a(state); edge labels are never consulted by
        // projection_state_in_Q / head_on_cycle.  Keying by label
        // would record the SAME transition twice when discovered once as a
        // concrete char and once as a minterm range, spuriously inflating the
        // SCC edge count and re-triggering cycle decomposition.
        partial_dfa_edge_key key{ src_e->get_id(), 0, dst_e->get_id() };
        if (m_partial_dfa_edge_index.contains(key))
            return;

        // Pin each expression so the egraph cannot release it on pop while we
        // still reference it from the cache.
        m_partial_dfa_pin.push_back(src_e);
        m_partial_dfa_pin.push_back(dst_e);

        unsigned edge_idx = m_partial_dfa_edges.size();
        m_partial_dfa_edge_index.emplace(key, edge_idx);

        partial_dfa_edge e;
        e.m_src = src_e;
        e.m_dst = dst_e;
        m_partial_dfa_edges.push_back(e);

        m_partial_dfa_out[src_e->get_id()].push_back(edge_idx);
    }

    bool nielsen_graph::head_on_cycle(euf::snode const* head_re) const {
        // Trigger gate for the cycle machinery: does some non-empty recorded
        // path lead from head_re back to head_re?  (Formerly a full SCC
        // computation whose result was only ever consumed as this boolean.)
        // Ids are expression ids (matching the keys of m_partial_dfa_out),
        // stable across sgraph pops because the exprs are pinned in
        // m_partial_dfa_pin.
        if (!head_re || !head_re->get_expr())
            return false;
        const unsigned root_id = head_re->get_expr()->get_id();
        uint_set seen;
        unsigned_vector stack;
        auto push_succs = [&](unsigned s) {
            auto it = m_partial_dfa_out.find(s);
            if (it == m_partial_dfa_out.end())
                return;
            for (const unsigned edge_idx : it->second) {
                if (edge_idx >= m_partial_dfa_edges.size())
                    continue;
                partial_dfa_edge const& e = m_partial_dfa_edges[edge_idx];
                if (e.m_dst)
                    stack.push_back(e.m_dst->get_id());
            }
        };
        push_succs(root_id); // start at the successors: a cycle needs >= 1 edge
        while (!stack.empty()) {
            const unsigned s = stack.back();
            stack.pop_back();
            if (s == root_id)
                return true;
            if (seen.contains(s))
                continue;
            seen.insert(s);
            push_succs(s);
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Landing decomposition support: Q = states forward-reachable from the head.
    // -----------------------------------------------------------------------

    void nielsen_graph::collect_reachable_from_head(euf::snode const* head_re, uint_set& Q,
                                                    ptr_vector<expr>* states) const {
        Q.reset();
        if (states)
            states->reset();
        if (!head_re || !head_re->get_expr())
            return;
        // Walk over expressions rather than bare ids so that `states` can be
        // filled in the same pass — the callers that need the state handles
        // would otherwise have to re-scan the whole partial DFA to recover them.
        ptr_vector<expr> stack;
        stack.push_back(head_re->get_expr());
        while (!stack.empty()) {
            expr* se = stack.back();
            stack.pop_back();
            const unsigned s = se->get_id();
            if (Q.contains(s))
                continue;
            Q.insert(s);
            if (states)
                states->push_back(se);
            auto it = m_partial_dfa_out.find(s);
            if (it == m_partial_dfa_out.end())
                continue;
            for (const unsigned edge_idx : it->second) {
                if (edge_idx >= m_partial_dfa_edges.size())
                    continue;
                partial_dfa_edge const& e = m_partial_dfa_edges[edge_idx];
                if (e.m_dst)
                    stack.push_back(e.m_dst);
            }
        }
    }

    unsigned nielsen_graph::mark_reachable_projection_edges(euf::snode const* head_re) {
        // Snapshot semantics (paper "Implementation Aspects": a view is
        // identified by ν AND its recorded state set Q).  The returned ν names
        // the EXACT forward-reachable set Q of head_re at this moment, stored
        // in m_projection_snapshots; views gate on membership in that snapshot
        // (projection_state_in_Q).
        if (!head_re || !head_re->get_expr())
            return 0;
        const unsigned head_id = head_re->get_expr()->get_id();

        // Fast path: the partial DFA is monotone, so an unchanged edge count
        // means the head's reachable set is unchanged — reuse the previous ν.
        auto cit = m_projection_head_cache.find(head_id);
        if (cit != m_projection_head_cache.end()
            && cit->second.first == m_partial_dfa_edges.size())
            return cit->second.second;

        uint_set Q;
        ptr_vector<expr> states;
        collect_reachable_from_head(head_re, Q, &states);

        // Slow path: the graph grew, but possibly only outside the head's
        // region — reuse the previous snapshot if the set is unchanged.
        if (cit != m_projection_head_cache.end()) {
            const auto sit = m_projection_snapshots.find(cit->second.second);
            if (sit != m_projection_snapshots.end()
                && sit->second.m_ids.num_elems() == Q.num_elems()) {
                bool same = true;
                for (const unsigned id : Q)
                    if (!sit->second.m_ids.contains(id)) { same = false; break; }
                if (same) {
                    cit->second.first = m_partial_dfa_edges.size();
                    return cit->second.second;
                }
            }
        }

        const unsigned nu = ++m_projection_extract_idx;

        // Record the snapshot: the id set plus the state exprs.  `states` was
        // collected by the reachability walk above (head first, then the states
        // in discovery order), so no scan of the whole partial DFA is needed.
        // Pin the head so every stored expr outlives sgraph pops (edge endpoints
        // are already pinned by record_partial_derivative_edge).
        projection_snapshot snap;
        snap.m_ids = Q;
        m_partial_dfa_pin.push_back(head_re->get_expr());
        snap.m_states.swap(states);
        SASSERT(!snap.m_states.empty() && snap.m_states[0] == head_re->get_expr());
        m_projection_snapshots.emplace(nu, std::move(snap));
        m_projection_head_cache[head_id] = { m_partial_dfa_edges.size(), nu };
        return nu;
    }

    void nielsen_graph::collect_projection_states(unsigned nu, svector<euf::snode const*>& out) {
        // Enumeration counterpart of projection_state_in_Q — keep in sync with
        // it (it is the membership test the view gates use in consume_view and
        // comp_step).  Exact semantics: the states of the ν-snapshot; every
        // minted ν has one, an unknown ν denotes the empty region.
        if (nu == 0)
            return;
        const auto sit = m_projection_snapshots.find(nu);
        SASSERT(sit != m_projection_snapshots.end());
        if (sit == m_projection_snapshots.end())
            return;
        for (expr* ep : sit->second.m_states) {
            // mk, not find: the exprs are pinned but their snodes may have
            // been released by an sgraph pop.
            euf::snode const* sn = m_sg.mk(ep);
            if (sn)
                out.push_back(sn);
        }
    }

    void nielsen_graph::compute_view_length_info(unsigned nu, expr* from, view_len_info& info) {
        info.m_dist.reset();
        info.m_stride = 0;
        info.m_ok = false;
        if (!from || nu == 0)
            return;
        const auto sit = m_projection_snapshots.find(nu);
        if (sit == m_projection_snapshots.end())
            return; // watermark-fallback ν without an exact snapshot: no abstraction
        uint_set const& Q = sit->second.m_ids;
        if (!Q.contains(from->get_id()))
            return; // gate closed at the head: L ⊆ {ε}, handled by the degenerate cases

        // BFS over the recorded in-Q edges (each edge consumes one character).
        // At ν-minting time compute_frontier saturated these edges, so they are
        // exactly the one-character transitions among Q_ν states; edges are only
        // ever added, so saturation persists and the abstraction stays sound.
        unsigned_vector queue;
        unsigned qhead = 0;
        info.m_dist.insert(from->get_id(), 0);
        queue.push_back(from->get_id());
        while (qhead < queue.size()) {
            const unsigned u = queue[qhead++];
            const unsigned du = info.m_dist.find(u);
            auto it = m_partial_dfa_out.find(u);
            if (it == m_partial_dfa_out.end())
                continue;
            for (const unsigned edge_idx : it->second) {
                if (edge_idx >= m_partial_dfa_edges.size())
                    continue;
                partial_dfa_edge const& e = m_partial_dfa_edges[edge_idx];
                if (!e.m_dst)
                    continue;
                const unsigned v = e.m_dst->get_id();
                if (!Q.contains(v) || info.m_dist.contains(v))
                    continue;
                info.m_dist.insert(v, du + 1);
                queue.push_back(v);
            }
        }

        // Stride g = gcd over reachable in-Q edges (u,v) of (d(u) + 1 − d(v)):
        // by telescoping, every gated walk from the head to v has length
        // ≡ d(v) (mod g); g = 0 means every such walk has length exactly d(v).
        unsigned g = 0;
        for (const unsigned u : queue) {
            const unsigned du = info.m_dist.find(u);
            auto it = m_partial_dfa_out.find(u);
            if (it == m_partial_dfa_out.end())
                continue;
            for (const unsigned edge_idx : it->second) {
                if (edge_idx >= m_partial_dfa_edges.size())
                    continue;
                partial_dfa_edge const& e = m_partial_dfa_edges[edge_idx];
                if (!e.m_dst)
                    continue;
                const unsigned v = e.m_dst->get_id();
                if (!Q.contains(v))
                    continue;
                SASSERT(info.m_dist.contains(v)); // v is reachable since u is
                const unsigned t = du + 1 - info.m_dist.find(v);
                if (t != 0)
                    g = g == 0 ? t : u_gcd(g, t);
            }
        }
        info.m_stride = g;
        info.m_ok = true;
    }

    void nielsen_graph::add_view_length_constraints(nielsen_edge* e, view_len_info const& info, unsigned nu,
                                                    euf::snode const* pinned, expr* to, dep_tracker const& dep) {
        if (!m_view_length_constraints)
            return;
        if (!e || !info.m_ok || !pinned || !to)
            return;

        unsigned min_len = 0, stride = 0;
        bool exact = false;
        if (projection_state_in_Q(to, nu)) {
            // Walk and landing state stay inside Q_ν, where the recorded edges
            // are saturated: min = d(to), stride = g.
            if (!info.m_dist.contains(to->get_id()))
                return; // unreachable ⇒ empty view; the branch dies at its leaf
            min_len = info.m_dist.find(to->get_id());
            stride = info.m_stride;
            exact = stride == 0;
        }
        else {
            // Landing target outside Q_ν (view landing at root ∉ Q_ν): the
            // final hop may be an UNRECORDED transition from any reachable
            // q ∈ Q_ν, of length d(q) + 1 ≡ 1 (mod gcd(g, all reachable d(q))),
            // so only this weakened progression is sound.
            min_len = 1;
            stride = info.m_stride;
            for (auto const& [id, d] : info.m_dist) {
                (void)id;
                if (d != 0)
                    stride = stride == 0 ? d : u_gcd(stride, d);
            }
            exact = stride == 0; // only the head is reachable: len = 1 exactly
        }

        if (!exact && min_len == 0 && stride <= 1)
            return; // trivial

        const expr_ref len = compute_length_expr(pinned);
        if (exact) {
            e->add_side_constraint(mk_constraint(a.mk_eq(len, a.mk_int(min_len)), dep));
            return;
        }
        if (min_len > 0)
            e->add_side_constraint(mk_constraint(a.mk_ge(len, a.mk_int(min_len)), dep));
        if (stride > 1) {
            // stride | (len − min).  Rewrite eagerly — the raw divisibility
            // predicate is not internalized automatically (see the analogous
            // gradient propagation in theory_nseq).
            expr_ref div(a.mk_divides(a.mk_int(stride), a.mk_sub(len, a.mk_int(min_len))), m);
            e->add_side_constraint(mk_constraint(div, dep));
        }
    }

    void nielsen_graph::compute_frontier(uint_set const& Q, svector<euf::snode const*> const& Qstates,
                                         vector<frontier_edge>& out_frontier) {
        // One lazy step from each Q state.  Derive over the minterms of every
        // p ∈ Qstates: δ_mt(p) ∈ Q is an internal edge (recorded, closing cycles
        // for a future land-at-R); δ_mt(p) ∉ Q (and ≠ ⊥) is a frontier/escape
        // edge.  Snapshot Qstates was collected by the caller BEFORE this call,
        // so recording internal edges (which appends to m_partial_dfa_edges) does
        // not disturb the iteration.
        for (euf::snode const* p : Qstates) {
            if (!m.inc())
                return;
            if (!p || !p->is_ground())
                continue;
            euf::snode_vector mts;
            m_sg.compute_minterms(p, mts);
            for (euf::snode const* mt : mts) {
                euf::snode const* q = m_sg.brzozowski_deriv(p, mt);
                if (!q || q->is_fail() || !q->is_ground())
                    continue;
                if (Q.contains(q->get_expr()->get_id()))
                    record_partial_derivative_edge(p, q);   // internal edge
                else
                    out_frontier.push_back(frontier_edge{ p, mt, q });
            }
        }
    }

    // -----------------------------------------------------------------------
    // Helper: ensure_automaton_explored  (budgeted, on-demand, cached)
    // Records the reachable Brzozowski automaton of root_re into the partial
    // DFA, once per regex component, up to a per-call STATE BUDGET.  This is
    // the eager/lazy hybrid of the paper's two modes:
    //   - a component smaller than the budget (the common case) is saturated
    //     in one go: every land-at-s block of the landing decomposition is
    //     available immediately, the frontier is empty, and no escape ever
    //     re-walks explored structure;
    //   - a larger component is left PARTIAL — a sound under-approximation,
    //     exactly as at the resource limit: the frontier is then non-empty
    //     and the ESCAPE branches grow Q on demand, one recorded edge at a
    //     time — the paper's lazy mode.  This avoids materializing large
    //     derivative automata (complement/intersection blowups, e.g. the
    //     paper's Σ*bΣ^k example) up front.
    // States dequeued before the cutoff are in m_explored_automaton; the
    // truncated remainder is NOT, so consumption-time minterm-edge recording
    // stays active for those sources — escapes keep making progress and the
    // termination bound (escapes ≤ edges of the finite monotone G) holds.
    //
    // Soundness never depends on completeness of Q: a land-at-s view forces
    // δ_x(head) = s for ANY Q, and the stabilizer invariant holds for any Q
    // (paper, Invariant 1); a partial Q only shifts work to the escapes.
    // The BFS is bounded by the budget and the finite reachable automaton
    // (Brzozowski states modulo ACI); m.inc() keeps it responsive to the
    // resource limit.
    // -----------------------------------------------------------------------

    bool nielsen_graph::ensure_automaton_explored(euf::snode const* root_re) {
        SASSERT(root_re);
        if (!root_re->is_ground())
            return false;
        if (m_explored_automaton.contains(root_re->get_expr()->get_id()))
            return m_fully_explored.contains(root_re->get_expr()->get_id());

        // Per-call cap on eagerly explored states.  Components that overflow it
        // fall back to the paper's lazy escape-driven exploration.  Exposed as
        // smt.nseq.exploration_budget; 0 = no eager exploration at all, i.e. the
        // fully lazy mode where Q grows only via escapes and consumption-time edges.
        const unsigned exploration_budget = m_exploration_budget;
        if (exploration_budget == 0)
            return false;
        unsigned processed = 0;

        svector<euf::snode const*> queue;
        queue.push_back(root_re);
        // States dequeued on THIS walk.  If the queue drains, every one of them has
        // its full reachable set recorded (reachability is transitive), so they can
        // all be marked complete — not just the root.
        unsigned_vector walked;
        // A state already in m_explored_automaton is skipped WITHOUT re-enqueuing its
        // successors, so this walk learns nothing about what lies beyond it.  If that
        // state is not itself known complete (an earlier walk may have been truncated
        // right after expanding it), draining our queue proves nothing.
        bool complete = true;

        while (!queue.empty()) {
            if (!m.inc())
                return false; // resource limit: leave Q partial (sound under-approx)
            euf::snode const* re = queue.back();
            queue.pop_back();
            const unsigned re_eid = re->get_expr()->get_id();
            if (m_explored_automaton.contains(re_eid)) {
                if (!m_fully_explored.contains(re_eid))
                    complete = false;
                continue; // already explored (here or in a previous component)
            }
            if (processed++ >= exploration_budget)
                return false; // budget: leave the remainder to the escape branches
            m_explored_automaton.insert(re_eid);
            walked.push_back(re_eid);

            euf::snode_vector mts;
            m_sg.compute_minterms(re, mts);
            for (euf::snode const* mt : mts) {
                euf::snode const* deriv = m_sg.brzozowski_deriv(re, mt);
                if (!deriv || deriv->is_fail())
                    continue;
                record_partial_derivative_edge(re, deriv);
                if (deriv->is_ground() && !m_explored_automaton.contains(deriv->get_expr()->get_id()))
                    queue.push_back(deriv);
            }
        }
        // The queue drained AND nothing we skipped was of unknown depth: every state
        // walked here has its whole reachable set recorded, so Q may be treated as
        // the full automaton from any of them.
        if (!complete)
            return false;
        for (const unsigned id : walked)
            m_fully_explored.insert(id);
        return true;
    }

    // -----------------------------------------------------------------------
    // Regex widening: over-approximate the string and check emptiness against
    // the membership's language — at the CONSTRAINT level (paper, "Pruning
    // incrementally during construction"): one product factor per token of
    // Ω(str) and one component for the right-hand side, decided by the
    // concatenation-aware synchronous derivative search below.  No closed-form
    // regex for Ω(str) ⊓ rhs is ever built, and land-state views participate
    // EXACTLY via their gated one-character law — both as the widened
    // membership itself and as pinned constraints inside Ω.
    // -----------------------------------------------------------------------

    bool nielsen_graph::check_regex_widening(nielsen_node const& node, str_mem const& mem, dep_tracker& dep) {
        const auto str = mem.m_str;
        const auto regex = mem.m_regex;
        SASSERT(m_seq_regex);
        // The right-hand side must be a settled plain state; an unresolved
        // symbolic ite residual is left to apply_regex_if_split.
        if (!regex->is_ground() || regex->kind() == euf::snode_kind::s_ite)
            return false;

        // Build Ω(str) as one component factor per token:
        //   concrete char c → plain component to_re(unit(c))
        //   variable x      → the variable's primitive components — plain
        //                     regexes AND land-state views, handled exactly;
        //                     the empty factor denotes Σ* when unconstrained
        //   symbolic char   → plain component from char_ranges (or Σ¹)
        //   anything else   → empty factor (Σ*)
        euf::snode_vector tokens;
        str->collect_tokens(tokens);
        if (tokens.empty())
            return false;

        SASSERT(dep);

        vector<vector<prod_comp>> factors;
        for (euf::snode const* tok : tokens) {
            vector<prod_comp> factor;

            if (tok->is_char()) {
                // Concrete character → to_re(unit(c))
                expr* te = tok->get_expr();
                SASSERT(te);
                factor.push_back(prod_comp::mk_plain(m_sg.mk(m_seq.re.mk_to_re(te))));
            }
            else if (tok->is_var()) {
                // Variable → ⊓Reg_x as components (views join exactly, with
                // their own gate/acceptance); empty factor = Σ* if unconstrained.
                collect_var_components(tok, node, factor, dep);
                TRACE(seq, tout << "widening factor " << spp(tok, m)
                                << ": " << factor.size() << " components\n");
            }
            else if (tok->is_unit()) {
                // Symbolic char — char_range if known, otherwise Σ¹.
                euf::snode const* range_re = nullptr;
                if (node.char_ranges().contains(tok->id())) {
                    auto& cs = node.char_ranges()[tok->id()];
                    if (!cs.first.is_empty()) {
                        // Build union of re.range for each interval
                        for (auto const& r : cs.first.ranges()) {
                            expr_ref rng(m_seq.re.mk_range(
                                m_seq.str.mk_string(zstring(r.m_lo)),
                                m_seq.str.mk_string(zstring(r.m_hi - 1))), m);
                            euf::snode const* rng_sn = m_sg.mk(rng);
                            if (!range_re)
                                range_re = rng_sn;
                            else {
                                expr_ref u(m_seq.re.mk_union(range_re->get_expr(), rng_sn->get_expr()), m);
                                range_re = m_sg.mk(u);
                            }
                        }
                        dep = dep_mgr().mk_join(dep, cs.second);
                    }
                }
                if (!range_re) {
                    // Unconstrained symbolic char: full_char (single char, any value)
                    sort* str_sort = m_seq.str.mk_string_sort();
                    expr_ref fc(m_seq.re.mk_full_char(m_seq.re.mk_re(str_sort)), m);
                    range_re = m_sg.mk(fc);
                }
                factor.push_back(prod_comp::mk_plain(range_re));
            }
            // else: unknown token type (e.g. power) — empty factor = Σ*.

            factors.push_back(factor);
        }

        // Right-hand side component: exact for plain memberships and views alike
        // (the view's Q-gate and land-state acceptance are the component's own
        // one-character law, Theorem "Soundness of views").
        const prod_comp rhs = mem.is_view()
            ? prod_comp::mk_view(mem.m_regex, mem.m_root, mem.m_nu,
                                 projection_region(mem.m_nu), /*complemented*/ false)
            : prod_comp::mk_plain(mem.m_regex);

        // TODO: Minimize the conflict here
        const lbool result = check_concat_product_emptiness(factors, rhs, 5000);
        TRACE(seq, tout << "widen empty-product: " << result << " " << mem_pp(mem) << "\n";
        display(tout, &node) << "\n");
        return result == l_true;
    }

    // -----------------------------------------------------------------------
    // Synchronous product over plain / view / guard / co-view components.
    // -----------------------------------------------------------------------

    lbool nielsen_graph::comp_accepting(prod_comp const& c) const {
        if (c.m_dead)
            return l_false;
        switch (c.m_kind) {
        case mem_kind::plain:
            return m_sg.re_nullable(c.m_state);
        case mem_kind::stab_view:
            if (c.m_complemented)
                return (c.m_sink || c.m_state != c.m_root) ? l_true : l_false;
            return (c.m_state == c.m_root) ? l_true : l_false;
        }
        return l_undef;
    }

    nielsen_graph::prod_comp nielsen_graph::comp_step(prod_comp const& c, euf::snode const* mt) {
        prod_comp r = c;
        if (c.m_dead)
            return r;
        switch (c.m_kind) {
        case mem_kind::plain: {
            euf::snode const* d = m_sg.brzozowski_deriv(c.m_state, mt);
            if (!d || d->is_fail()) r.m_dead = true; else r.m_state = d;
            return r;
        }
        case mem_kind::stab_view: {
            if (c.m_complemented) {
                if (c.m_sink) return r;                    // Σ*
                if (!c.state_in_region()) { r.m_sink = true; return r; }
                euf::snode const* d = m_sg.brzozowski_deriv(c.m_state, mt);
                if (!d || d->is_fail()) { r.m_sink = true; return r; } // ~∅ = Σ*
                r.m_state = d;
                return r;
            }
            if (!c.state_in_region()) { r.m_dead = true; return r; }
            euf::snode const* d = m_sg.brzozowski_deriv(c.m_state, mt);
            if (!d || d->is_fail()) { r.m_dead = true; return r; }
            r.m_state = d;
            return r;
        }
        }
        return r;
    }

    void nielsen_graph::prod_comp_key(prod_comp const& c, std::vector<unsigned>& key) {
        key.push_back(static_cast<unsigned>(c.m_kind));
        key.push_back((c.m_complemented ? 1u : 0u) | (c.m_sink ? 2u : 0u) | (c.m_dead ? 4u : 0u));
        key.push_back(c.m_state ? c.m_state->id() : UINT_MAX);
    }

    lbool nielsen_graph::tuple_accepting(vector<prod_comp> const& cs) const {
        bool any_undef = false;
        for (auto const& c : cs) {
            const lbool a = comp_accepting(c);
            if (a == l_false)
                return l_false;
            if (a == l_undef)
                any_undef = true;
        }
        return any_undef ? l_undef : l_true;
    }

    bool nielsen_graph::step_tuple(vector<prod_comp> const& cur, euf::snode const* mt,
                                   vector<prod_comp>& nxt) {
        nxt.reset();
        for (auto const& c : cur) {
            prod_comp d = comp_step(c, mt);
            if (d.m_dead)
                return false;
            nxt.push_back(d);
        }
        return true;
    }

    void nielsen_graph::joint_minterms(vector<prod_comp> const& comps, prod_comp const* extra,
                                       euf::snode_vector& mts) {
        // joint first-character partition = minterms of the intersection of
        // all still-discriminating (non-sink, non-dead) component states.
        expr* combined = nullptr;
        auto add_state = [&](prod_comp const& c) {
            if (c.m_sink || c.m_dead)
                return;
            combined = combined ? m_seq.re.mk_inter(combined, c.m_state->get_expr())
                                : c.m_state->get_expr();
        };
        if (extra)
            add_state(*extra);
        for (auto const& c : comps)
            add_state(c);
        if (!combined)
            return; // no discriminating state: no character step possible
        m_sg.compute_minterms(m_sg.mk(combined), mts);
    }

    lbool nielsen_graph::check_product_emptiness(vector<prod_comp> const& comps0, unsigned max_states) {
        if (comps0.empty())
            return l_false; // empty intersection = Σ* (non-empty)
        // Thin wrapper over the concatenation-aware engine: a single factor
        // holding the whole tuple, with a trivially accepting Σ* right-hand
        // side.  A common word is then found exactly when the factor tuple is
        // simultaneously accepting.
        sort* re_sort = comps0[0].m_state->get_expr()->get_sort();
        const expr_ref full(m_seq.re.mk_full_seq(re_sort), m);
        const prod_comp rhs = prod_comp::mk_plain(m_sg.mk(full));
        vector<vector<prod_comp>> factors;
        factors.push_back(comps0);
        return check_concat_product_emptiness(factors, rhs, max_states);
    }

    // -----------------------------------------------------------------------
    // Concatenation-aware synchronous product (paper, "Pruning incrementally
    // during construction"): emptiness of
    //     ( L(F_0) · L(F_1) · … · L(F_{k-1}) )  ⊓  L(rhs)
    // where each factor F_i is the intersection of its components (an EMPTY
    // component list denotes Σ*) and rhs is one further component consumed
    // synchronously with the whole concatenation.  A search state is
    // (factor index i, component tuple of F_i, rhs component); a character
    // step derives every live component on a joint minterm, and when all of
    // F_i's components accept the search may ε-advance to F_{i+1}
    // (nondeterministically — both continuations are explored).  A word is
    // found when every factor has been consumed (i = k) and rhs accepts.
    //
    // l_true:  empty — pruning on this verdict is sound;
    // l_false: a common word exists;
    // l_undef: budget exhausted or acceptance undecidable — the caller must
    //          NOT prune (dropping the ε-advance or the final acceptance on
    //          an undecided component could wrongly report emptiness).
    // -----------------------------------------------------------------------

    // FNV-style hash for the visited-key encoding of a product state.  The
    // engines below run with budgets of several thousand states per call; an
    // ordered std::set would pay an O(len·log n) vector comparison per probe.
    struct prod_key_hash {
        size_t operator()(std::vector<unsigned> const& v) const {
            size_t h = 0xcbf29ce484222325ull;
            for (unsigned x : v)
                h = (h ^ x) * 0x100000001b3ull;
            return h;
        }
    };

    lbool nielsen_graph::check_concat_product_emptiness(vector<vector<prod_comp>> const& factors,
                                                        prod_comp const& rhs, unsigned max_states) {
        const unsigned k = factors.size();

        struct cstate {
            unsigned          m_idx;   // current factor (k = all factors consumed)
            vector<prod_comp> m_comps; // components of factor m_idx
            prod_comp         m_rhs;   // right-hand-side component
        };

        std::unordered_set<std::vector<unsigned>, prod_key_hash> visited;
        vector<cstate> work;

        // Reused key buffer: the vast majority of candidates are duplicates, and
        // building the key into a scratch vector means only the states that are
        // actually NEW pay an allocation (the one the set has to make anyway).
        std::vector<unsigned> key;
        // `comps` by value so callers can hand over ownership: the character
        // step below moves its successor tuple in instead of copying it.
        auto push_state = [&](unsigned idx, vector<prod_comp> comps, prod_comp const& r) {
            key.clear();
            key.push_back(idx);
            prod_comp_key(r, key);
            for (auto const& c : comps)
                prod_comp_key(c, key);
            if (visited.insert(key).second)
                work.push_back(cstate{ idx, std::move(comps), r });
        };

        push_state(0, k == 0 ? vector<prod_comp>() : factors[0], rhs);
        unsigned explored = 0;
        // an ε-advance or final acceptance was undecidable somewhere: on
        // exhaustion we may no longer claim emptiness (pruning on it would be
        // unsound), but a definite common word found on another path still
        // decides l_false.
        bool undef_result = false;

        // scratch buffers of the character step, reused across all states
        euf::snode_vector mts;
        vector<prod_comp> nxt;

        while (!work.empty()) {
            if (!m.inc())
                return l_undef;
            if (explored >= max_states)
                return l_undef;
            const cstate cur = std::move(work.back());
            work.pop_back();
            ++explored;

            if (cur.m_rhs.m_dead)
                continue; // the membership side is ∅ from here
            bool any_dead = false;
            for (auto const& c : cur.m_comps) if (c.m_dead) { any_dead = true; break; }
            if (any_dead)
                continue;

            // ε-advance / final acceptance: do all components of the current
            // factor accept?  (Trivially true for the Σ* empty factor and for
            // the terminal index k.)  An undecided acceptance forfeits only
            // this state's ε-advance/word-end — character continuations are
            // still explored.
            const lbool allacc = tuple_accepting(cur.m_comps);
            if (allacc == l_undef)
                undef_result = true;

            if (allacc == l_true) {
                if (cur.m_idx >= k) {
                    // all factors consumed: the word ends here
                    const lbool racc = comp_accepting(cur.m_rhs);
                    if (racc == l_true)
                        return l_false; // found a common word
                    if (racc == l_undef)
                        undef_result = true;
                }
                else
                    // ε-advance to the next factor (kept alongside the
                    // character continuations below)
                    push_state(cur.m_idx + 1,
                               cur.m_idx + 1 < k ? factors[cur.m_idx + 1] : vector<prod_comp>(),
                               cur.m_rhs);
            }

            if (cur.m_idx >= k)
                continue; // terminal: no further characters may be consumed

            // character step: joint first-character partition of the live
            // component states (factor + rhs).  `mts` / `nxt` are hoisted out of
            // the loops: step_tuple resets `nxt`, and moving it into push_state
            // leaves it in the (valid, empty-after-reset) moved-from state.
            mts.reset();
            joint_minterms(cur.m_comps, &cur.m_rhs, mts);

            for (euf::snode const* mt : mts) {
                prod_comp r2 = comp_step(cur.m_rhs, mt);
                if (r2.m_dead)
                    continue;
                if (!step_tuple(cur.m_comps, mt, nxt))
                    continue;
                push_state(cur.m_idx, std::move(nxt), r2);
            }
        }
        // exhausted with no accepting configuration → empty, unless some
        // acceptance/advance decision could not be made along the way
        return undef_result ? l_undef : l_true;
    }

    bool nielsen_graph::collect_var_components(euf::snode const* var, nielsen_node const& node,
                                               vector<prod_comp>& out, dep_tracker& dep) {
        bool found = false;
        for (auto const& mem : node.str_mems()) {
            if (!mem.is_primitive())
                continue;
            // Compare by expression, not snode pointer: the sgraph may hold
            // several distinct snode objects for the same hash-consed
            // expression (seq_model passes a snode re-created from the
            // substitution tree).  A pointer mismatch would silently drop the
            // variable's view/plain components here, and product_witness's
            // empty-tuple fast path would then fabricate an unconstrained
            // filler word resulting in an invalid model.
            if (mem.m_str->first()->get_expr() != var->get_expr())
                continue;
            switch (mem.m_kind) {
            case mem_kind::plain:
                out.push_back(prod_comp::mk_plain(mem.m_regex));
                break;
            case mem_kind::stab_view:
                out.push_back(prod_comp::mk_view(mem.m_regex, mem.m_root, mem.m_nu,
                                                 projection_region(mem.m_nu), false));
                break;
            }
            dep = m_dep_mgr.mk_join(dep, mem.m_dep);
            found = true;
        }
        return found;
    }

    lbool nielsen_graph::check_var_length_emptiness(euf::snode const* var, nielsen_node const& node,
                                                    unsigned len, dep_tracker& dep) {
        vector<prod_comp> comps;
        collect_var_components(var, node, comps, dep);
        if (comps.empty())
            return l_false;   // unconstrained: every length is realizable
        sort* re_sort = comps[0].m_state ? comps[0].m_state->get_expr()->get_sort() : nullptr;
        if (!re_sort)
            return l_undef;
        const expr_ref sigma_n(m_seq.re.mk_loop(m_seq.re.mk_full_char(re_sort), len, len), m);
        comps.push_back(prod_comp::mk_plain(m_sg.mk(sigma_n)));
        return check_product_emptiness(comps, 5000);
    }

    bool nielsen_graph::product_witness(euf::snode const* var, nielsen_node const& node,
                                        unsigned len, zstring& out) {
        // Shortest-accepting-word search over the product of all of var's
        // primitive components (plain regexes AND land-state views), optionally
        // intersected with Σ^len.  Mirrors check_product_emptiness but records
        // the spelled word so a SAT-leaf variable pinned to a land-state view
        // (F={s}) gets a concrete witness (ε alone is inadmissible when s≠head).
        vector<prod_comp> comps0;
        dep_tracker d = nullptr;
        collect_var_components(var, node, comps0, d);

        if (len != UINT_MAX) {
            // force exact length via a Σ^len plain component
            sort* re_sort = nullptr;
            if (!comps0.empty() && comps0[0].m_state)
                re_sort = comps0[0].m_state->get_expr()->get_sort();
            if (re_sort) {
                const expr_ref sigma_n(
                    m_seq.re.mk_loop(m_seq.re.mk_full_char(re_sort), len, len), m);
                comps0.push_back(prod_comp::mk_plain(m_sg.mk(sigma_n)));
            }
        }

        if (comps0.empty()) {
            // no constraints: any word of the requested length (default ε)
            out = zstring();
            for (unsigned i = 0; i < (len == UINT_MAX ? 0u : len); ++i)
                out = out + zstring((unsigned)'a');
            return true;
        }

        // Reused key buffer (see check_concat_product_emptiness): only tuples
        // that are actually new pay an allocation.
        std::vector<unsigned> key;
        auto encode_into = [&key](vector<prod_comp> const& cs) {
            key.clear();
            for (auto const& c : cs)
                prod_comp_key(c, key);
        };

        std::unordered_set<std::vector<unsigned>, prod_key_hash> visited;
        // BFS (vector + head index) for a SHORTEST accepting word.
        vector<std::pair<vector<prod_comp>, zstring>> work;
        encode_into(comps0);
        visited.insert(key);
        work.push_back({ comps0, zstring() });
        unsigned head = 0;
        const unsigned MAX_STATES = 200000;

        // scratch buffers of the character step, reused across all states
        euf::snode_vector mts;
        vector<prod_comp> nxt;

        while (head < work.size()) {
            if (!m.inc() || head >= MAX_STATES)
                return false;
            // move out: the BFS never revisits an entry behind `head`
            vector<prod_comp> cur = std::move(work[head].first);
            zstring w = std::move(work[head].second);
            ++head;

            bool any_dead = false;
            for (auto const& c : cur) if (c.m_dead) { any_dead = true; break; }
            if (any_dead)
                continue;

            if (tuple_accepting(cur) == l_true) {
                out = w;
                return true;
            }

            mts.reset();
            joint_minterms(cur, nullptr, mts);

            for (euf::snode const* mt : mts) {
                char_set cs = m_seq_regex->minterm_to_char_set(mt->get_expr());
                if (cs.is_empty())
                    continue;
                const unsigned ch = cs.first_char();
                if (!step_tuple(cur, mt, nxt))
                    continue;
                encode_into(nxt);
                if (visited.insert(key).second)
                    work.push_back({ std::move(nxt), w + zstring(ch) });
            }
        }
        return false;
    }

    // l_true: every variable's primitive intersection is non-empty (leaf feasible)
    // l_false: some variable's intersection is empty (dep set to its justification)
    // l_undef: the product search ran out of budget/resources — the leaf can be
    //          neither confirmed nor refuted and must NOT be declared SAT (the
    //          model builder could otherwise emit an unsatisfiable witness).
    lbool nielsen_graph::check_leaf_regex(nielsen_node const& node, dep_tracker& dep) {
        SASSERT(m_seq_regex);

        // distinct variables carrying a primitive constraint
        uint_set seen;
        for (auto const& mem : node.str_mems()) {
            SASSERT(mem.is_primitive());
            euf::snode const* const first = mem.m_str->first();
            SASSERT(first && first->is_var());
            if (seen.contains(first->id()))
                continue;
            seen.insert(first->id());

            vector<prod_comp> comps;
            dep_tracker d = nullptr;
            collect_var_components(first, node, comps, d);
            const lbool result = check_product_emptiness(comps, 5000);
            if (result == l_true) {
                TRACE(seq, tout << "empty intersection\n");
                dep = d;
                return l_false;
            }
            if (result == l_undef)
                return l_undef;
        }
        return l_true;
    }
}
