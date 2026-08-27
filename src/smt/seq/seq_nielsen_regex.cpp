/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen_regex.cpp

Abstract:

    Nielsen graph: the regex modifiers -- landing decomposition and its
    view variant, cycle subsumption, symbolic-derivative (ite) splitting,
    minterm variable splitting, lazy regex factorization (sigma splits)
    and the monadic-decomposition backstop.


Author:

    Clemens Eisenhofer 2026-03-02
    Nikolaj Bjorner (nbjorner) 2026-03-02

--*/

#include "smt/seq/seq_nielsen_internal.h"

namespace seq {

    // Choose the factorization boundary for `str`: split so the tail starts with
    // the LONGEST run of concrete characters c — this gives the split-engine
    // lookahead oracle the most pruning information.  head = the tokens before
    // the run; tail = the tokens AFTER the run, i.e. with c already removed (the
    // caller consumes c from each split's ∇ via δ_c derivatives).  With no
    // constant run, head is the first token, c is empty and tail the remainder.
    // Shared by split_membership (eager path) and mk_rf_state (lazy path).
    static void choose_factorization_boundary(euf::snode const* str, euf::sgraph& sg,
                                              euf::snode const*& head, euf::snode const*& tail,
                                              zstring& c) {
        seq_util& seq = sg.get_seq_util();
        euf::snode const* first = str->first();
        SASSERT(first);
        SASSERT(!first->is_char());     // constants are consumed earlier

        euf::snode_vector toks;
        str->collect_tokens(toks);
        const unsigned total = toks.size();
        unsigned run_start = 0, run_len = 0;
        for (unsigned i = 0; i < total; ) {
            if (!toks[i]->is_char()) { ++i; continue; }
            unsigned j = i;
            while (j < total && toks[j]->is_char()) ++j;
            if (j - i > run_len) { run_len = j - i; run_start = i; }
            i = j;
        }
        // No constant run → fall back to splitting off the first token.
        const unsigned p = run_len == 0 ? 1 : run_start;
        SASSERT(p >= 1);
        head = p == 1 ? first : sg.drop_right(str, total - p);

        c = zstring();
        for (unsigned i = 0; i < run_len; ++i) {
            expr* ch = nullptr;
            unsigned cv = 0;
            VERIFY(seq.str.is_unit(toks[run_start + i]->get_expr(), ch));
            VERIFY(seq.is_const_char(ch, cv));
            c = c + zstring(cv);
        }
        tail = c.empty() ? sg.drop_left(str, p) : sg.drop_left(str, run_start + run_len);
        SASSERT(head && tail);
    }

    std::pair<euf::snode const*, euf::snode const*> split_membership(euf::snode const *str, euf::snode const *regex, euf::sgraph& sg, seq_rewriter& rw, unsigned threshold, split_set& result) {
        ast_manager& m = sg.get_manager();
        euf::snode const* head;
        euf::snode const* tail;
        zstring c;
        choose_factorization_boundary(str, sg, head, tail, c);

        split_oracle oracle;
        if (!c.empty())
            oracle = [&sg, c](expr*, expr* n) { return split_lookahead_viable(n, sg, c); };

        // Decompose the regex into a split-set via the shared seq_split engine
        // (sigma from the paper): head ∈ Δ ∧ tail ∈ ∇ for each ⟨Δ,∇⟩, with the
        // lookahead oracle pruning non-viable ∇ during generation.
        // "strong" might cause explosive behavior; better do this only in the saturation
        if (!rw.split(regex->get_expr(), result, threshold, split_mode::weak, oracle)) {
            result.clear();
            return { nullptr, nullptr };
        }

        rw.simplify_split(result);

        // Eagerly consume the constant run c from the tail by taking the c-derivative
        // of each ∇:  c·tail ∈ ∇  ⟺  tail ∈ δ_c(∇)  (Brzozowski; the returned tail
        // already has c removed).  Drops any split whose ∇ cannot start with c,
        // since there δ_c(∇) = ∅ (e.g. the star rule's ⟨ε,ε⟩: δ_c(ε) = ∅ for
        // non-empty c).  This is sound because ∇ is a complete top-level component
        // (no factor appended).
        if (!c.empty()) {
            unsigned w = 0;
            for (unsigned i = 0; i < result.size(); ++i) {
                euf::snode const* d = sg.mk(result[i].m_n);
                for (unsigned k = 0; d && !d->is_fail() && k < c.length(); ++k) {
                    d = sg.brzozowski_deriv(d, sg.mk_char(c[k]));
                }
                SASSERT(d);
                if (d->is_fail())
                    continue;   // ∇ can't start with c → infeasible split, drop
                result[w++] = ::split_pair(result[i].m_d, d->get_expr(), m);
            }
            result.shrink(w);
        }

        return { head, tail };
    }

    bool split_lookahead_viable(expr* n_regex, euf::sgraph& sg, zstring const& c) {
        euf::snode const* cur = sg.mk(n_regex);
        SASSERT(cur);
        for (unsigned i = 0; i < c.length(); i++) {
            if (sg.re_nullable(cur) == l_true)
                return true;            // N accepts the prefix c[0..i) → a suffix completes it
            cur = sg.brzozowski_deriv(cur, sg.mk_char(c[i]));
            SASSERT(cur);
            if (cur->is_fail())
                return false;           // N went (syntactically) dead before reaching c
        }
        return !cur->is_fail();
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_cycle_subsumption  (paper Section "Cycle Subsumption")
    // For a membership x·u ∈ R (u≠ε) with L(⊓Reg_x) ⊆ stab(R,Q_ν), drop the
    // leading x: replace x·u ∈ R by u ∈ R.  The inclusion is decided as the
    // product-emptiness test  L(⊓Reg_x) ∩ ~stab(R,Q_ν) = ∅  (Section 3.3),
    // adding one co-view component for ~stab.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_cycle_subsumption(nielsen_node* node) {
        if (!m_regex_dynamic_decomposition)
            return false;
        for (unsigned mi = 0; mi < node->str_mems().size(); ++mi) {
            str_mem const& mem = node->str_mems()[mi];
            SASSERT(mem.well_formed());
            if (!mem.is_plain() || mem.is_primitive())
                continue;
            euf::snode const* first = mem.m_str->first();
            SASSERT(first);
            if (!first->is_var())
                continue;
            euf::snode const* R = mem.m_regex;
            if (!R->is_ground() || R->kind() == euf::snode_kind::s_ite)
                continue;

            // R must lie on a detected cycle in the explored region.  Use the
            // same reachable-Q snapshot as apply_landing_decomposition so the
            // stabilizer view stab(R,Q_ν) matches the land-at-R view.
            ensure_automaton_explored(R);
            if (!head_on_cycle(R))
                continue;
            const unsigned nu = mark_reachable_projection_edges(R);
            if (nu == 0)
                continue;

            // Decide  L(⊓Reg_x) ⊆ stab(R,Q_ν)  as  ⊓Reg_x ∩ ~stab = ∅.
            vector<prod_comp> comps;
            dep_tracker x_dep = nullptr;
            collect_var_components(first, *node, comps, x_dep);
            comps.push_back(prod_comp::mk_view(R, R, nu, projection_region(nu), /*complemented*/ true));
            if (check_product_emptiness(comps, 5000) != l_true)
                continue;

            // Subsume: replace x·u ∈ R with u ∈ R.
            euf::snode const* tail = m_sg.drop_first(mem.m_str);
            SASSERT(tail);

            nielsen_node* child = mk_child(node);
            mk_edge(node, child, "cycle subs", true);

            for (auto& cm : child->str_mems()) {
                if (cm == mem) {
                    cm.m_str = tail;
                    cm.m_dep = m_dep_mgr.mk_join(cm.m_dep, x_dep);
                    break;
                }
            }

            TRACE(seq, tout << "cycle_subsumption: dropped x=" << mk_pp(first->get_expr(), m)
                            << " from " << mk_pp(mem.m_str->get_expr(), m)
                            << " ∈ " << mk_pp(R->get_expr(), m) << " nu=" << nu << "\n");
            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_landing_decomposition  (paper §5.3 "Landing Decomposition")
    //
    // The core branching rule.  For a plain non-primitive membership x·u ∈ R
    // (u ≠ ε, x a variable, R a ground regex) we split x by WHERE its value
    // lands in the explored region Q — the states forward-reachable from R in
    // the partial DFA G — using the frontier partition (Lemma 4.7):
    //
    //   Land-at-s  (for each s ∈ Q):
    //       pin  x ∈_{Q_ν,{s}} R   (land-state view, acceptance F = {s},
    //                               current state = R) and advance to  u ∈ s.
    //       x is removed outright (no split, no guard).  s = R is stabilizer
    //       absorption: one view swallows every lap of the R-cycle.
    //
    //   Escape-via-(p,a)  (for each frontier edge p ∈ Q, δ_a(p) ∉ Q):
    //       substitute  x → x1·a·x2  (x1,x2 fresh), pin  x1 ∈_{Q_ν,{p}} R,
    //       drop x1 from the active constraint (it lands at p) leaving
    //       a·x2·u ∈ p; the normal char-consumption then steps p →a δ_a(p),
    //       recording the new edge and growing Q.
    //
    // By Lemma 4.7 the blocks partition Σ*, so the branches are exhaustive and
    // pairwise disjoint.  Character unwinding is the degenerate Q = {R} case
    // (land-at-R = x→ε; escape-via-(R,a) = x→a·x2), so this rule subsumes
    // apply_regex_var_split for ground regexes.  Views are constraint metadata
    // over the plain state R and the ν-indexed explored subautomaton Q_ν
    // (projection_state_in_Q) — nothing is materialized as a regex.
    // Termination: a landing removes a variable (active term shrinks); each
    // escape consumes a fresh state of the finite monotone G.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_landing_decomposition(nielsen_node* node) {
        if (!m_regex_dynamic_decomposition)
            return false;
        for (unsigned mi = 0; mi < node->str_mems().size(); ++mi) {
            str_mem const& mem = node->str_mems()[mi];
            SASSERT(mem.well_formed());
            if (!mem.is_plain() || mem.is_primitive())
                continue;
            euf::snode const* x = mem.m_str->first();
            SASSERT(x);
            if (!x->is_var())
                continue;
            euf::snode const* R = mem.m_regex;
            // R must be a settled ground state; an unresolved symbolic ite is
            // left to apply_regex_if_split, a non-ground regex to the var-split
            // fallback.
            if (!R->is_ground() || R->kind() == euf::snode_kind::s_ite)
                continue;

            // Explore R's reachable automaton (once, cached, BUDGETED) so the
            // SCC gate below and the landing enumeration see the explored
            // region Q.  Without it the cycle would not be recorded before
            // factorization/var_split fire, so landing would never trigger.
            // If exploration is cut off (state budget or resource limit) Q is
            // left partial — a sound under-approximation, the paper's lazy
            // mode — and the escape branches recover completeness, growing Q
            // one recorded edge at a time.
            ensure_automaton_explored(R);

            // Trigger: R must sit on a detected cycle in the explored G.  This is
            // the same gate the old split-and-guard apply_cycle_decomposition
            // used; the acyclic growth/unwinding of x is left to the pre-existing
            // flow (apply_regex_var_split / apply_regex_factorization).  Landing
            // then replaces the split+guard on cyclic heads with land-at-s +
            // escape, and is exhaustive on its own (frontier partition) so
            // preempting var_split at this node loses no words.
            if (!head_on_cycle(R))
                continue;

            // Fix the ν identifying Q for every view created below, and read Q
            // back from its snapshot.  Minting FIRST is what makes this cheap:
            // the snapshot already holds both the id set and the state handles,
            // so one reachability walk serves everything.  (The old order —
            // walk, then scan every partial-DFA edge to recover the handles,
            // then mint, which walks a second time — was three passes, two of
            // them over the whole automaton.)
            //
            // It is equivalent: compute_frontier below records only edges whose
            // target is ALREADY in Q, so Q does not grow, and the snapshot still
            // names exactly the enumerated region.  The views therefore gate on
            // precisely that region, and together with the escape blocks the
            // branches partition Σ* exactly (Lemma 4.7).
            const unsigned nu = mark_reachable_projection_edges(R);
            SASSERT(nu > 0);
            uint_set const* Qp = projection_region(nu);
            SASSERT(Qp);
            if (!Qp)
                continue;
            uint_set const& Q = *Qp;

            // mk, not find: the state exprs are pinned (m_partial_dfa_pin) but
            // their snodes may have been released by an sgraph pop since the
            // snapshot was taken — collect_projection_states re-creates them.
            svector<euf::snode const*> Qstates;
            collect_projection_states(nu, Qstates);
            // R must be present: land-at-R is the stabilizer-absorption branch,
            // and dropping it would make the split non-exhaustive (unsound UNSAT).
            if (!Qstates.contains(R))
                Qstates.push_back(R);

            // One lazy exploration step: record internal (cycle-closing) edges
            // and collect the frontier (escape candidates).
            vector<frontier_edge> frontier;
            compute_frontier(Q, Qstates, frontier);
            // The edges just recorded stay inside Q, so R's reachable set — and
            // hence its snapshot — is unchanged.  Re-stamp the head cache with
            // the new edge count so the next mint for R takes the fast path
            // instead of re-walking Q only to conclude nothing changed.
            m_projection_head_cache[R->get_expr()->get_id()] = { m_partial_dfa_edges.size(), nu };

            // Length abstraction of the region (one BFS serves every land and
            // escape pin below): every pinned view gets  len ≥ d(s)  and
            // stride | (len − d(s))  side constraints, so the outer arith
            // model can only assign the pinned variable a length the view can
            // realize (otherwise seq_model's witness search fails at the
            // assigned length and the emitted model is length-inconsistent).
            view_len_info vli;
            compute_view_length_info(nu, R->get_expr(), vli);

            sort* seq_sort = x->get_expr()->get_sort();

            // (a) LAND-AT-s branches (progress: x removed).
            for (euf::snode const* s : Qstates) {
                nielsen_node* child = mk_child(node);
                nielsen_edge* le = mk_edge(node, child, "land", /*progress*/ true);
                str_mem& cm = child->m_str_mem[mi];
                cm.m_str = m_sg.drop_first(cm.m_str);      // u
                cm.m_regex = s;                            // active becomes  u ∈ s
                // x ∈_{Q_ν,{s}} R : state = R (start), root = s (acceptance).
                child->add_str_mem(str_mem::mk_view(m, x, R, s, nu, mem.m_dep));
                add_view_length_constraints(le, vli, nu, x, s->get_expr(), mem.m_dep);
                TRACE(seq, tout << "landing: land x=" << mk_pp(x->get_expr(), m)
                                << " at " << mk_pp(s->get_expr(), m)
                                << " R=" << mk_pp(R->get_expr(), m) << " nu=" << nu << "\n");
            }

            // (b) ESCAPE branches (non-progress: consumes a fresh state, grows Q).
            for (frontier_edge const& fe : frontier) {
                euf::snode const* p = fe.m_src;
                char_set cs = m_seq_regex->minterm_to_char_set(fe.m_mt->get_expr());
                if (cs.is_empty())
                    continue;
                euf::snode const* x1 = mk_fresh_var(seq_sort);
                // Escape char: a singleton class contributes its concrete char.
                // A multi-char class must NOT be collapsed to a representative:
                // the substitution x → x1·a·x2 reaches EVERY constraint on x,
                // where the characters of p's minterm are distinguishable (other
                // memberships, equations, later derivative steps from different
                // states), so committing to one char would drop every model whose
                // escape char is another member of the class.  Use the symbolic
                // char x[|x1|] instead, range-restricted to the class; the
                // ordinary symbolic consumption + apply_regex_if_split machinery
                // then enumerates exactly the feasible sub-cases.
                const bool concrete = cs.is_unit();
                euf::snode const* aunit;
                if (concrete)
                    aunit = m_sg.mk(m_seq.str.mk_unit(m_seq.mk_char(cs.first_char())));
                else {
                    const expr_ref nth(m_seq.str.mk_nth_u(x->get_expr(), compute_length_expr(x1).get()), m);
                    aunit = m_sg.mk(m_seq.str.mk_unit(nth.get()));
                }
                // x2 = x[|x1|+1:]  (slice tail after the landed prefix and the char)
                const expr_ref after =
                    normalize_arith(m_rw, a.mk_add(compute_length_expr(x1).get(), a.mk_int(1)));
                euf::snode const* x2 = get_tail(x, after.get());
                euf::snode const* repl = m_sg.mk_concat(x1, m_sg.mk_concat(aunit, x2));

                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, "escape", /*progress*/ false);
                const nielsen_subst sub(x, repl, mem.m_dep);
                e->add_subst(sub);
                child->apply_subst(m_sg, sub);
                if (!concrete)
                    child->add_char_range(aunit, cs, mem.m_dep);

                // x1 lands at p: drop it from the active constraint, whose state
                // becomes p; the leading char is then consumed by simplify_and_init
                // (stepping p →a δ_a(p) — via apply_regex_if_split for a symbolic
                // char — and recording the edge).
                str_mem& cm = child->m_str_mem[mi];
                SASSERT(cm.m_str->first() == x1);
                cm.m_str = dir_drop(m_sg, cm.m_str, 1, true);   // a·x2·u
                cm.m_regex = p;
                // x1 ∈_{Q_ν,{p}} R
                child->add_str_mem(str_mem::mk_view(m, x1, R, p, nu, mem.m_dep));
                add_view_length_constraints(e, vli, nu, x1, p->get_expr(), mem.m_dep);
                TRACE(seq, tout << "landing: escape x=" << mk_pp(x->get_expr(), m)
                                << " via (" << mk_pp(p->get_expr(), m) << ", "
                                << (concrete ? "char " : "class first ") << cs.first_char()
                                << ") R=" << mk_pp(R->get_expr(), m)
                                << " nu=" << nu << "\n");
            }

            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_view_landing_decomposition  (paper §5.3, "Landing
    // decomposition on view constraints")
    //
    // A substitution applied throughout the node (an escape x → x1·a·x2, a
    // Nielsen split x → y·x', a power introduction, …) can hit a variable that
    // an earlier landing has pinned, turning its primitive view into the
    // NON-PRIMITIVE view constraint  y·u ∈_{Q_ν,F} p  with a leading variable
    // y.  consume_view only consumes leading characters, and letting
    // apply_regex_var_split unwind y character-by-character would re-introduce
    // exactly the cycle-unrolling divergence the views were built to prevent:
    // each lap around a cycle of p's region would spawn a fresh variable that
    // is never pinned, so the search could unroll forever.  This rule removes
    // the leading variable in one step instead:
    //
    //   p ∉ Q_ν (degenerate case):  L_{Q_ν,F}(p) ⊆ {ε}, since consuming any
    //       first character requires the gate p ∈ Q_ν.  The whole remaining
    //       LHS must denote ε: conflict if p ∉ F (ε itself inadmissible) or a
    //       character/unit token remains; otherwise deterministically
    //       substitute the LHS variables to ε.  Remaining power tokens (if
    //       any) are left to the power modifiers, whose n = 0 / peel-one split
    //       disposes of them — a peeled character dies at the gate at once.
    //
    //   p ∈ Q_ν (land-only case):  branch on WHERE the value of y lands.  Any
    //       admissible value w of the whole LHS keeps δ_{w'}(p) ∈ Q_ν for
    //       every proper prefix w' ≺ w and lands in F = {root}.  The value of
    //       y is a prefix of w: a proper prefix lands in Q_ν, and y = w (the
    //       remainder u taking ε) lands at root.  So branching s over
    //       Q_ν ∪ {root}, pinning  y ∈_{Q_ν,{s}} p  and advancing the residual
    //       to  u ∈_{Q_ν,F} s  is exhaustive, and the blocks are pairwise
    //       disjoint because the landing state is unique (determinism).  There
    //       are NO escape branches: a value of y leaving Q_ν at a proper
    //       prefix of the LHS violates the view outright.  (Unlike the paper
    //       we cannot assume a character follows y — Nielsen splits on
    //       equations create adjacent variables — which is why root joins the
    //       landing set: only proper prefixes are Q-gated, the final state is
    //       constrained to F instead.)
    //
    // Soundness is the view derivative law (Theorem "Soundness of views"),
    // applied once per character of y's value: w1 ∈ L_{Q,{s}}(p) gives
    // w1⁻¹ L_{Q,F}(p) = L_{Q,F}(s).  Termination: the leading variable is
    // removed outright, no fresh variables are introduced, and the branching
    // is over the finitely many states of Q_ν — so the "active work strictly
    // decreases between escapes" bound of the paper's termination proof
    // extends unchanged.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_view_landing_decomposition(nielsen_node* node) {
        for (unsigned mi = 0; mi < node->str_mems().size(); ++mi) {
            str_mem const& mem = node->str_mems()[mi];
            SASSERT(mem.well_formed());
            if (!mem.is_view() || mem.is_primitive())
                continue;
            euf::snode const* y = mem.m_str->first();
            SASSERT(y);
            if (!y->is_var())
                continue; // leading char/unit: consume_view; leading power: power modifiers
            euf::snode const* p = mem.m_regex;
            // The current state must be settled; an unresolved symbolic ite
            // residual is left to apply_regex_if_split.
            if (!p->is_ground() || p->kind() == euf::snode_kind::s_ite)
                continue;

            // ---- degenerate case: p ∉ Q_ν  →  L_{Q_ν,F}(p) ⊆ {ε} ----------
            if (!projection_state_in_Q(p->get_expr(), mem.m_nu)) {
                if (p != mem.m_root) {
                    // ε ∉ L_{Q_ν,{root}}(p): the view denotes ∅.
                    node->set_general_conflict();
                    node->set_conflict(backtrack_reason::regex, mem.m_dep);
                    return true;
                }
                euf::snode_vector tokens;
                mem.m_str->collect_tokens(tokens);
                if (any_of(tokens, [](euf::snode const* t) { return t->is_char_or_unit(); })) {
                    // a character remains — σ(lhs) = ε is impossible.
                    node->set_general_conflict();
                    node->set_conflict(backtrack_reason::regex, mem.m_dep);
                    return true;
                }
                // Force every variable of the LHS to ε (single deterministic
                // child; the substitution reaches all constraints, including
                // this view, whose LHS thereby shrinks).
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, "view eps", /*progress*/ true);
                uint_set done;
                for (euf::snode const* tok : tokens) {
                    if (!tok->is_var() || done.contains(tok->id()))
                        continue;
                    done.insert(tok->id());
                    const nielsen_subst s(tok, m_sg.mk_empty_seq(tok->get_sort()), mem.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                TRACE(seq, tout << "view landing: eps-forcing " << mem_pp(mem)
                                << " (state outside Q, nu=" << mem.m_nu << ")\n");
                return true;
            }

            // ---- land-only branching over Q_ν ∪ {root} --------------------
            svector<euf::snode const*> Sstates;
            collect_projection_states(mem.m_nu, Sstates);
            if (all_of(Sstates, [&](euf::snode const* s) { return s != mem.m_root; }))
                Sstates.push_back(mem.m_root);

            // Length abstraction from the current state p over the view's own
            // region (see apply_landing_decomposition): keeps the arith length
            // of the pinned y realizable in  L_{Q_ν,{s}}(p).
            view_len_info vli;
            compute_view_length_info(mem.m_nu, p->get_expr(), vli);
            uint_set const* region = projection_region(mem.m_nu);

            for (euf::snode const* s : Sstates) {
                // Skip provably-empty landing blocks (L_{Q_ν,{s}}(p) = ∅): the
                // paper's rule only branches on non-empty blocks, and this
                // keeps the fan-out at the size of p's gated region rather
                // than all of Q_ν.  Keep the branch on l_undef.  The block for
                // s = p contains ε, so at least one branch always survives.
                vector<prod_comp> block;
                block.push_back(prod_comp::mk_view(p, s, mem.m_nu, region, /*complemented*/ false));
                if (check_product_emptiness(block, 1000) == l_true)
                    continue;

                nielsen_node* child = mk_child(node);
                nielsen_edge* le = mk_edge(node, child, "view land", /*progress*/ true);
                str_mem& cm = child->m_str_mem[mi];
                cm.m_str = m_sg.drop_first(cm.m_str);   // u  (kind/root/ν stay)
                cm.m_regex = s;                         // residual  u ∈_{Q_ν,F} s
                // pin  y ∈_{Q_ν,{s}} p
                child->add_str_mem(str_mem::mk_view(m, y, p, s, mem.m_nu, mem.m_dep));
                add_view_length_constraints(le, vli, mem.m_nu, y, s->get_expr(), mem.m_dep);
                TRACE(seq, tout << "view landing: land y=" << mk_pp(y->get_expr(), m)
                                << " at " << mk_pp(s->get_expr(), m)
                                << " from " << mk_pp(p->get_expr(), m)
                                << " nu=" << mem.m_nu << "\n");
            }
            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_regex_factorization (Boolean Closure)
    // -----------------------------------------------------------------------

    // Safety cap handed to the lazy split iterator.  Large by design: the whole
    // point of the lazy factorization is that the binary child-B chain walks the
    // splits one at a time, so the count must not bound how many splits we may
    // explore.  It still guards internal materialisation of intersection /
    // complement bodies against runaway space blow-up.
    static const unsigned RF_LAZY_CAP = 1u << 20;

    rf_state* nielsen_graph::mk_rf_state(nielsen_node* /*node*/, str_mem const& mem) {
        // Boundary + constant lookahead c (see choose_factorization_boundary).
        // The constant run is consumed from the tail per split (the δ_c
        // derivative in rf_step), so the stored tail has c already removed.
        euf::snode const* head;
        euf::snode const* tail;
        zstring c;
        choose_factorization_boundary(mem.m_str, m_sg, head, tail, c);

        // Suspended sigma(regex): the iterator expands it one split at a time.
        const expr_ref suspended = m_split_rw.make_split(mem.m_regex->get_expr());
        if (!suspended)
            return nullptr;   // non-regex argument (should not happen for a well-formed mem)

        split_oracle oracle;
        if (!c.empty()) {
            euf::sgraph& sg = m_sg;
            oracle = [&sg, c](expr*, expr* n) { return split_lookahead_viable(n, sg, c); };
        }

        seq_split::iterator it =
            m_split_rw.iterate_split(suspended, RF_LAZY_CAP, split_mode::strong, oracle);
        rf_state* st = alloc(rf_state, mem, head, tail, c, std::move(it));
        m_rf_states.push_back(st);
        return st;
    }

    nielsen_graph::rf_step_result
    nielsen_graph::rf_step(nielsen_node* node, rf_state* st, dep_tracker& conflict_dep) {
        euf::snode const* const first = st->m_mem.m_str->first();
        dep_tracker eliminated_dep = st->m_mem.m_dep;

        expr_ref d(m), n(m);
        while (st->m_iter.next(d, n)) {
            // Consume the constant run c from the tail: tail = c·u''' ∈ ∇ ⟺
            // u''' ∈ δ_c(∇)  (Brzozowski).  Drops any split whose ∇ cannot start
            // with c (there δ_c(∇) = ∅).  Identity when c is empty.
            euf::snode const* sn_q = m_sg.mk(n);
            for (unsigned k = 0; sn_q && !sn_q->is_fail() && k < st->m_c.length(); ++k)
                sn_q = m_sg.brzozowski_deriv(sn_q, m_sg.mk_char(st->m_c[k]));
            SASSERT(sn_q);
            if (sn_q->is_fail())
                continue;   // ∇ can't start with c → infeasible split, skip

            euf::snode const* sn_p = m_sg.mk(d);

            // Feasibility: Δ must be non-empty.  When head is the single token
            // `first`, also intersect with other primitive constraints on `first`;
            // for a multi-token head Δ constrains the whole prefix, so we only
            // check Δ ≠ ∅.
            euf::snode_vector regexes_p;
            regexes_p.push_back(sn_p);
            dep_tracker first_filter_dep = nullptr;
            if (st->m_head == first) {
                for (auto const& prev_mem : node->str_mems()) {
                    if (prev_mem.m_str == first) {
                        regexes_p.push_back(prev_mem.m_regex);
                        first_filter_dep = m_dep_mgr.mk_join(first_filter_dep, prev_mem.m_dep);
                    }
                }
            }
            // Self-concatenation (e.g. x++x): the tail collapses back onto the
            // exact same SEQUENCE as the head, so Δ and ∇ constrain the same
            // word simultaneously and must be checked jointly -- otherwise
            // a Δ/∇ pair that is only individually non-empty (e.g. <eps, "a">)
            // is wrongly treated as feasible.  The joint check is only sound
            // when head and tail are the SAME sequence: comparing the tail
            // against `first` alone (the first token of the whole membership
            // string) also matches e.g. x·y·c·x, where head = x·y is a
            // DIFFERENT word than the tail x — intersecting Δ with ∇ there
            // over-prunes feasible splits (a spurious UNSAT).
            if (st->m_head == st->m_tail)
                regexes_p.push_back(sn_q);
            if (m_seq_regex->check_intersection_emptiness(regexes_p, 100) == l_true) {
                eliminated_dep = m_dep_mgr.mk_join(eliminated_dep, first_filter_dep);
                continue;   // infeasible split → skip without branching
            }

            const dep_tracker split_dep = m_dep_mgr.mk_join(st->m_mem.m_dep, first_filter_dep);

            // child A — the "first case": apply this split and drop the original
            // membership.
            nielsen_node* child_a = mk_child(node);
            mk_edge(node, child_a, "regex fact", true);
            auto& child_mems = child_a->str_mems();
            for (unsigned k = 0; k < child_mems.size(); ++k) {
                if (child_mems[k] == st->m_mem) {
                    child_mems[k] = child_mems.back();
                    child_mems.pop_back();
                    break;
                }
            }
            child_a->add_str_mem(str_mem(m, st->m_head, sn_p, split_dep));
            child_a->add_str_mem(str_mem(m, st->m_tail, sn_q, split_dep));

            // child B — the "did not use the first case" branch: keep the
            // membership and hand down the SAME iterator so factorization resumes
            // from the next split.  No substitution: child B is an exact clone, so
            // st->m_mem stays valid down the whole chain.
            nielsen_node* child_b = mk_child(node);
            mk_edge(node, child_b, "regex fact rest", true);
            child_b->set_rf_cont(st);

            return rf_step_result::branched;
        }

        // No feasible split remained.
        conflict_dep = eliminated_dep;
        return st->m_iter.gave_up() ? rf_step_result::gaveup : rf_step_result::conflict;
    }

    bool nielsen_graph::apply_regex_factorization(nielsen_node* node) {
        if (m_regex_factorization_threshold == 0)
            return false;

        // A node under landing control carries land-state views; the cycle
        // machinery (apply_landing_decomposition / apply_cycle_subsumption) owns
        // it, so factorization defers.
        for (str_mem const& mem : node->str_mems()) {
            if (mem.is_view())
                return false;
        }

        // Continuation: resume the iterator handed down to this node by its
        // parent's "remaining splits" branch.
        if (rf_state* st = node->rf_cont()) {
            node->set_rf_cont(nullptr);   // the iterator migrates to child B (or is dropped)
            dep_tracker conflict_dep = nullptr;
            switch (rf_step(node, st, conflict_dep)) {
            case rf_step_result::branched:
                return true;
            case rf_step_result::conflict:
                // Every split has been tried: the membership's split disjunction
                // is refuted on this branch.
                node->set_general_conflict();
                node->set_conflict(backtrack_reason::regex, conflict_dep);
                return true;
            case rf_step_result::gaveup:
                return false;   // engine give-up → let other modifiers handle the membership
            }
        }

        // Fresh: find the first factorizable membership and start an iterator.
        for (str_mem const& mem : node->str_mems()) {
            SASSERT(mem.well_formed());
            SASSERT(!mem.m_str->is_empty()); // should have been eliminated already

            // split() handles all regex forms (incl. complement / intersection),
            // so the classical restriction is no longer needed.
            if (mem.is_primitive())
                continue;

            // Land-state view memberships (paper §5.3) are handled by the cycle
            // machinery and the synchronous product, not by factorization.
            if (!mem.is_plain())
                continue;

            rf_state* st = mk_rf_state(node, mem);
            if (!st)
                continue;   // unsupported regex shape → try the next membership

            dep_tracker conflict_dep = nullptr;
            switch (rf_step(node, st, conflict_dep)) {
            case rf_step_result::branched:
                return true;
            case rf_step_result::conflict:
                node->set_general_conflict();
                node->set_conflict(backtrack_reason::regex, conflict_dep);
                return true;
            case rf_step_result::gaveup:
                continue;   // engine gave up on this membership → try the next one
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_monadic_split  (whole-language monadic decomposition)
    bool nielsen_graph::monadic_abstract_subject(euf::snode const* str, expr_ref_vector& pin,
                                                 ptr_vector<expr>& unit_vars,
                                                 vector<std::pair<euf::snode const*, expr*>>& tokens,
                                                 expr_ref& out) {
        expr_ref_vector args(m);
        bool has_var = false;
        for (euf::snode const* t : *str) {
            if (t->is_char()) {
                args.push_back(t->get_expr());
                continue;
            }
            sort* s = t->get_expr()->get_sort();
            const std::string name = "nseq.mon!" + std::to_string(t->id());
            expr_ref v(m.mk_const(symbol(name.c_str()), s), m);
            pin.push_back(v);
            // A symbolic character has unknown value but length exactly 1.
            if (t->is_unit())
                unit_vars.push_back(v);
            tokens.push_back({ t, v.get() });
            args.push_back(v);
            has_var = true;
        }
        if (!has_var)
            return false;
        out = m_seq.str.mk_concat(args, str->get_expr()->get_sort());
        pin.push_back(out);
        return true;
    }

    void nielsen_graph::ensure_monadic() {
        if (m_monadic)
            return;
        // Brzozowski, not the engine's default light-Antimirov: apply_monadic_landing
        // turns the reported reach views into land-state views over nseq's partial DFA,
        // which steps with brzozowski_deriv.  Under light-Antimirov the engine splits a
        // derivative over its top-level unions, so "x reaches q" means "SOME run ends at
        // q" -- a different relation from "the deterministic derivative run ends at q",
        // and a view built from it constrains the variable differently than the branch
        // does.  The refutations apply_monadic_split consumes are mode-independent, so
        // the one mode serves both users.
        m_monadic = alloc(seq_monadic, m_monadic_rw, m_monadic_trail,
                          seq::transition_mode::brzozowski_tm);
        // Conflict-only by default: apply_monadic_split consumes no solution.
        m_monadic->set_gen_solution(false);
    }

    bool nielsen_graph::apply_monadic_split(nielsen_node* node) {
        if (!m_monadic_split)
            return false;
        auto const& mems = node->str_mems();
        if (mems.empty())
            return false;

        ensure_monadic();

        // Abstract the plain memberships once; `src` maps back to the mems index.
        expr_ref_vector pin(m);
        vector<std::pair<expr*, expr*>> abstracted;
        vector<ptr_vector<expr>> unit_vars;
        unsigned_vector src;
        for (unsigned i = 0; i < mems.size(); ++i) {
            str_mem const& mi = mems[i];
            // A view has no plain-regex counterpart; an unresolved symbolic-derivative
            // residual (ite) belongs to apply_regex_if_split.
            if (!mi.is_plain() || mi.m_regex->is_ite())
                continue;
            expr_ref term(m);
            ptr_vector<expr> uvars;
            vector<std::pair<euf::snode const*, expr*>> toks;
            if (!monadic_abstract_subject(mi.m_str, pin, uvars, toks, term))
                continue;
            if (!m_monadic->can_decide_term(term))
                continue;
            abstracted.push_back(std::make_pair(term.get(), mi.m_regex->get_expr()));
            unit_vars.push_back(uvars);
            src.push_back(i);
        }
        const unsigned n = abstracted.size();
        if (n == 0)
            return false;

        // Decide the memberships selected by `sel` jointly; close the node if empty.
        // The conflict dependency joins only the memberships seq_monadic's core kept.
        auto close = [&](unsigned_vector const& sel) {
            m_monadic_trail.push_scope();
            obj_hashtable<expr> seen;
            for (unsigned k : sel) {
                m_monadic->add(abstracted[k].first, abstracted[k].second, mems[src[k]].m_dep);
                for (expr* v : unit_vars[k]) {
                    if (seen.contains(v))
                        continue;
                    seen.insert(v);
                    // Length-1 is unconditionally true of a symbolic character, so it
                    // carries no dependency; whenever it matters, the membership that
                    // introduced v is itself in the core.
                    expr_ref sigma(m_seq.re.mk_full_char(m_seq.re.mk_re(v->get_sort())), m);
                    pin.push_back(sigma);
                    m_monadic->add(v, sigma, nullptr);
                }
            }
            const lbool r = m_monadic->check();
            dep_tracker dep = nullptr;
            if (r == l_false)
                for (void* d : m_monadic->core())
                    dep = m_dep_mgr.mk_join(dep, static_cast<dep_tracker>(d));
            m_monadic_trail.pop_scope(1);
            TRACE(seq, tout << "MONPROBE n=" << sel.size() << " r=" << r
                            << " subj=" << mk_pp(abstracted[sel[0]].first, m) << "\n");
            if (r != l_false)
                return false;   // non-empty (l_true) or undecided (l_undef): no conclusion
            TRACE(seq, tout << "monadic split: " << sel.size() << " membership(s) jointly empty, at "
                            << mem_pp(mems[src[sel[0]]]) << "\n");
            node->set_general_conflict();
            node->set_conflict(backtrack_reason::regex, dep);
            return true;
        };

        // 1. each non-primitive membership on its own (cheap, and conclusive most often).
        for (unsigned k = 0; k < n; ++k) {
            if (mems[src[k]].m_str->length() < 2)
                continue;   // single token: plain emptiness of L(R), checked elsewhere
            unsigned_vector sel;
            sel.push_back(k);
            if (close(sel))
                return true;
        }

        // 2. all of them jointly: catches subjects that are only jointly empty through a
        //    shared variable.  check() minimizes the core, so no pre-grouping is needed.
        if (n < 2)
            return false;
        unsigned_vector all;
        for (unsigned k = 0; k < n; ++k)
            all.push_back(k);
        return close(all);
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_monadic_leaf  (monadic decomposition as an END-GAME)

    void nielsen_graph::ensure_monadic_leaf() {
        if (m_monadic_leaf_engine)
            return;
        // Default transition mode on purpose -- see the member's declaration.  This rule
        // consumes only the verdict, the core and a concrete witness, none of which are
        // tied to nseq's partial DFA, so it is free to use the mode theory_seq uses.
        m_monadic_leaf_engine = alloc(seq_monadic, m_monadic_leaf_rw, m_monadic_leaf_trail,
                                      seq::transition_mode::light_antimirov_tm);
        // The witness is the whole point of this rule.
        m_monadic_leaf_engine->set_gen_solution(true);
        m_monadic_leaf_engine->set_orientation(seq_monadic::orientation::retry);
        // Intersection refinement, off by default in the engine.  These nodes are an
        // intersection by construction -- every membership on one subject is a conjunct --
        // so without it the engine bails on exactly the re.inter/re.comp shapes this rule
        // is aimed at.  10 is theory_seq's default (smt.seq.regex_split).
        m_monadic_leaf_engine->set_split_rounds(10);
        // Bounded work, unlike theory_seq's 1000000.  theory_seq calls the engine at final
        // check, when it has nothing cheaper left to try; this rule calls it mid-search,
        // ahead of nseq's own rules, so an expensive decision here is not free -- it is
        // taken INSTEAD of a search step that might have been cheap.  Measured: a file
        // nseq's native rules close in 0.10s costs the engine ~6s to decide (theory_seq
        // needs the same 6s on it).  A budget turns that into an l_undef the rule falls
        // through on, which is the whole reason the component reports one.  Measured over
        // the regex corpus: unbounded gains 26 files and loses 4; at 300000 it gains 22
        // and loses none, and the commonly decided set runs 15% faster rather than 9%.
        if (m_monadic_leaf_budget > 0)
            m_monadic_leaf_engine->set_budget(m_monadic_leaf_budget);
    }

    bool nielsen_graph::apply_monadic_leaf(nielsen_node* node) {
        if (!m_monadic_leaf)
            return false;
        // The engine never sees equations, so its verdict is a verdict about the NODE
        // only when the node has none.  This is the eq_vars gate of mk_mon_state taken to
        // its conclusion: instead of dropping the memberships that touch an equation, do
        // not run at all until the equations are gone.
        if (!node->str_eqs().empty() || !node->str_deqs().empty())
            return false;
        // child B below is an exact clone; refusing on an alias is what stops the rule
        // from firing again all the way down that spine (see m_is_monadic_leaf_rest).
        if (node->is_signature_alias())
            return false;

        auto const& mems = node->str_mems();
        if (mems.empty())
            return false;

        ensure_monadic_leaf();

        // EVERY membership has to be covered: a satisfiable subset says nothing about the
        // node, and it is the l_true half this rule exists for.
        expr_ref_vector pin(m);
        vector<std::pair<expr*, expr*>> abstracted;
        vector<dep_tracker> mem_deps;
        vector<std::pair<euf::snode const*, expr*>> tokens;
        bool any_non_primitive = false;
        dep_tracker all_dep = nullptr;
        for (str_mem const& mi : mems) {
            if (!mi.is_plain() || mi.m_regex->is_ite())
                return false;
            expr_ref term(m);
            ptr_vector<expr> uvars;
            vector<std::pair<euf::snode const*, expr*>> toks;
            if (!monadic_abstract_subject(mi.m_str, pin, uvars, toks, term))
                return false;   // ground subject: not covered, so the verdict is partial
            // Same guard as mk_mon_state: only a free, non-rigid variable denotes an
            // unconstrained word.  Anything else abstracts to a constant the witness
            // would be free to choose but the node is not.
            if (!uvars.empty())
                return false;
            if (any_of(toks, [](auto const& p) { return !p.first->is_var() || p.first->is_rigid(); }))
                return false;
            if (!m_monadic_leaf_engine->can_decide_term(term))
                return false;
            if (!mi.is_primitive())
                any_non_primitive = true;
            for (auto const& t : toks) {
                if (!any_of(tokens, [&](auto const& p) { return p.first == t.first; }))
                    tokens.push_back(t);
            }
            abstracted.push_back({ term.get(), mi.m_regex->get_expr() });
            mem_deps.push_back(mi.m_dep);
            all_dep = m_dep_mgr.mk_join(all_dep, mi.m_dep);
        }
        // An all-primitive node is check_leaf_regex's business, and it answers the same
        // question without spending a monadic decision on it.
        if (!any_non_primitive || tokens.empty())
            return false;

        m_monadic_leaf_trail.push_scope();
        for (unsigned k = 0; k < abstracted.size(); ++k)
            m_monadic_leaf_engine->add(abstracted[k].first, abstracted[k].second, mem_deps[k]);
        const lbool r = m_monadic_leaf_engine->check();

        if (r == l_false) {
            // Explain with the engine's minimized core rather than with every membership:
            // all of them were asserted, so whatever it kept is a subset of the node's own
            // constraints and a stronger conflict clause.
            dep_tracker dep = nullptr;
            for (void* d : m_monadic_leaf_engine->core())
                dep = m_dep_mgr.mk_join(dep, static_cast<dep_tracker>(d));
            m_monadic_leaf_trail.pop_scope(1);
            ++m_stats.m_monadic_leaf_unsat;
            node->set_general_conflict();
            node->set_conflict(backtrack_reason::regex, dep);
            TRACE(seq, tout << "monadic leaf: node refuted by the end-game\n");
            return true;
        }
        if (r != l_true) {
            m_monadic_leaf_trail.pop_scope(1);
            ++m_stats.m_monadic_leaf_gaveup;
            return false;
        }

        // l_true: collapse each token's views into one concrete word.  Materialize BEFORE
        // any child is built, so that a token the engine cannot collapse costs nothing.
        vector<std::pair<euf::snode const*, expr_ref>> witness;
        for (auto const& [tok, v] : tokens) {
            expr_ref word(m);
            if (m_monadic_leaf_engine->materialize(v, word) != l_true) {
                m_monadic_leaf_trail.pop_scope(1);
                ++m_stats.m_monadic_leaf_gaveup;
                return false;
            }
            witness.push_back({ tok, word });
        }
        m_monadic_leaf_trail.pop_scope(1);

        // child A -- every token pinned to its witness word.  Adding equations is a
        // RESTRICTION of the node, so the child is sound as one disjunct however good or
        // bad the witness is; nseq's own machinery then substitutes the constants and
        // either reaches a satisfied leaf or refutes this particular witness.  Nothing
        // here trusts the engine: an equation cannot make the node easier to satisfy.
        // The witness rests on all the memberships jointly, so it carries their join.
        nielsen_node* child_a = mk_child(node);
        mk_edge(node, child_a, "monadic leaf witness", true);
        for (auto const& [tok, word] : witness)
            child_a->add_str_eq(str_eq(m, tok, m_sg.mk(word), all_dep));

        // child B -- the node unchanged.  It alone covers the parent, so completeness does
        // not depend on the witness being the right one.  The flag makes it a signature
        // alias: it must escape the sibling loop-cut against its own parent, and the rule
        // must not fire on it again (see m_is_monadic_leaf_rest).
        nielsen_node* child_b = mk_child(node);
        mk_edge(node, child_b, "monadic leaf rest", true);
        child_b->set_monadic_leaf_rest();

        ++m_stats.m_monadic_leaf_sat;
        TRACE(seq, tout << "monadic leaf: witness pinned for " << witness.size() << " token(s)\n");
        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_monadic_landing  (monadic decomposition as a branching rule)

    // Cap on the branches this rule hands out for one node: the branch count is a product
    // of per-position split degrees and every branch costs two nodes.  Overrunning it is a
    // give-up, never an exhaustion.
    static const unsigned MON_LAZY_CAP = 256;

    mon_state* nielsen_graph::mk_mon_state(nielsen_node* node) {
        ensure_monadic();   // can_decide_term is used while collecting, below
        // Enforced, not assumed: a reach view only means what a land-state view means
        // when the engine steps the same automaton the partial DFA does.  Whoever
        // changes the mode in ensure_monadic (say to give apply_monadic_split its
        // Antimirov speed back) gets a rule that stops firing, not one that answers
        // wrongly.
        if (m_monadic->mode() != seq::transition_mode::brzozowski_tm)
            return nullptr;

        // Variables constrained by a residual word (dis)equation.  seq_monadic never
        // sees those, so an `l_true` about a membership on such a variable says
        // nothing about the NODE — the equation can still be unsatisfiable with it.
        // Emitting child A there is pure overhead, and it is not symmetric: child B
        // already carries the whole problem, so on an UNSAT node child A is an extra
        // subtree to refute that can never pay off (there is no model to find).
        // Measured on noodles-unsat-2/harvest_000002: 16 such firings took the search
        // from 10 to 326 DFS nodes and 0.07 s to 6.0 s, inside ONE solve() call.
        // Where the variables ARE disjoint the two subproblems are independent and
        // the answer is informative again, so equations as such are not the gate.
        uint_set eq_vars;
        auto note_vars = [&](euf::snode const* s) {
            euf::snode_vector toks;
            s->collect_tokens(toks);
            for (euf::snode const* t : toks) {
                if (t->is_var())
                    eq_vars.insert(t->id());
            }
        };
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            note_vars(eq.m_lhs);
            note_vars(eq.m_rhs);
        }
        for (str_deq const& dq : node->str_deqs()) {
            note_vars(dq.m_lhs);
            note_vars(dq.m_rhs);
        }

        auto const& mems = node->str_mems();
        unsigned_vector covered;      // indices into mems fed to the engine
        bool any_non_primitive = false;
        expr_ref_vector pin(m);
        vector<std::pair<expr*, expr*>> abstracted;
        vector<std::pair<euf::snode const*, expr*>> tokens;   // token -> its constant
        dep_tracker dep = nullptr;

        for (unsigned i = 0; i < mems.size(); ++i) {
            str_mem const& mi = mems[i];
            // A view is owned by the landing machinery; an unresolved ite residual
            // belongs to apply_regex_if_split.
            if (!mi.is_plain() || mi.m_regex->is_ite())
                continue;
            expr_ref term(m);
            ptr_vector<expr> uvars;
            vector<std::pair<euf::snode const*, expr*>> toks;
            if (!monadic_abstract_subject(mi.m_str, pin, uvars, toks, term))
                continue;   // ground subject: nothing to decompose
            // Only a free, non-rigid variable denotes an unconstrained word.  A
            // power / replace / symbolic-character token abstracts to an
            // unconstrained constant, so the components the engine returns would
            // not be implied by the node — and here we USE them, we do not merely
            // refute with them.
            if (!uvars.empty())
                continue;
            if (any_of(toks, [](auto const& p) { return !p.first->is_var() || p.first->is_rigid(); }))
                continue;
            // Shares a variable with a residual equation: the engine's answer would
            // not be informative about the node — see eq_vars above.
            if (any_of(toks, [&](auto const& p) { return eq_vars.contains(p.first->id()); }))
                continue;
            if (!m_monadic->can_decide_term(term))
                continue;
            if (!mi.is_primitive())
                any_non_primitive = true;
            for (auto const& t : toks) {
                if (!any_of(tokens, [&](auto const& p) { return p.first == t.first; }))
                    tokens.push_back(t);
            }
            abstracted.push_back({ term.get(), mi.m_regex->get_expr() });
            covered.push_back(i);
            dep = m_dep_mgr.mk_join(dep, mi.m_dep);
        }
        // Nothing to gain unless some membership is actually non-primitive: on an
        // all-primitive node check_leaf_regex already decides the same question.
        if (!any_non_primitive || tokens.empty())
            return nullptr;

        // The iterator snapshots the memberships, so it outlives the scope they are
        // asserted in and can be suspended across other uses of the engine.
        m_monadic_trail.push_scope();
        for (auto const& [term, re] : abstracted)
            m_monadic->add(term, re, nullptr);
        seq_monadic::iterator it = m_monadic->iterate(MON_LAZY_CAP);
        m_monadic_trail.pop_scope(1);

        mon_state* st = alloc(mon_state, m, dep, std::move(it));
        st->m_pin.append(pin);
        st->m_tokens.append(tokens);
        for (unsigned i : covered) {
            st->m_idx.push_back(i);
            st->m_mems.push_back(mems[i]);
        }
        m_mon_states.push_back(st);
        return st;
    }

    bool nielsen_graph::mon_map_branch(mon_state* st,
                                       obj_map<expr, seq::view_vector> const& solution,
                                       vector<str_mem>& components) {
        // A reach view means "drive the automaton from `state` to `target`" with no region
        // restriction, whereas a node view is gated on Q_nu.  The two coincide when Q_nu
        // holds every state a run from `state` can visit, which is the case when it is the
        // COMPLETE reachable set of a membership's regex -- so only fully explored regexes
        // mint a nu, and each view takes the nu whose region contains both its states.
        // That test does double duty: it also verifies that the engine's state terms
        // canonicalize (via mk_rewrite) onto the snodes the partial DFA was built from.
        unsigned_vector nus;
        for (str_mem const& mem : st->m_mems) {
            euf::snode const* R = mem.m_regex;
            unsigned nu = 0;
            if (R->is_ground() && ensure_automaton_explored(R))
                nu = mark_reachable_projection_edges(R);
            nus.push_back(nu);
        }
        auto region_for = [&](euf::snode const* a, euf::snode const* b) {
            for (unsigned nu : nus) {
                if (nu != 0 && projection_state_in_Q(a->get_expr(), nu)
                    && projection_state_in_Q(b->get_expr(), nu))
                    return nu;
            }
            return 0u;
        };

        // Driven by the recorded tokens rather than by the solution map: every covered
        // membership has a non-ground subject whose every token is a free variable, so
        // each token must carry at least one view or child A would drop a membership
        // without replacing it (and stop being a strengthening).  Iterating the vector
        // also keeps the emitted order independent of expression addresses.
        for (auto const& [tok, var] : st->m_tokens) {
            seq::view_vector views;
            if (!solution.find(var, views))
                return false;
            for (auto const& c : views) {
                euf::snode const* state = mk_rewrite(c.m_state);
                if (!state)
                    return false;
                if (c.is_membership()) {
                    components.push_back(str_mem(m, tok, state, st->m_dep));
                    continue;
                }
                euf::snode const* target = mk_rewrite(c.m_target);
                const unsigned nu = target ? region_for(state, target) : 0;
                if (nu == 0)
                    return false;
                components.push_back(str_mem::mk_view(m, tok, state, target, nu, st->m_dep));
            }
        }
        return true;
    }

    bool nielsen_graph::mon_view_lengths(vector<str_mem> const& components, nielsen_edge* e) {
        // The abstraction is the only length information child A gets for a view, so
        // the rule cannot run soundly without it.
        if (!m_view_length_constraints)
            return false;
        for (str_mem const& c : components) {
            // A plain component is still picked up by generate_node_length_constraints.
            if (!c.is_view())
                continue;
            view_len_info vli;
            compute_view_length_info(c.m_nu, c.m_regex->get_expr(), vli);
            if (!vli.m_ok)
                return false;
            expr* to = c.m_root->get_expr();
            // region_for put BOTH endpoints inside Q_nu, so the in-Q branch of
            // add_view_length_constraints is the one that applies and it needs `to`
            // to be gated-reachable from the head.  An unreachable target means the
            // view language is empty -- true, but not expressible as a length
            // constraint, and here there is no residual membership left to kill the
            // branch at its leaf.
            if (!projection_state_in_Q(to, c.m_nu) || !vli.m_dist.contains(to->get_id()))
                return false;
            if (e)
                add_view_length_constraints(e, vli, c.m_nu, c.m_str, to, c.m_dep);
        }
        return true;
    }

    nielsen_graph::mon_step_result nielsen_graph::mon_step(nielsen_node* node, mon_state* st) {
        auto const& mems = node->str_mems();
        // The chain is made of exact clones, so the covered memberships must still sit
        // where they were, as the very same snodes.  By IDENTITY, not str_mem::operator==,
        // which is slice-insensitive (1.10b): child A drops whatever is AT THESE POSITIONS
        // and replaces it by components over the recorded tokens, so a merely similar
        // membership would be dropped without being replaced.
        dep_tracker dep = nullptr;
        for (unsigned k = 0; k < st->m_idx.size(); ++k) {
            if (st->m_idx[k] >= mems.size())
                return mon_step_result::gaveup;
            str_mem const& at = mems[st->m_idx[k]];
            if (at.m_str != st->m_mems[k].m_str || at.m_regex != st->m_mems[k].m_regex ||
                at.m_kind != st->m_mems[k].m_kind)
                return mon_step_result::gaveup;
            dep = m_dep_mgr.mk_join(dep, at.m_dep);
        }
        // Deps grow along the chain (a simplification pass can join a source into a
        // membership without touching its subject or regex), so take them from the node
        // being extended: the components and a drain conflict must name all of them.
        st->m_dep = dep;

        obj_map<expr, seq::view_vector> solution;
        while (st->m_iter.next(solution)) {
            // An unmappable branch is not a refuted one, so the enumeration stops being
            // complete and its end may then only fall through (see mon_state::m_lossy).
            // is_reversed would key the views on the reversed reading of the variable;
            // the enumerator always reads forwards, so that is a guard, not a live path.
            vector<str_mem> components;
            if (solution.empty() || m_monadic->is_reversed()
                || !mon_map_branch(st, solution, components)
                || !mon_view_lengths(components, nullptr)) {
                st->m_lossy = true;
                continue;
            }

            // child A -- the covered memberships replaced by this branch's components.
            // Each component implies its membership, so the child is a STRENGTHENING of
            // the node: sound as one disjunct.  That holds in the STRING dimension only:
            // the components must also carry the length information of the memberships
            // they replace, which is what mon_view_lengths emits below (and which the
            // guard above already established is available).
            nielsen_node* child_a = mk_child(node);
            nielsen_edge* e_a = mk_edge(node, child_a, "monadic landing", true);
            auto& child_mems = child_a->str_mems();
            for (unsigned k = st->m_idx.size(); k-- > 0; ) {
                child_mems[st->m_idx[k]] = child_mems.back();
                child_mems.pop_back();
            }
            for (auto const& c : components)
                child_a->add_str_mem(c);
            // The strengthening only holds once the views carry their length
            // abstraction: the plain memberships just dropped were the sole source of
            // length information for these tokens on this child.  Validated above, so
            // the emission cannot fail here.
            VERIFY(mon_view_lengths(components, e_a));

            // child B -- the node unchanged, carrying the SAME enumerator so the next
            // branch is taken when it is extended.  It alone covers the parent, so the
            // split is exhaustive whatever the enumerator does.
            nielsen_node* child_b = mk_child(node);
            mk_edge(node, child_b, "monadic landing rest", true);
            child_b->set_monadic_cont(st);

            ++m_stats.m_monadic_branches;
            TRACE(seq, tout << "monadic landing: branch " << st->m_iter.count() << ", "
                            << st->m_mems.size() << " membership(s) -> "
                            << components.size() << " component(s)\n");
            return mon_step_result::branched;
        }

        // Drained: every branch was either handed to a child A above us or refuted by the
        // engine -- but only if nothing was lost on the way.
        if (st->m_iter.gave_up() || st->m_lossy)
            return mon_step_result::gaveup;
        ++m_stats.m_monadic_drained;
        return mon_step_result::conflict;
    }

    bool nielsen_graph::apply_monadic_landing(nielsen_node* node) {
        if (!m_monadic_landing)
            return false;

        // Resume the enumerator handed down by the parent's "remaining branches" child.
        // The pointer migrates to the next child B, exactly as the factorization iterator
        // does; a fresh state that reports nothing is dropped again right away.
        mon_state* st = node->monadic_cont();
        const bool fresh = !st;
        if (st)
            node->set_monadic_cont(nullptr);        else {
            // Never START on a node that aliases its parent's string signature: one of our
            // own spent continuations (a fresh enumerator would restart at branch 1
            // forever), a factorization continuation (whose live split iterator neither of
            // our children would inherit), or any exact clone -- all of them are exempt
            // from the loop cut and the unsat cache, so nothing would stop the resulting
            // N -> B -> B_B -> ... descent.  The parent has already had its chance on the
            // identical constraint set.
            if (node->is_signature_alias())
                return false;
            st = mk_mon_state(node);
            if (!st)
                return false;
        }

        switch (mon_step(node, st)) {
        case mon_step_result::branched:
            if (fresh) ++m_stats.m_monadic_fresh; else ++m_stats.m_monadic_resumed;
            return true;
        case mon_step_result::conflict:
            if (fresh) ++m_stats.m_monadic_fresh; else ++m_stats.m_monadic_resumed;
            node->set_general_conflict();
            node->set_conflict(backtrack_reason::regex, st->m_dep);
            return true;
        default:
            ++m_stats.m_monadic_gaveup;
            if (fresh) {
                SASSERT(m_mon_states.back() == st);
                m_mon_states.pop_back();
                dealloc(st);
            }
            return false;
        }
    }

    bool nielsen_graph::apply_regex_if_split(nielsen_node *node) {
        bool_rewriter brw(m);
        for (str_mem const &mem : node->str_mems()) {
            SASSERT(mem.well_formed());

            expr *r_expr = mem.m_regex->get_expr();
            expr_ref c(m), th(m), el(m);
            if (!brw.decompose_ite(r_expr, c, th, el))
                continue;

            bool created = false;

            // Worklist: (regex_expr, accumulated_conditions).
            // Call decompose_ite in a loop until no more ite sub-expressions,
            // branching on c=true and c=false and accumulating conditions.
            vector<std::pair<expr_ref, expr_ref_vector>> worklist;
            worklist.push_back({expr_ref(r_expr, m), expr_ref_vector(m)});

            while (!worklist.empty()) {
                auto [r, cs] = std::move(worklist.back());
                worklist.pop_back();

                if (m_seq.re.is_empty(r))
                    continue;

                expr_ref c2(m), th2(m), el2(m);
                if (!brw.decompose_ite(r, c2, th2, el2)) {
                    // No ite remaining: leaf → create child node with regex updated to r.
                    // Canonicalize with th_rewriter so that the resolved leaf shares
                    // its snode id with the corresponding partial-DFA state (which is
                    // built by brzozowski_deriv); otherwise un-simplified residuals
                    // like (a|∅)·R≠a·R break view Q-membership checks.
                    euf::snode const* new_regex_snode = mk_rewrite(r);
                    nielsen_node *child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, "regex if", true);
                    for (const auto f : cs) {
                        e->add_side_constraint(constraint(f, mem.m_dep, m));
                    }
                    for (str_mem &cm : child->str_mems()) {
                        if (cm == mem) {
                            cm.m_regex = new_regex_snode;
                            break;
                        }
                    }
                    created = true;
                    continue;
                }

                expr_ref c_simp(c2, m);
                m_rw(c_simp);

                if (m.is_true(c_simp)) {
                    if (!m_seq.re.is_empty(th2))
                        worklist.push_back({th2, std::move(cs)});
                }
                else if (m.is_false(c_simp)) {
                    if (!m_seq.re.is_empty(el2))
                        worklist.push_back({el2, std::move(cs)});
                }
                else {
                    if (!m_seq.re.is_empty(th2)) {
                        expr_ref_vector cs_true(cs);
                        cs_true.push_back(c2);
                        worklist.push_back({th2, std::move(cs_true)});
                    }
                    if (!m_seq.re.is_empty(el2)) {
                        expr_ref_vector cs_false(cs);
                        cs_false.push_back(mk_not(c2));
                        worklist.push_back({el2, std::move(cs_false)});
                    }
                }
            }

            if (created)
                return true;

            // The worklist only ever prunes ∅ branches, so no created child
            // means every valuation of the ite conditions collapses the regex
            // to ∅ — the membership is unsatisfiable outright.  Report the
            // definite regex conflict instead of falling through to weaker
            // modifiers (or, for a view state, to none at all → VERIFY(ext)).
            // Justified by the membership alone: the conditions are part of
            // the regex itself.
            node->set_general_conflict();
            node->set_conflict(backtrack_reason::regex, mem.m_dep);
            return true;
        }
        return false;
    }
    // -----------------------------------------------------------------------
    // Modifier: apply_regex_var_split
    // For str_mem x·s ∈ R where x is a variable, split using minterms:
    //   (1) x → ε (empty)
    //   (2) x → c · x' for each minterm character class c
    // More general than regex_char_split; uses minterm partitioning rather
    // than just extracting concrete characters.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_regex_var_split(nielsen_node* node) {
        for (str_mem const& mem : node->str_mems()) {
            SASSERT(mem.well_formed());
            if (mem.is_primitive())
                continue;
            euf::snode const* first = mem.m_str->first();
            SASSERT(first);
            // This modifier handles x·s ∈ R where x is a variable.  A non-var
            // leading token (e.g. a power u^n) must NOT be substituted as if it
            // were a free variable — that is unsound (it discards the power's
            // semantics, producing an invalid model).  Leave it for the
            // power-aware modifiers (apply_var_num_unwinding_mem etc.).
            if (!first->is_var())
                continue;

            // std::cout << "Considering regex: " << spp(mem.m_regex, m) << std::endl;

            // Branch 1: x → ε (progress)
            {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, "regex var split", true);
                const nielsen_subst s(first, m_sg.mk_empty_seq(first->get_sort()), mem.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
            }

            euf::snode const* tail = get_tail(first, 1, true);

            // Branch 2..k: x → c · x' per JOINT minterm of every constraint on x.
            // Option (b) — synchronize at var-split time.  Instead of unwinding to
            // a single symbolic char ?c and letting each of x's constraints (the
            // primary membership, any pinned land-state views) derive ?c
            // into its own ite — which apply_regex_if_split then resolves
            // independently, materializing a cross-product of their states — we
            // branch directly on the joint minterm partition of all of x's
            // constraint regexes.  A SINGLETON minterm contributes its concrete
            // character, which every constraint on x then consumes synchronously —
            // no ites, no cross-product.  A multi-char minterm must NOT be
            // collapsed to a concrete representative: the minterms are joint only
            // over the memberships x LEADS, while equations, disequations and
            // non-leading occurrences of x can still distinguish characters within
            // the class (committing to one char would drop every model whose first
            // char is another member — unsound UNSAT).  Such classes get the
            // symbolic char ?c range-restricted to the class instead, paying the
            // ite resolution only where it is needed for completeness.
            euf::snode_vector states;
            for (auto const& m2 : node->str_mems())
                if (m2.m_str->first() == first)
                    states.push_back(m2.m_regex);

            euf::snode const* combined = states[0];
            for (unsigned i = 1; i < states.size(); ++i)
                combined = m_sg.mk(m_seq.re.mk_inter(combined->get_expr(), states[i]->get_expr()));

            euf::snode_vector minterms;
            if (combined->is_ground())
                m_sg.compute_minterms(combined, minterms);

            if (!minterms.empty()) {
                for (euf::snode const* mt : minterms) {
                    char_set cs = m_seq_regex->minterm_to_char_set(mt->get_expr());
                    if (cs.is_empty())
                        continue;
                    const bool concrete = cs.is_unit();
                    euf::snode const* cunit = concrete
                        ? m_sg.mk(m_seq.str.mk_unit(m_seq.mk_char(cs.first_char())))
                        : m_sg.mk(get_or_create_char_var(first));
                    euf::snode const* replacement = m_sg.mk_concat(cunit, tail);
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, "regex var split", false);
                    const nielsen_subst s(first, replacement, mem.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                    if (!concrete)
                        child->add_char_range(cunit, cs, mem.m_dep);
                }
                return true;
            }

            // Fallback (non-ground / no minterms): a single symbolic char child.
            euf::snode const* fresh_char = m_sg.mk(get_or_create_char_var(first));
            euf::snode const* replacement = m_sg.mk_concat(fresh_char, tail);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, "regex var split", false);
            const nielsen_subst s(first, replacement, mem.m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);

            return true;
        }
        return false;
    }
}
