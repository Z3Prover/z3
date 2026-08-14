/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen_search.cpp

Abstract:

    Nielsen graph: the search driver -- iterative-deepening DFS
    (solve / search_dfs) with the subsumption (loop-cut) rule and the
    unsat transposition table, the modifier dispatcher
    (generate_extensions), the incremental eager closure chain and
    conflict-dependency collection.


Author:

    Clemens Eisenhofer 2026-03-02
    Nikolaj Bjorner (nbjorner) 2026-03-02

--*/

#include "smt/seq/seq_nielsen_internal.h"

namespace seq {

    // -----------------------------------------------------------------------
    // nielsen_graph: search
    // -----------------------------------------------------------------------

    void nielsen_graph::apply_parikh_to_node(nielsen_node& node) const {
        if (!m_parikh_enabled || node.m_parikh_applied)
            return;
        node.m_parikh_applied = true;

        // Generate modular length constraints (len(str) = min_len + stride·k, etc.)
        // and append them to the node's integer constraint list.
        m_parikh->apply_to_node(node);

        // Lightweight feasibility pre-check: does the Parikh modular constraint
        // contradict the variable's current integer bounds?  If so, mark this
        // node as a Parikh-image conflict immediately (avoids a solver call).
        dep_tracker parikh_dep = nullptr;
        if (!node.is_currently_conflict() && m_parikh->check_parikh_conflict(node, parikh_dep) != nullptr) {
            node.set_general_conflict();
            node.set_conflict(backtrack_reason::parikh_image, parikh_dep);
        }
    }

    void nielsen_graph::assert_root_constraints_to_solver() {
        if (m_root_constraints_asserted)
            return;
        m_root_constraints_asserted = true;
        // Constraint.Shared: assert all root-level length/Parikh constraints
        // to m_solver at the base level (no push/pop). These include:
        //   - len(lhs) = len(rhs) for each non-trivial string equality
        //   - len(str) >= min_len and len(str) <= max_len for each regex membership
        //   - len(x) >= 0 for each variable appearing in the root constraints
        // Making these visible to the solver before the DFS allows arithmetic
        // pruning at every node, not just the root.
        vector<length_constraint> constraints;
        generate_length_constraints(constraints);
        for (auto const& lc : constraints) {
            m_root->add_constraint(lc.to_constraint());
        }
    }

    nielsen_graph::search_result nielsen_graph::solve() {
        SASSERT(m_root);

        try {
            ++m_stats.m_num_solve_calls;
            // new solve = possibly new external context (outer bounds / literal
            // assignments): let every node re-simplify once under it
            ++m_simplify_epoch;
            clear_sat_node();

            TRACE(seq, tout << "Solve call " << m_stats.m_num_solve_calls << "\n");

            // Constraint.Shared: assert root-level length/Parikh constraints to the
            // solver at the base level, so they are visible during all feasibility checks.
            assert_root_constraints_to_solver();

            if (harvest_mode()) {
                // Benchmark-harvest mode: a single fixed-depth DFS pass at the harvest
                // bound (no iterative deepening, to avoid re-harvesting / divergence).
                // Every branch reaching the bound dumps a snapshot of the current node
                // and returns unknown; SAT leaves also return unknown (see search_dfs),
                // so the whole pass returns unknown.  theory_nseq turns this into a
                // blocking clause to force the SAT solver onto a different assignment.
                m_depth_bound = m_harvest;
                ptr_vector<nielsen_edge> cur_path;
                m_siblings.clear();
                const unsigned before = m_stats.m_num_dfs_nodes;
                search_dfs(m_root, cur_path);
                IF_VERBOSE(2, verbose_stream() << "nseq harvest: DFS explored "
                    << (m_stats.m_num_dfs_nodes - before) << " nodes (bound="
                    << m_depth_bound << ")\n");
                ++m_stats.m_num_unknown;
                return search_result::unknown;
            }

            // Iterative deepening: double the bound on each failure.
            // m_max_search_depth == 0 means unlimited; otherwise stop when bound exceeds it.
            m_depth_bound = 3;
            while (true) {
                if (!m.inc()) {
#ifdef Z3DEBUG
                    // Examining the Nielsen graph is probably the best way of debugging
                    const std::string dot = to_dot();
                    IF_VERBOSE(1, verbose_stream() << dot << "\n";);
                    IF_VERBOSE(1, display(verbose_stream()));
#endif
                    break;
                }
                if (m_max_search_depth > 0 && m_depth_bound > m_max_search_depth)
                    break;
                ptr_vector<nielsen_edge> cur_path;
                // The active-path index is per-traversal; clear it so a sat-aborted
                // previous iteration cannot leave stale ancestors behind.
                m_siblings.clear();
                // TODO: scope m_dep_mgr around the traversal to gc dependencies
                // after the search (the dep arena only ever grows within a solve).
                SASSERT(!m_root->is_currently_conflict());
                const search_result r = search_dfs(m_root, cur_path); // the main search loop
                IF_VERBOSE(1, verbose_stream()
                                  << " depth_bound=" << m_depth_bound << " dfs_nodes=" << m_stats.m_num_dfs_nodes
                                  << " max_depth=" << m_stats.m_max_depth << " extensions=" << m_stats.m_num_extensions
                                  << " arith_prune=" << m_stats.m_num_arith_infeasible << " result="
                                  << (r == search_result::sat     ? "SAT"
                                      : r == search_result::unsat ? "UNSAT"
                                                                  : "UNKNOWN")
                                  << "\n";);
                if (r == search_result::sat) {
                    IF_VERBOSE(1,
                        verbose_stream() << "side constraints: \n";
                        for (auto const &c : cur_path.back()->side_constraints()) {
                            verbose_stream() << "  side constraint: " << c.fml << "\n";
                        });
                    ++m_stats.m_num_sat;
                    SASSERT(m_sat_node != nullptr);
                    return r;
                }
                if (r == search_result::unsat) {
                    ++m_stats.m_num_unsat;
                    const auto deps = collect_conflict_deps();
                    m_conflict_sources.reset();
                    m_dep_mgr.linearize(deps, m_conflict_sources);
                    TRACE(seq, display(tout, m_root));
                    return r;
                }
                // depth limit hit – double the bound and retry
                if (m_depth_bound < INT_MAX/2)
                    m_depth_bound *= 2;
                SASSERT(m_depth_bound < INT_MAX);
            }
            ++m_stats.m_num_unknown;
            return search_result::unknown;
        }
        catch(const std::exception& e) {
#ifdef Z3DEBUG
            std::string dot = to_dot();
#endif
            throw;
        }
    }

    void nielsen_graph::eager_begin() {
        reset();
        create_root();
        m_eager_leaf = m_root;
        m_eager_substs.reset();
        m_eager_active = true;
    }

    euf::snode const* nielsen_graph::eager_rewrite(euf::snode const* s, dep_tracker& dep) {
        for (auto const& sub : m_eager_substs) {
            s = m_sg.subst(s, sub.m_var, sub.m_replacement);
            dep = m_dep_mgr.mk_join(dep, sub.m_dep);
        }
        return s;
    }

    void nielsen_graph::eager_add_str_eq(euf::snode const* lhs, euf::snode const* rhs, smt::enode* l, smt::enode* r) {
        SASSERT(m_eager_active && m_eager_leaf);
        dep_tracker dep = m_dep_mgr.mk_leaf(enode_pair(l, r));
        lhs = eager_rewrite(lhs, dep);
        rhs = eager_rewrite(rhs, dep);
        str_eq eq(m, lhs, rhs, dep);
        eq.sort();
        m_eager_leaf->add_str_eq(eq);
    }

    void nielsen_graph::eager_add_str_deq(euf::snode const* lhs, euf::snode const* rhs, sat::literal lit) {
        SASSERT(m_eager_active && m_eager_leaf);
        dep_tracker dep = m_dep_mgr.mk_leaf(lit);
        lhs = eager_rewrite(lhs, dep);
        rhs = eager_rewrite(rhs, dep);
        str_deq deq(m, lhs, rhs, dep);
        m_eager_leaf->add_str_deq(deq);
    }

    void nielsen_graph::eager_add_str_mem(euf::snode const* str, euf::snode const* regex, sat::literal lit) {
        SASSERT(m_eager_active && m_eager_leaf);
        dep_tracker dep = m_dep_mgr.mk_leaf(lit);
        str = eager_rewrite(str, dep);
        regex = eager_rewrite(regex, dep);
        m_eager_leaf->add_str_mem(str_mem(m, str, regex, dep));
    }

    // Drive the deterministic chain from the current leaf to a fixpoint.  Each step
    // is a single-child apply_det_modifier (progress, strictly token-reducing), so
    // this terminates without a budget.  An EMPTY path makes simplify_and_init take
    // only its assignment-independent branches (LP/arith passes 3c-else/3e are gated
    // on !cur_path.empty()); no arithmetic/length solver is touched.
    nielsen_graph::search_result nielsen_graph::eager_close() {
        SASSERT(m_eager_active && m_eager_leaf);
        ++m_stats.m_num_eager_calls;
        const ptr_vector<nielsen_edge> empty_path;

        // Rigid defined ops (str.replace_all, …) must never be Nielsen-substituted;
        // a rigid term is inherited down the whole chain, so a single check on the
        // leaf (which holds all current constraints) suffices — bail before any det
        // step (mirrors final_check's guard).
        if (m_eager_leaf->references_rigid())
            return search_result::unknown;

        auto report_conflict = [&](nielsen_node* n) {
            // The conflict node's deps already transitively include the source deps
            // of every constraint that fed it (apply_subst + eager_rewrite join the
            // substitution deps).  We must NOT use collect_conflict_deps() — it walks
            // from the root and asserts every visited node is a conflict, but only
            // the chain's last node is.
            dep_tracker deps = nullptr;
            if (n->m_conflict_external_literal != sat::null_literal)
                deps = m_dep_mgr.mk_join(deps, m_dep_mgr.mk_leaf(n->m_conflict_external_literal));
            if (n->m_conflict_internal)
                deps = m_dep_mgr.mk_join(deps, n->m_conflict_internal);
            m_conflict_sources.reset();
            m_dep_mgr.linearize(deps, m_conflict_sources);
        };

        while (true) {
            if (!m.inc())
                return search_result::unknown;
            nielsen_node* node = m_eager_leaf;

            // a substitution applied in the previous step may have produced a
            // conflict directly (e.g. an empty character-range intersection)
            if (node->is_currently_conflict()) {
                report_conflict(node);
                return search_result::unsat;
            }

            const simplify_result sr = node->simplify_and_init(empty_path);
            if (sr == simplify_result::conflict || node->is_currently_conflict()) {
                report_conflict(node);
                return search_result::unsat;
            }
            if (sr == simplify_result::satisfied || node->is_satisfied())
                return search_result::unknown; // no eager conflict; defer to solve()

            // deterministic, single-child substitution closure.  apply_det_modifier
            // only acts on word equations; membership-only structural conflicts are
            // already caught by simplify_and_init's post-passes above.
            if (!apply_det_modifier(node))
                return search_result::unknown; // would need branching; stop here

            // record the det substitution(s) and advance the leaf
            SASSERT(!node->outgoing().empty());
            nielsen_edge* e = node->outgoing().back();
            for (auto const& s : e->subst())
                m_eager_substs.push_back(s);
            m_eager_leaf = e->tgt();
        }
    }

    // ---- Transposition-table helpers (node memoization) ----------------------

    static bool reason_is_string_only(backtrack_reason r) {
        switch (r) {
        case backtrack_reason::regex:
        case backtrack_reason::regex_widening:
        case backtrack_reason::symbol_clash:
        case backtrack_reason::character_range:
        case backtrack_reason::sibling:
            return true;
        default:
            // arithmetic, parikh_image, external, children_failed, unevaluated
            return false;
        }
    }

    bool nielsen_graph::node_unsat_string_only(nielsen_node const* n) const {
        if (n->m_reason == backtrack_reason::children_failed)
            return n->m_unsat_cacheable; // set when the children_failed result was formed
        return reason_is_string_only(n->m_reason);
    }

    dep_tracker nielsen_graph::node_all_deps(nielsen_node const* n) const {
        dep_tracker d = nullptr;
        for (auto const& e : n->str_eqs()) {
            d = m_dep_mgr.mk_join(d, e.m_dep);
        }
        for (auto const& q : n->str_deqs()) {
            d = m_dep_mgr.mk_join(d, q.m_dep);
        }
        for (auto const& mm : n->str_mems()) {
            d = m_dep_mgr.mk_join(d, mm.m_dep);
        }
        for (auto const& [uid, cr] : n->char_ranges()) {
            d = m_dep_mgr.mk_join(d, cr.second);
        }
        return d;
    }

    nielsen_graph::search_result nielsen_graph::search_dfs(nielsen_node* node,
        ptr_vector<nielsen_edge>& cur_path, const unsigned depth) {

        ++m_stats.m_num_dfs_nodes;
        // std::cout << m_stats.m_num_dfs_nodes << std::endl;
        // depth is NOT necessarily the length of the path
        // Reason: Progress nodes are not counted towards the depth limit
        // Otw. problems with a lot of variables would barely terminate
        SASSERT(depth <= cur_path.size());
        m_stats.m_max_depth = std::max(m_stats.m_max_depth, depth);

        // structural depth of this node on the current DFS path (counts ALL edges,
        // unlike `depth` which discounts progress edges).  Used by the subsumption
        // rule to identify and compare ancestors.
        node->m_dfs_path_pos = cur_path.size();

        // Cut bookkeeping is per-visit: values left over from an earlier traversal
        // (hot-restart) describe a different path.  Reset them so the early unsat
        // returns below (sticky general conflict, cache hit, simplify/arith
        // conflict) report a clean, cut-free closure to the parent's fold instead
        // of leaking a stale cut.
        node->m_subtree_lowlink = UINT_MAX;
        node->m_subtree_has_cut = false;

        if (node->is_general_conflict()) {
            ++m_stats.m_num_simplify_conflict;
            return search_result::unsat;
        }

        // check for external cancellation (timeout, user interrupt)
        if (!m.inc())
            return search_result::unknown;

#ifdef Z3DEBUG
        if (m_stats.m_num_dfs_nodes % 20 == 0) {
            std::string dot = to_dot();
            std::cout << "";
        }
#endif

        // check DFS node budget (0 = unlimited)
        if (m_max_nodes > 0 && m_stats.m_num_dfs_nodes > m_max_nodes)
            return search_result::unknown;

        // we might need to tell the SAT solver about the new integer inequalities
        // that might have been added by an extension step
        assert_node_side_constraints(node);
        // Constraints below this index are asserted in THIS visit's solver
        // scope; the later calls of this visit assert only the newly added
        // tail.  (The next visit runs in a fresh scope and starts over from
        // m_parent_ic_count via the default argument.)
        unsigned ic_asserted = node->constraints().size();

        if (node->is_currently_conflict()) {
            ++m_stats.m_num_simplify_conflict;
            return search_result::unsat;
        }

        // simplify constraints (idempotent after first call)
        const simplify_result sr = node->simplify_and_init(cur_path);

        if (sr == simplify_result::conflict || node->is_general_conflict()) {
            SASSERT(node->is_general_conflict());
            ++m_stats.m_num_simplify_conflict;
            node->set_general_conflict();
            return search_result::unsat;
        }

        // Transposition-table lookup.  The node is now canonical (post-simplify).
        // If an equivalent node was already proven UNSAT for string/regex-only
        // reasons, this node is unsat too — independently of its (integer) side
        // constraints — so we prune without re-exploring its subtree.  We derive
        // the conflict from this node's own constraint deps (a sound over-approx).
        //
        // A lazy-factorization continuation node (rf_cont set) is EXEMPT: it shares
        // its parent's string constraints (only the suspended split iterator
        // differs), so it would alias the parent's signature, yet it still has
        // pending splits to explore — it is not a true recurrence.  The same holds
        // for an arithmetic-split child (apply_num_cmp / apply_split_power_elim):
        // it aliases its parent's signature while its branch's integer constraint
        // still awaits LP resolution one level down (see is_signature_alias).
        {
            if (!node->is_signature_alias() && m_unsat_node_cache.contains(node)) {
                // The cached UNSAT is a property of the string signature alone, so
                // THIS node's own constraint deps are a sound justification.  A null
                // dep would make the branch contribute nothing to the conflict
                // explanation — collect_conflict_deps treats sibling nodes as stop
                // points that must carry their own justification — yielding an
                // under-justified (too strong) conflict clause.
                node->set_conflict(backtrack_reason::sibling, node_all_deps(node));
                node->set_general_conflict();
                node->m_unsat_cacheable = true;
                ++m_stats.m_num_simplify_conflict;
                ++m_num_cache_hits;
                return search_result::unsat;
            }
        }

        // Apply Parikh image filter: generate modular length constraints and
        // perform a lightweight feasibility pre-check.  The filter is guarded
        // internally (m_parikh_applied) so it only runs once per node.
        // Note: Parikh filtering is skipped for satisfied nodes (returned above);
        // a fully satisfied node has no remaining memberships to filter.
        apply_parikh_to_node(*node);

        if (node->is_general_conflict()) {
            ++m_stats.m_num_simplify_conflict;
            return search_result::unsat;
        }

        // Assert any new int_constraints added during simplify_and_init for this
        // node into the current solver scope. Constraints inherited from the parent
        // (indices 0..m_parent_ic_count-1) are already present at the enclosing
        // scope level; only the newly-added tail needs to be asserted here.
        // Also generate per-node |LHS| = |RHS| length constraints for descendant
        // equations (root constraints are already at the base level).
        generate_node_length_constraints(node);
        assert_node_side_constraints(node, ic_asserted);
        ic_asserted = node->constraints().size();

        if (node->is_currently_conflict()) {
            ++m_stats.m_num_simplify_conflict;
            return search_result::unsat;
        }

        // integer feasibility check: the solver now holds all path constraints
        // incrementally; just query the solver directly
        if (!cur_path.empty() && !check_int_feasibility()) {
            const dep_tracker deps = get_subsolver_dependency(node);
            node->set_conflict(backtrack_reason::arithmetic, deps);
            node->set_general_conflict();

            ++m_stats.m_num_arith_infeasible;
            return search_result::unsat;
        }

        SASSERT(sr != simplify_result::satisfied || node->is_satisfied());
        SASSERT(!node->is_currently_conflict());

        if (node->is_satisfied()) {
            // Benchmark-harvest mode: a satisfied node has only primitive memberships
            // (uninteresting for the regex factorization benchmark) — do NOT declare SAT
            // (that would terminate the harvest loop) and do NOT harvest; just dead-end
            // this branch so the search keeps exploring others.
            if (harvest_mode())
                return search_result::unknown;
            // Before declaring SAT, check leaf-node regex feasibility:
            // for each variable with multiple regex constraints, verify
            // that the intersection of all its regexes is non-empty.
            dep_tracker dep = nullptr;
            const lbool leaf_feasible = check_leaf_regex(*node, dep);
            if (leaf_feasible == l_false) {
                node->set_general_conflict();
                node->set_conflict(backtrack_reason::regex, dep);
                // string-only conflict (empty intersection) → memoize.
                node->m_unsat_cacheable = true;
                node->canonize_and_compute_final_node_hash();
                m_unsat_node_cache.insert(node);
                return search_result::unsat;
            }
            if (leaf_feasible == l_undef)
                // The product search exhausted its budget: the leaf can be
                // neither confirmed nor refuted.  Declaring SAT here would let
                // the model builder emit a witness that may violate the very
                // constraints the check could not decide.
                return search_result::unknown;
            assert_node_side_constraints(node, ic_asserted);
            // We need to have everything asserted before reporting SAT
            // (otw. the outer solver might assume false-assigned literals to be true)
            if (node->is_currently_conflict()) {
                ++m_stats.m_num_simplify_conflict;
                return search_result::unsat;
            }
            node->canonize_and_compute_final_node_hash();
            set_sat_node(node);
            m_sat_path = cur_path;
            return search_result::sat;
        }

        if (node->is_currently_conflict())
            return search_result::unsat;

        // -------------------------------------------------------------------
        // Subsumption rule (Nielsen loop-cut).
        // If this node has the SAME string constraints as a node further up the
        // current DFS path (an ancestor "sibling"), then every continuation from
        // here is already being explored from that ancestor.  We must NOT report a
        // conflict: the arithmetic side-constraints accumulated along the two paths
        // differ, so a model may exist here that does not at the ancestor.  Instead
        // we CUT — return unsat provisionally and remember (in m_subtree_lowlink)
        // the structural depth of the ancestor we defer to.  A cut only hardens
        // into a genuine conflict at an enclosing node whose entire subtree closes
        // with string-only conflicts and self-contained cuts (see the epilogue).
        // -------------------------------------------------------------------
        node->canonize_and_compute_final_node_hash();
        // A lazy-factorization continuation node (is_rf_cont) is EXEMPT from the
        // loop-cut: it aliases its parent's string signature (only the suspended
        // split iterator differs) but is not a true recurrence — it still has
        // pending splits.  The iterator is finite, so the continuation chain
        // terminates on its own (exhaustion → regex conflict).  The exemption uses
        // the STICKY is_rf_cont() marker, not the live rf_cont() pointer: the
        // pointer is nulled once the node is extended, but on a hot-restart the
        // node is re-traversed without re-extending, and it must stay exempt (else
        // it is wrongly cut as a sibling of the ancestor it aliases, pruning a
        // branch that may still lead to SAT).
        // An arithmetic-split child (apply_num_cmp / apply_split_power_elim) is
        // exempt for the analogous reason: it is string-identical to its parent BY
        // CONSTRUCTION — only the edge's integer side constraint differs — and
        // exists so that simplify_and_init's LP passes resolve the power
        // cancellation one level down.  Cutting it as a sibling of its parent when
        // the LP is inconclusive (l_undef) would let the parent close as a
        // "string-only" conflict built purely from cuts — a spurious UNSAT.  With
        // the exemption an unresolved chain instead runs into the resource/node
        // budget and returns unknown, the sound degradation for an LP timeout.
        if (!node->is_signature_alias()) {
            auto it = m_siblings.find(node);
            if (it != m_siblings.end() && !it->second.empty()) {
                nielsen_node* anc = it->second.back(); // deepest sibling still on the path
                SASSERT(anc != node);
                // deps are a sound over-approximation (the node's own constraint
                // sources); only used if a children_failed ancestor recurses here.
                node->set_conflict(backtrack_reason::sibling, node_all_deps(node));
                node->m_subtree_lowlink = anc->m_dfs_path_pos; // escape level
                node->m_subtree_has_cut = true;
                ++m_stats.m_num_sibling_cut;
                return search_result::unsat;
            }
        }

        // depth bound check
        if (depth >= m_depth_bound) {
            // Benchmark-harvest mode: this node has reached the configured number of
            // non-progress extension steps and is a genuine intermediate state
            // (post-simplify, post-Parikh, not a conflict, not satisfied) whose
            // memberships are the rewritten (often non-primitive) ones we want.
            // Dump the snapshot, then backtrack.
            if (harvest_mode())
                harvest_node(node);
            return search_result::unknown;
        }

        SASSERT(!node->is_currently_conflict());

        // generate extensions only once per node; children persist across runs
        if (!node->is_extended()) {
            const bool ext = generate_extensions(node);
            // Benchmark-harvest mode: with all regex modifiers disabled, a node whose
            // only remaining work is on (non-primitive) memberships has no applicable
            // word-equation modifier, so generate_extensions yields nothing.  This is a
            // harvest leaf: dump the snapshot and backtrack instead of failing the
            // VERIFY(ext) below.
            if (harvest_mode() && !ext) {
                harvest_node(node);
                return search_result::unknown;
            }
            IF_VERBOSE(1, display(verbose_stream(), node));
            CTRACE(seq, !ext, display(tout, node) << to_dot() << "\n");
            if (!ext) {
                std::cout << "No extensions generated for node " << node->id() << ", but not satisfied or conflict?!"
                          << std::endl;
                node->to_html(std::cout, m);
                std::cout << std::endl;
                display(std::cout, node);
            }
            VERIFY(ext);

            if (node->is_currently_conflict())
                // in rare cases, trying to extend can make a complicated conflict visible
                return search_result::unsat;

            node->set_extended(true);
            ++m_stats.m_num_extensions;
        }

        // Register this node on the active path so descendants can detect a loop
        // back to it (the subsumption cut above).  The hash/signature is already
        // computed (cut check) so the structural key is stable.  Popped after the
        // child loop.  A bucket holds at most one on-path node per signature
        // (a second equal node on the path would have been cut before reaching here).
        m_siblings[node].push_back(node);

        // explore children
        bool any_unknown = false;
        bool all_general_conflict = true;
        bool subtree_has_cut = false;         // a sibling loop-cut occurred below
        unsigned min_child_lowlink = UINT_MAX; // min depth any sibling cut below escapes to
        for (nielsen_edge *e : node->outgoing()) {
            cur_path.push_back(e);
            // Push a solver scope for this edge and assert its side integer
            // constraints.  The child's own new constraints will be asserted
            // inside the recursive call (above).  On return, pop the scope so
            // that backtracking removes those assertions.
            m_length_solver.push();

            // Lazily compute substitution length constraints (|x| = |u|) on first
            // traversal. This must happen before asserting side_constraints
            if (!e->len_constraints_computed()) {
                add_subst_length_constraints(e);
                e->set_len_constraints_computed(true);

                for (const auto& sc : e->side_constraints()) {
                    e->tgt()->add_constraint(sc);
                }
            }

            const auto new_depth = depth + (e->is_progress() ? 0 : 1);
            const search_result r = search_dfs(e->tgt(), cur_path, new_depth);

            m_length_solver.pop(1);
            if (r == search_result::sat)
                // m_siblings entry is left dangling; it is cleared at the start of
                // the next iteration (and the whole search returns sat now anyway).
                return search_result::sat;
            cur_path.pop_back();
            if (r == search_result::unknown)
                any_unknown = true;
            else { // unsat: fold the child's lowlink (cut escape level) into ours
                min_child_lowlink = std::min(min_child_lowlink, e->tgt()->m_subtree_lowlink);
                subtree_has_cut |= e->tgt()->m_subtree_has_cut;
            }
            if (!e->tgt()->is_general_conflict())
                all_general_conflict = false;
        }

        // leave the active path (mirrors the push above)
        SASSERT(!m_siblings[node].empty() && m_siblings[node].back() == node);
        m_siblings[node].pop_back();

        if (all_general_conflict) {
            SASSERT(!any_unknown);
            // mark it such that we do not have to reconsider it even after a hot-restart
            node->set_general_conflict();
        }
        node->m_subtree_has_cut = subtree_has_cut;
        if (!any_unknown) {
            // The subtree closed.  Record our lowlink and decide how strong a
            // conflict we may claim.  self_contained == no sibling cut below
            // escapes above this node, i.e. every loop is internal to our subtree.
            node->m_subtree_lowlink = min_child_lowlink;
            const bool self_contained = (min_child_lowlink >= node->m_dfs_path_pos);

            // string-only closure: every leaf below is a string-only conflict or a
            // sibling cut (cuts count as string-only, see reason_is_string_only).
            bool all_string_only = true;
            for (nielsen_edge* e : node->outgoing()) {
                if (!node_unsat_string_only(e->tgt())) {
                    all_string_only = false;
                    break;
                }
            }

            // Soundness of the subsumption rule: a loop-cut defers to an ancestor
            // whose arithmetic side-constraints differ from this path's, so a cut is
            // only a valid UNSAT witness when the WHOLE closure is string-only.  If a
            // cut coexists with an arithmetic / Parikh / external conflict, the cut
            // may be hiding a model feasible under this node's distinct side
            // constraints — we cannot conclude UNSAT.  Report unknown (the node is
            // left unmarked and re-explored at a larger depth bound).
            if (subtree_has_cut && !all_string_only)
                return search_result::unknown;

            if (all_string_only) {
                // Subsumption rule: this node is a string-only conflict.  It is a
                // STOP point for collect_conflict_deps, so it must carry its own
                // justification: node_all_deps over-approximates the input
                // constraints behind its unsatisfiable string signature.
                node->set_conflict(backtrack_reason::sibling, node_all_deps(node));
                ++m_stats.m_num_sibling_closure;
                if (self_contained) {
                    // No cut escapes this subtree: the unsat is a property of the
                    // node's string signature alone.  Make it sticky (survives
                    // hot-restart) and memoize it in the transposition table.
                    node->set_general_conflict();
                    // The internal cuts (if any) deferred to this node or its
                    // descendants and are DISCHARGED by this closure — nothing
                    // escapes, so report a clean closure to the parent's fold.
                    // Leaking the internal cut upward lets an ancestor with a
                    // mixed closure (this child string-only + another child
                    // arithmetic) mark itself general_conflict (all children
                    // are) and THEN take the "cut may hide a model" unknown
                    // exit — the sticky mark reads as unsat on the next
                    // traversal: a spurious UNSAT.
                    node->m_subtree_has_cut = false;
                    node->m_subtree_lowlink = UINT_MAX;
                    // EXCEPTION: a lazy-factorization continuation (is_rf_cont)
                    // aliases its parent's — and ultimately the original, undivided
                    // membership's — string signature, yet its subtree only explored
                    // the REMAINING splits of the suspended iterator (the earlier
                    // splits' child-A branches live under ancestors, not here).  Its
                    // "string-only unsat" is thus a property of the remaining-splits
                    // subproblem, NOT of the full signature.  Memoizing it would let a
                    // structurally-identical ancestor (e.g. the root, on a later
                    // hot-restart solve) hit the cache and be pruned even though it
                    // still has the earlier splits to try — a spurious UNSAT.  So we
                    // keep the node itself dead but do NOT cache it, mirroring the
                    // cache-lookup and loop-cut exemptions above (both keyed on
                    // is_rf_cont).
                    // The same applies to an arithmetic-split child: its signature
                    // is its parent's, so caching its (branch-constrained) unsat
                    // would prune the parent's other branch on a later traversal.
                    if (!node->is_signature_alias()) {
                        node->m_unsat_cacheable = true;
                        m_unsat_node_cache.insert(node);
                    }
                    else
                        node->m_unsat_cacheable = false;
                }
                else
                    // Conditional on an ancestor above us; valid for this path only.
                    node->m_unsat_cacheable = false;
            }
            else {
                // a child relied on arithmetic / Parikh / external context.
                node->set_child_conflict();
                node->m_unsat_cacheable = false;
            }
            return search_result::unsat;
        }
        return search_result::unknown;
    }

    bool nielsen_graph::generate_extensions(nielsen_node *node) {
        SASSERT(node != nullptr);
        SASSERT(!node->is_currently_conflict());
        // The first modifier that produces edges is used and returned immediately.

        // TEMPORARY-COVERAGE-HOIST
        if (!harvest_mode() && apply_monadic_split(node))
            return ++m_stats.m_mod_monadic_split, true;

        // Priority 1: deterministic modifiers (single child, always progress)
        if (apply_det_modifier(node))
            return ++m_stats.m_mod_det, true;

        // Priority 2: PowerEpsilon - power → ε via base=ε or n=0
        if (apply_power_epsilon(node))
            return ++m_stats.m_mod_power_epsilon, true;

        // Priority 3: NumCmp - length comparison branching for power tokens
        if (apply_num_cmp(node))
            return ++m_stats.m_mod_num_cmp, true;

        // Priority 3b: SplitPowerElim - CommPower-based branching when
        // one side has a power and the other side has same-base occurrences
        // but ordering is unknown.
        if (apply_split_power_elim(node))
            return ++m_stats.m_mod_split_power_elim, true;

        // Priority 3c: FineWilf - overlap split for a head power vs a
        // different-base power behind a concrete-char prefix.  Preempts
        // ConstNumUnwinding's divergent one-copy peel loop on that shape.
        // (opt-in via smt.nseq.fine_wilf, default off)
        if (m_fine_wilf && apply_fine_wilf(node))
            return ++m_stats.m_mod_fine_wilf, true;

        // Priority 4: ConstNumUnwinding - power vs constant: n=0 or peel
        if (apply_const_num_unwinding(node))
            return ++m_stats.m_mod_const_num_unwinding, true;

        // Priority 5: EqSplit - split equations into two (single progress child)
        if (apply_eq_split(node))
            return ++m_stats.m_mod_eq_split, true;

        // Priority 5b: CycleSubsumption - eliminate leading variable subsumed by stabilizer
        // (regex-related: skipped in benchmark-harvest mode)
        if (!harvest_mode() && apply_cycle_subsumption(node))
            return ++m_stats.m_mod_cycle_subsumption, true;

        // Priority 5c: MonadicLanding - decompose the non-primitive memberships in
        // ONE step via seq_monadic's satisfying branch, emitted as land-state views.
        // Must precede the modifiers that grind the subject down by splitting
        // (landing 6, factorization 8, const nielsen 8b, regex var split 10).
        // (regex-related: skipped in benchmark-harvest mode)
        if (!harvest_mode() && apply_monadic_landing(node))
            return ++m_stats.m_mod_monadic_landing, true;

        // Priority 6: LandingDecomp - the core branching rule (paper §5.3):
        // split the leading variable by its landing state in the explored region
        // (land-at-s + escape-via-frontier).  Subsumes character unwinding.
        // (regex-related: skipped in benchmark-harvest mode)
        if (!harvest_mode() && apply_landing_decomposition(node))
            return ++m_stats.m_mod_landing, true;

        // Priority 6b: ViewLandingDecomp - land-only decomposition of a view
        // constraint made non-primitive by a substitution on a pinned variable
        // (paper §5.3, "Landing decomposition on view constraints").  Must
        // preempt RegexVarSplit: character-unwinding a pinned variable would
        // re-introduce the cycle-unrolling divergence the views prevent.
        // (regex-related: skipped in benchmark-harvest mode)
        if (!harvest_mode() && apply_view_landing_decomposition(node))
            return ++m_stats.m_mod_view_land, true;

        // Priority 7: GPowerIntr - ground power introduction
        if (apply_gpower_intr(node))
            return ++m_stats.m_mod_gpower_intr, true;

        // Priority 8: Regex Factorization
        // (regex-related: skipped in benchmark-harvest mode)
        if (!harvest_mode() && apply_regex_factorization(node))
            return ++m_stats.m_mod_regex_factorization, true;

        // Priority 8a: MonadicSplit - monadic decomposition (seq_monadic): close
        // the node if a membership, a same-subject group, or all of them jointly
        // have a provably empty language.  Sound one-way (conflict only);
        // opt-in via smt.nseq.monadic_split.  (skipped in benchmark-harvest mode)
        if (!harvest_mode() && apply_monadic_split(node))
            return ++m_stats.m_mod_monadic_split, true;

        // Priority 8b: ConstNielsen - char vs var (2 children)
        if (apply_const_nielsen(node))
            return ++m_stats.m_mod_const_nielsen, true;

        // Priority 9: RegexIfSplit - split str_mem s ∈ ite(c,th,el) by branching on c
        // (regex-related: skipped in benchmark-harvest mode)
        if (!harvest_mode() && apply_regex_if_split(node))
            return ++m_stats.m_mod_regex_if_split, true;

        // Priority 9b: SignatureSplit - heuristic string equation splitting
        if (m_signature_split && apply_signature_split(node))
            return ++m_stats.m_mod_signature_split, true;

        // Priority 10: RegexVarSplit - split str_mem by minterms
        // (regex-related: skipped in benchmark-harvest mode)
        if (!harvest_mode() && apply_regex_var_split(node))
            return ++m_stats.m_mod_regex_var_split, true;

        // Priority 11: PowerSplit - power unwinding with bounded prefix
        if (apply_power_split(node))
            return ++m_stats.m_mod_power_split, true;

        // Priority 12: VarNielsen - var vs var, all progress (classic Nielsen)
        if (apply_var_nielsen(node))
            return ++m_stats.m_mod_var_nielsen, true;

        // Priority 13: VarNumUnwinding - variable power unwinding for equality constraints
        if (apply_var_num_unwinding_eq(node))
            return ++m_stats.m_mod_var_num_unwinding_eq, true;

        // Priority 14: variable power unwinding for membership constraints
        // (regex/membership-related: skipped in benchmark-harvest mode)
        if (!harvest_mode() && apply_var_num_unwinding_mem(node))
            return ++m_stats.m_mod_var_num_unwinding_mem, true;

        // let's unwindind a disequality
        // (axiomatize_diseq requires the node to be satisfied-except-diseq; in
        // benchmark-harvest mode a node may still carry non-primitive memberships
        // because the regex modifiers are disabled, so skip it and let the caller
        // treat the empty result as a harvest leaf)
        if (!harvest_mode() && axiomatize_diseq(node))
            return ++m_stats.m_ax_diseq, true;

        return false;
    }

    dep_tracker nielsen_graph::collect_conflict_deps() const {
        dep_tracker deps = nullptr;
        // todo: Add visit set if the graph could contain cycles in the future
        // enumerating all nodes would not work due to hot-restarts having created
        // children that are currently not relevant
        vector<nielsen_node const*> to_visit;
        to_visit.push_back(m_root);
        while (!to_visit.empty()) {
            nielsen_node const* n = to_visit.back();
            to_visit.pop_back();
            // Recurse only through children_failed nodes.  A sibling (subsumption)
            // node — whether a loop-cut leaf, a transposition-cache hit, or an
            // internal string-only closure — is a STOP point: it carries its own
            // node_all_deps justification in m_conflict_internal (a sound
            // over-approximation of the input constraints that produced its
            // unsatisfiable string signature), so we do NOT descend into its
            // subtree (which may contain cut leaves whose targets lie outside it).
            if (n->reason() == backtrack_reason::children_failed) {
                for (unsigned i = n->outgoing().size(); i > 0; i--) {
                    nielsen_edge const* e = n->outgoing()[i - 1];
                    to_visit.push_back(e->tgt());
                }
                continue;
            }
            // not true anymore since we might have done a hot-restart where we previously created the child:
            //SASSERT(n->outgoing().empty());
            SASSERT(n->is_currently_conflict());
            if (n->m_conflict_external_literal != sat::null_literal)
                // We know from the outer solver that this literal is assigned true and contradicts node constraint
                deps = m_dep_mgr.mk_join(deps, m_dep_mgr.mk_leaf(n->m_conflict_external_literal));
            if (n->m_conflict_internal)
                deps = m_dep_mgr.mk_join(deps, n->m_conflict_internal);
        }
        return deps;
    }


    // NSB review: this is one of several methods exposed for testing
    void nielsen_graph::test_aux_explain_conflict(svector<enode_pair>& eqs,
        svector<sat::literal>& mem_literals) const {
        SASSERT(m_root);
        const auto deps = collect_conflict_deps();
        vector<dep_source, false> vs;
        m_dep_mgr.linearize(deps, vs);
        for (dep_source const& d : vs) {
            if (std::holds_alternative<enode_pair>(d))
                eqs.push_back(std::get<enode_pair>(d));
            else if (std::holds_alternative<sat::literal>(d))
                mem_literals.push_back(std::get<sat::literal>(d));
            else
                UNREACHABLE();
        }
    }
}
