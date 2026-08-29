/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen_modifiers.cpp

Abstract:

    Nielsen graph: the word-equation and power modifiers -- the
    deterministic closure, the classic Nielsen transformations, equation
    splitting and every rule that reasons about seq.power tokens.

    The regex-side modifiers live in seq_nielsen_regex.cpp.


Author:

    Clemens Eisenhofer 2026-03-02
    Nikolaj Bjorner (nbjorner) 2026-03-02

--*/

#include "smt/seq/seq_nielsen_internal.h"

namespace seq {

    // deep_contains_var now lives in seq_nielsen_internal.h: nielsen_subst's
    // is_eliminating() and add_subst_length_constraints need it too.  All power
    // bases are ground w.r.t. the substituted variable by construction today
    // (gpower prefixes stop at the first variable); the assertions at the
    // power-substitution sites pin that invariant down.

    bool nielsen_graph::apply_det_modifier(nielsen_node* node) {
        // resist the temptation to add rules that "simplify" primitive membership constraints!
        // pretty much all of them could cause divergence!
        // e.g., x \in aa* => don't apply substitution x / ax even though it looks "safe" to do
        // there might be another constraint x \in a* and they would just push the "a" back and forth!

        for (unsigned eq_idx = 0; eq_idx < node->str_eqs().size(); ++eq_idx) {
            str_eq const& eq = node->str_eqs()[eq_idx];
            if (eq.is_trivial())
                continue; // We should have simplified it away before
            auto l = eq.m_lhs, r = eq.m_rhs;
            if (!l || !r)
                continue;

            // 0. empty side propagation
            if (l->is_empty() || r->is_empty()) {
                euf::snode const* non_empty_side = l->is_empty() ? r : l;
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, "det", true);
                euf::snode_vector tokens;
                non_empty_side->collect_tokens(tokens);

                auto& eqs = child->str_eqs();
                eqs[eq_idx] = eqs.back();
                eqs.pop_back();

                for (euf::snode const* t : tokens) {
                    if (t->is_var()) {
                        nielsen_subst s(t, m_sg.mk_empty_seq(t->get_sort()), eq.m_dep);
                        e->add_subst(s);
                        child->apply_subst(m_sg, s);
                    } else if (t->is_power()) {
                        expr* expr_node = t->get_expr();
                        expr* pow_base = nullptr, *pow_exp = nullptr;
                        if (seq().str.is_power(expr_node, pow_base, pow_exp) && pow_exp)
                            e->add_side_constraint(mk_constraint(a.mk_eq(pow_exp, a.mk_int(0)), eq.m_dep));
                        nielsen_subst s(t, m_sg.mk_empty_seq(t->get_sort()), eq.m_dep);
                        e->add_subst(s);
                        child->apply_subst(m_sg, s);
                    }
                }
                return true;
            }

            // 1. unit equalities produced by unit-unit prefix/suffix splits
            {
                euf::snode_vector lhs_toks, rhs_toks;
                l->collect_tokens(lhs_toks);
                r->collect_tokens(rhs_toks);

                // --- prefix ---
                unsigned prefix = 0;
                while (prefix < lhs_toks.size() && prefix < rhs_toks.size()) {
                    euf::snode const* lt = lhs_toks[prefix];
                    euf::snode const* rt = rhs_toks[prefix];
                    if (m.are_equal(lt->get_expr(), rt->get_expr()))
                        ++prefix;
                    else if (m_sg.are_unit_distinct(lt, rt))
                        break;
                    else if (lt->is_char_or_unit() && rt->is_char_or_unit()) {
                        nielsen_node* child = mk_child(node);
                        nielsen_edge* e = mk_edge(node, child, "det", true);

                        // orient so the substituted token is the symbolic unit
                        // (two concrete chars would be are_equal or unit-distinct above)
                        if (lt->is_char())
                            std::swap(lt, rt);
                        SASSERT(lt->is_unit());

                        euf::snode const* lhs_rest = m_sg.drop_left(l, prefix + 1);
                        euf::snode const* rhs_rest = m_sg.drop_left(r, prefix + 1);

                        auto& eqs = child->str_eqs();
                        eqs[eq_idx] = eqs.back();
                        eqs.pop_back();
                        // push the residual BEFORE applying the substitution so the
                        // substituted unit is rewritten inside it as well
                        if (!lhs_rest->is_empty() || !rhs_rest->is_empty())
                            eqs.push_back(str_eq(m, lhs_rest, rhs_rest, eq.m_dep));

                        nielsen_subst subst(lt, rt, eq.m_dep);
                        e->add_subst(subst);
                        child->apply_subst(m_sg, subst);
                        return true;
                    }
                    else
                        break;
                }

                // --- suffix ---
                unsigned lsz = lhs_toks.size(), rsz = rhs_toks.size();
                unsigned suffix = 0;
                while (suffix < lsz - prefix && suffix < rsz - prefix) {
                    euf::snode const* lt = lhs_toks[lsz - 1 - suffix];
                    euf::snode const* rt = rhs_toks[rsz - 1 - suffix];
                    if (m.are_equal(lt->get_expr(), rt->get_expr()))
                        ++suffix;
                    else if (m_sg.are_unit_distinct(lt, rt))
                        break;
                    else if (lt->is_char_or_unit() && rt->is_char_or_unit()) {
                        nielsen_node* child = mk_child(node);
                        nielsen_edge* e = mk_edge(node, child, "det", true);

                        euf::snode const* lhs_rest = m_sg.drop_right(l, suffix + 1);
                        euf::snode const* rhs_rest = m_sg.drop_right(r, suffix + 1);

                        auto& eqs = child->str_eqs();
                        eqs[eq_idx] = eqs.back();
                        eqs.pop_back();
                        // push the residual BEFORE applying the substitution so the
                        // substituted unit is rewritten inside it as well
                        if (!lhs_rest->is_empty() || !rhs_rest->is_empty())
                            eqs.push_back(str_eq(m, lhs_rest, rhs_rest, eq.m_dep));

                        // orient so the substituted token is the symbolic unit
                        if (lt->is_char())
                            std::swap(lt, rt);
                        nielsen_subst subst(lt, rt, eq.m_dep);
                        e->add_subst(subst);
                        child->apply_subst(m_sg, subst);
                        return true;
                    }
                    else
                        break;
                }
            }

            // 2. power-character directional inconsistency
            for (unsigned od = 0; od < 2; ++od) {
                bool fwd = (od == 0);
                euf::snode const* lh = dir_token(l, fwd);
                euf::snode const* rh = dir_token(r, fwd);
                for (int side = 0; side < 2; ++side) {
                    euf::snode const* pow_head = (side == 0) ? lh : rh;
                    euf::snode const* other_head = (side == 0) ? rh : lh;
                    if (!pow_head || !pow_head->is_power() || !other_head || !other_head->is_char())
                        continue;
                    euf::snode const* base_sn = pow_head->arg0();
                    if (!base_sn) continue;
                    euf::snode const* base_head = dir_token(base_sn, fwd);
                    if (!base_head || !base_head->is_char()) continue;
                    if (m.are_equal(base_head->get_expr(), other_head->get_expr())) continue;
                    // Directional base/head mismatch -> force exponent 0 and power -> ε.
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, "det", true);
                    nielsen_subst s(pow_head, m_sg.mk_empty_seq(pow_head->get_sort()), eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                    expr* pow_exp = get_power_exp_expr(pow_head, m_seq);
                    if (pow_exp) {
                        expr* zero = a.mk_int(0);
                        e->add_side_constraint(mk_constraint(a.mk_eq(pow_exp, zero), eq.m_dep));
                    }
                    return true;
                }
            }

            // 3. variable-character look-ahead substitution
            for (unsigned od = 0; od < 2; ++od) {
                bool fwd = od == 0;

                euf::snode const* var_side = nullptr;
                euf::snode const* char_side = nullptr;
                euf::snode const* lhead = dir_token(l, fwd);
                euf::snode const* rhead = dir_token(r, fwd);
                if (!lhead || !rhead) continue;

                if (lhead->is_var() && rhead->is_char()) {
                    var_side = l;
                    char_side = r;
                }
                else if (rhead->is_var() && lhead->is_char()) {
                    var_side = r;
                    char_side = l;
                }
                else
                    continue;

                euf::snode_vector var_toks, char_toks;
                collect_tokens_dir(var_side, fwd, var_toks);
                collect_tokens_dir(char_side, fwd, char_toks);
                if (var_toks.size() <= 1 || char_toks.empty())
                    continue;

                euf::snode const* var_node = var_toks[0];
                SASSERT(var_node->is_var());

                unsigned i = 0;
                for (; i < char_toks.size() && char_toks[i]->is_char(); ++i) {
                    unsigned j1 = 1;
                    unsigned j2 = i;
                    bool failed = false;

                    while (j1 < var_toks.size() && j2 < char_toks.size()) {
                        euf::snode const* st1 = var_toks[j1];
                        euf::snode const* st2 = char_toks[j2];

                        if (!st2->is_char()) break;
                        if (st1->is_char()) {
                            if (st1->id() == st2->id()) {
                                j1++; j2++;
                                continue;
                            }
                            failed = true; break;
                        }
                        if (st1->id() != var_node->id()) break;

                        bool inner_indet = false;
                        for (unsigned l_idx = 0; j2 < char_toks.size() && l_idx < i; ++l_idx) {
                            st2 = char_toks[j2];
                            if (!st2->is_char()) {
                                inner_indet = true; break;
                            }
                            if (st2->id() == char_toks[l_idx]->id()) {
                                j2++; continue;
                            }
                            failed = true; break;
                        }
                        if (inner_indet || failed) break;
                        j1++;
                    }

                    if (failed) continue;
                    break;
                }

                if (i == 0) continue;

                bool skip_dir = false;
                euf::snode const* next_var = nullptr;
                for (unsigned k = i; k < char_toks.size(); ++k) {
                    euf::snode const* t = char_toks[k];
                    if (t->is_power()) {
                        skip_dir = true;
                        break;
                    }
                    if (t->is_var()) {
                        next_var = t;
                        break;
                    }
                }
                if (skip_dir) continue;

                if (next_var) {
                    u_map<unsigned> dep_edges;
                    for (str_eq const& other_eq : node->str_eqs()) {
                        if (other_eq.is_trivial() || !other_eq.m_lhs || !other_eq.m_rhs)
                            continue;
                        euf::snode const* lh2 = dir_token(other_eq.m_lhs, fwd);
                        euf::snode const* rh2 = dir_token(other_eq.m_rhs, fwd);
                        if (!lh2 || !rh2) continue;

                        auto record_dep = [&](euf::snode const* head_var, euf::snode const* other_side) {
                            euf::snode_vector other_toks;
                            collect_tokens_dir(other_side, fwd, other_toks);
                            for (unsigned idx = 0; idx < other_toks.size(); ++idx) {
                                if (other_toks[idx]->is_var()) {
                                    if (!dep_edges.contains(head_var->id()))
                                        dep_edges.insert(head_var->id(), other_toks[idx]->id());
                                    return;
                                }
                            }
                        };

                        if (lh2->is_var() && rh2->is_var()) {
                            if (!dep_edges.contains(lh2->id()))
                                dep_edges.insert(lh2->id(), rh2->id());
                            if (!dep_edges.contains(rh2->id()))
                                dep_edges.insert(rh2->id(), lh2->id());
                        }
                        else if (lh2->is_var() && !rh2->is_var()) record_dep(lh2, other_eq.m_rhs);
                        else if (rh2->is_var() && !lh2->is_var()) record_dep(rh2, other_eq.m_lhs);
                    }

                    uint_set visited;
                    svector<unsigned> worklist;
                    worklist.push_back(next_var->id());
                    bool cycle_found = false;
                    while (!worklist.empty() && !cycle_found) {
                        unsigned cur = worklist.back();
                        worklist.pop_back();
                        if (cur == var_node->id()) {
                            cycle_found = true; break;
                        }
                        if (visited.contains(cur)) continue;
                        visited.insert(cur);
                        unsigned dep_id;
                        if (dep_edges.find(cur, dep_id))
                            worklist.push_back(dep_id);
                    }
                    if (cycle_found) continue;
                }

                euf::snode const* prefix_sn = char_toks[0];
                for (unsigned j = 1; j < i; ++j) {
                    prefix_sn = dir_concat(m_sg, prefix_sn, char_toks[j], fwd);
                }
                euf::snode const* tail = get_tail(var_node, compute_length_expr(prefix_sn).get(), fwd);
                euf::snode const* replacement = dir_concat(m_sg, prefix_sn, tail, fwd);
                nielsen_subst s(var_node, replacement, eq.m_dep);
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, "det", true);
                e->add_side_constraint(mk_constraint(a.mk_ge(compute_length_expr(tail), a.mk_int(0)), eq.m_dep));
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                return true;
            }

            // variable definition: x = t where x is a single var and x ∉ vars(t)
            // → deterministically substitute x → t throughout the node
            euf::snode const* var = nullptr;
            euf::snode const* def;

            if (l->is_var() && !snode_contains_var(r, l)) {
                var = l;
                def = r;
            }
            else if (r->is_var() && !snode_contains_var(l, r)) {
                var = r;
                def = l;
            }
            else if (l->is_unit() && r->is_char_or_unit()) {
                var = l;
                def = r;
            }
            else if (r->is_unit() && l->is_char_or_unit()) {
                var = r;
                def = l;
            }

            if (var) {
                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, "det", true);
                nielsen_subst s(var, def, eq.m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);
                return true;
            }
        }
        return false;
    }

    void nielsen_graph::leading_char_block(euf::snode const* side, const bool fwd,
                                           const unsigned cap, euf::snode_vector& out) {
        euf::snode_vector toks;
        collect_tokens_dir(side, fwd, toks);
        out.reset();
        for (unsigned i = 0; i < toks.size() && out.size() < cap; i++) {
            // Single-character tokens only.  Symbolic units qualify: the case
            // split below needs each token's LENGTH (1), not its value.
            if (!toks[i]->is_char_or_unit())
                break;
            out.push_back(toks[i]);
        }
    }

    euf::snode const* nielsen_graph::mk_block_word(euf::snode_vector const& block, const unsigned k,
                                                   const bool fwd, sort* s) {
        if (k == 0)
            return m_sg.mk_empty_seq(s);
        euf::snode const* w = nullptr;
        for (unsigned i = 0; i < k; i++) {
            w = dir_concat(m_sg, w, block[i], fwd);   // grows in DIRECTION order
        }
        return w;
    }

    bool nielsen_graph::apply_const_nielsen(nielsen_node* node) {
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            SASSERT(eq.well_formed());
            for (unsigned od = 0; od < 2; ++od) {
                const bool fwd = (od == 0);
                euf::snode const* lhead = dir_token(eq.m_lhs, fwd);
                euf::snode const* rhead = dir_token(eq.m_rhs, fwd);
                if (!lhead || !rhead)
                    continue;

                // char vs var: branch 1: var -> ε, branch 2: var -> char·var   (depending on direction)
                euf::snode const* char_head = lhead->is_char_or_unit() ? lhead : (rhead->is_char_or_unit() ? rhead : nullptr);
                euf::snode const* var_head = lhead->is_var() ? lhead : (rhead->is_var() ? rhead : nullptr);
                if (!char_head || !var_head)
                    continue;

                const euf::snode* const_side = (lhead == char_head) ? eq.m_lhs : eq.m_rhs;
                const euf::snode* var_side   = (lhead == char_head) ? eq.m_rhs : eq.m_lhs;
                euf::snode_vector block;
                if (m_block_compression > 1)
                    leading_char_block(const_side, fwd, m_block_compression, block);
                else
                    block.push_back(char_head);
                const unsigned m_len = block.size();
                SASSERT(m_len >= 1);
                if (m_len > 1) {
                    ++m_stats.m_mod_block_compression;
                    m_stats.m_block_chars_consumed += m_len;
                }

                // Token following x on the variable side (null if x is the whole side)
                euf::snode_vector var_toks;
                collect_tokens_dir(var_side, fwd, var_toks);
                SASSERT(var_toks.empty() || var_toks[0] == var_head);
                euf::snode const* const next_tok = var_toks.size() > 1 ? var_toks[1] : nullptr;

                sort* const seq_sort = var_head->get_sort();

                
                // x = ε  (the classic "var → ε" branch; a ground, eliminating
                // substitution, so it keeps its progress flag)
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, "nielsen const 0", true);
                    const nielsen_subst s(var_head, m_sg.mk_empty_seq(seq_sort), eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }

                // x = w · x'  —  the whole block is consumed in one step and
                // cancels against the other side during simplification.  For
                // m_len = 1 this is exactly the classic one-character peel.
                {
                    euf::snode const* tail = get_tail(var_head, a.mk_int(m_len), fwd);
                    euf::snode const* replacement =
                        dir_concat(m_sg, mk_block_word(block, m_len, fwd, seq_sort), tail, fwd);
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, "nielsen const &gt;", false);
                    e->add_side_constraint(mk_constraint(a.mk_ge(compute_length_expr(tail), a.mk_int(0)), eq.m_dep));
                    const nielsen_subst s(var_head, replacement, eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }

                // x = w[0..k) for 0 < k < m_len: x ends strictly inside the block.
                for (unsigned k = 1; k < m_len; ++k) {
                    // Clash lookahead [maybe drop it at the other position]
                    if (!next_tok ||
                        (next_tok->is_char() && block[k]->is_char() && next_tok->id() != block[k]->id())) {
                        ++m_stats.m_block_children_pruned;
                        continue;
                    }
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, "nielsen block =", false);
                    const nielsen_subst s(var_head, mk_block_word(block, k, fwd, seq_sort), eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                return true;
            }
        }
        return false;
    }

    bool nielsen_graph::apply_var_nielsen(nielsen_node* node) {
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            SASSERT(eq.well_formed());
            for (unsigned od = 0; od < 2; ++od) {
                const bool fwd = od == 0;
                euf::snode const* lhead = dir_token(eq.m_lhs, fwd);
                euf::snode const* rhead = dir_token(eq.m_rhs, fwd);
                SASSERT(lhead && rhead);
                SASSERT(lhead->id() != rhead->id());
                if (!lhead->is_var() || !rhead->is_var())
                    continue;

                // x·A = y·B where x,y are distinct variables (classic Nielsen)
                // child 1: x → ε (progress)
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, "nielsen var =l", true);
                    const nielsen_subst s(lhead, m_sg.mk_empty_seq(lhead->get_sort()), eq.m_dep);
                    e->add_subst(s);
                    child->apply_subst(m_sg, s);
                }
                // child 2: y → ε && |x| > 0 (progress)
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, "nielsen var =r", true);
                    const nielsen_subst s(rhead, m_sg.mk_empty_seq(rhead->get_sort()), eq.m_dep);
                    e->add_subst(s);
                    // |x| > 0: the |x| = 0 case is child 1 (keeps the branches disjoint)
                    e->add_side_constraint(mk_constraint(a.mk_gt(compute_length_expr(lhead), a.mk_int(0)), eq.m_dep));
                    child->apply_subst(m_sg, s);
                }
                // child 3: x → y && |x| > 0 (progress)
                {
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, "nielsen var =", true);
                    const nielsen_subst s(lhead, rhead, eq.m_dep);
                    e->add_subst(s);
                    // |x| > 0: the |x| = 0 case is child 1 (keeps the branches disjoint)
                    e->add_side_constraint(mk_constraint(a.mk_gt(compute_length_expr(lhead), a.mk_int(0)), eq.m_dep));
                    child->apply_subst(m_sg, s);
                }
                // child 4: x → y·x && |x| > 0 && |y| > 0 (no progress)
                {
                    auto* tail = get_tail(lhead, compute_length_expr(rhead).get(), fwd);
                    euf::snode const* replacement = dir_concat(m_sg, rhead, tail, fwd);
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, "nielsen var &gt;", false);
                    const nielsen_subst s(lhead, replacement, eq.m_dep);
                    e->add_subst(s);
                    e->add_side_constraint(mk_constraint(a.mk_gt(compute_length_expr(rhead), a.mk_int(0)), eq.m_dep));
                    e->add_side_constraint(mk_constraint(a.mk_gt(compute_length_expr(tail), a.mk_int(0)), eq.m_dep));
                    child->apply_subst(m_sg, s);
                }
                // child 5: y → x·y && |x| > 0 && |y| > 0 (no progress)
                {
                    auto* tail = get_tail(rhead, compute_length_expr(lhead).get(), fwd);
                    euf::snode const* replacement = dir_concat(m_sg, lhead, tail, fwd);
                    nielsen_node* child = mk_child(node);
                    nielsen_edge* e = mk_edge(node, child, "nielsen var &lt;", false);
                    const nielsen_subst s(rhead, replacement, eq.m_dep);
                    e->add_subst(s);
                    e->add_side_constraint(mk_constraint(a.mk_gt(compute_length_expr(lhead), a.mk_int(0)), eq.m_dep));
                    e->add_side_constraint(mk_constraint(a.mk_gt(compute_length_expr(tail), a.mk_int(0)), eq.m_dep));
                    child->apply_subst(m_sg, s);
                }
                return true;
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // EqSplit helpers: token length classification
    // -----------------------------------------------------------------------

    bool nielsen_graph::token_has_variable_length(euf::snode const* tok) const {
        // Chars and units have known constant length 1.
        if (tok->is_char_or_unit())
            return false;
        // Variables and powers have symbolic/unknown length.
        if (tok->is_var() || tok->is_power())
            return true;
        // For s_var string literals: check if it's a string literal (known constant length).
        if (tok->get_expr()) {
            zstring s;
            if (m_seq.str.is_string(tok->get_expr(), s))
                return false;
        }
        // Everything else is treated as variable length.
        return true;
    }

    unsigned nielsen_graph::token_const_length(euf::snode const* tok) const {
        if (tok->is_char_or_unit())
            return 1;
        if (tok->get_expr()) {
            zstring s;
            if (m_seq.str.is_string(tok->get_expr(), s))
                return s.length();
        }
        return 0;
    }

    // -----------------------------------------------------------------------
    // EqSplit: find_eq_split_point
    //
    // Walks tokens from each side tracking two accumulators:
    //   - balance : per variable-length token, occurrences consumed on the LHS
    //     minus occurrences consumed on the RHS, with nz counting the entries
    //     that are currently nonzero
    //   - const_diff : net constant-length difference (LHS constants − RHS constants)
    //
    // A potential split point arises when nz == 0, i.e. the two prefixes have
    // *equal variable content*: their symbolic lengths then cancel and the
    // prefix lengths are determined up to the constant offset const_diff, which
    // becomes the padding.
    //
    // Among all such split points, we pick the one minimising |const_diff|
    // (the padding amount). We also require having seen at least one variable-
    // length token before accepting a split, so that the split is non-trivial.
    //
    // NB: the accumulators used to be two booleans, "has a variable-length token
    // been consumed on this side", which were set but never cleared -- and since
    // a split needed both to be false *after* a variable had been seen, the
    // condition was unsatisfiable and the whole modifier was unreachable (it
    // fired zero times across 709 corpus files that entered the search).  A
    // per-token signed balance is what the surrounding code always assumed: the
    // split is sound exactly when the variable multisets of the two prefixes
    // agree, which is what makes |LHS prefix| - |RHS prefix| = const_diff hold.
    // -----------------------------------------------------------------------

    bool nielsen_graph::find_eq_split_point(
            euf::snode_vector const& lhs_toks,
            euf::snode_vector const& rhs_toks,
            unsigned& out_lhs_idx,
            unsigned& out_rhs_idx,
            int& out_padding) const {
        const unsigned lhs_len = lhs_toks.size();
        const unsigned rhs_len = rhs_toks.size();
        if (lhs_len <= 1 || rhs_len <= 1)
            return false;

        u_map<int> balance;
        unsigned nz = 0;
        int const_diff = 0;
        unsigned li = 0, ri = 0;
        unsigned lvars = 0, rvars = 0;   // variable-length tokens consumed
        bool seen_variable = false;

        bool has_best = false;
        unsigned best_lhs = 0, best_rhs = 0;
        int best_padding = 0;

        auto bump = [&](euf::snode const* tok, const int d) {
            int b = 0;
            balance.find(tok->id(), b);
            if (b == 0)
                ++nz;
            b += d;
            if (b == 0)
                --nz;
            balance.insert(tok->id(), b);
        };

        while (true) {
            // The split must be strictly interior on *both* sides.  A boundary
            // at an endpoint leaves one side's prefix equal to the whole side
            // and its suffix empty, so eq1 is just the original equation with a
            // renamed tail: no progress, the child re-derives the parent, and
            // since eq_split emits a single progress child the node would be
            // closed as unsat by the memo.  Requiring 0 < li < lhs_len and
            // 0 < ri < rhs_len also makes both new equations strictly shorter
            // than the original, which bounds the recursion.
            const bool interior = li > 0 && li < lhs_len && ri > 0 && ri < rhs_len;
            if (seen_variable && nz == 0 && interior &&
                (!has_best || std::abs(const_diff) < std::abs(best_padding))) {
                has_best = true;
                best_padding = const_diff;
                best_lhs = li;
                best_rhs = ri;
            }

            const bool l_done = li >= lhs_len;
            const bool r_done = ri >= rhs_len;
            if (l_done && r_done)
                break;

            // Advance the side that is behind on variable-length tokens: that is
            // what lets two differently-ordered variable sequences reach a
            // cancellation point.  With the counts level, prefer the side
            // carrying fewer constants, which keeps |padding| small.
            bool consume_lhs;
            if (l_done)
                consume_lhs = false;
            else if (r_done)
                consume_lhs = true;
            else if (lvars != rvars)
                consume_lhs = lvars < rvars;
            else
                consume_lhs = const_diff <= 0;

            euf::snode const* tok = consume_lhs ? lhs_toks[li++] : rhs_toks[ri++];
            if (token_has_variable_length(tok)) {
                bump(tok, consume_lhs ? 1 : -1);
                ++(consume_lhs ? lvars : rvars);
                seen_variable = true;
            }
            else
                const_diff += (consume_lhs ? 1 : -1) * (int)token_const_length(tok);
        }

        if (!has_best)
            return false;

        out_lhs_idx = best_lhs;
        out_rhs_idx = best_rhs;
        out_padding = best_padding;
        return true;
    }

    // -----------------------------------------------------------------------
    // apply_eq_split
    //
    // For a regex-free equation LHS = RHS, finds a split point and decomposes
    // into two shorter equations with optional padding variable:
    //
    //   eq1: LHS[0..lhsIdx] · [pad if padding<0] = [pad if padding>0] · RHS[0..rhsIdx]
    //   eq2: LHS[lhsIdx..] · [pad if padding>0] = [pad if padding<0] · RHS[rhsIdx..]
    //
    // Creates a single progress child.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_eq_split(nielsen_node* node) {

        for (unsigned eq_idx = 0; eq_idx < node->str_eqs().size(); ++eq_idx) {
            str_eq const& eq = node->str_eqs()[eq_idx];
            SASSERT(eq.well_formed());
            SASSERT(!eq.is_trivial());

            euf::snode_vector lhs_toks, rhs_toks;
            eq.m_lhs->collect_tokens(lhs_toks);
            eq.m_rhs->collect_tokens(rhs_toks);
            SASSERT(!lhs_toks.empty());
            SASSERT(!rhs_toks.empty());

            unsigned split_lhs = 0, split_rhs = 0;
            int padding = 0;
            if (!find_eq_split_point(lhs_toks, rhs_toks, split_lhs, split_rhs, padding))
                continue;

            // Split the equation sides into prefix / suffix.
            euf::snode const* lhs_prefix = m_sg.drop_right(eq.m_lhs, lhs_toks.size() - split_lhs);
            euf::snode const* lhs_suffix = m_sg.drop_left(eq.m_lhs, split_lhs);
            euf::snode const* rhs_prefix = m_sg.drop_right(eq.m_rhs, rhs_toks.size() - split_rhs);
            euf::snode const* rhs_suffix = m_sg.drop_left(eq.m_rhs, split_rhs);

            // Build the two new equations, incorporating a padding variable if needed.
            euf::snode const* eq1_lhs = lhs_prefix;
            euf::snode const* eq1_rhs = rhs_prefix;
            euf::snode const* eq2_lhs = lhs_suffix;
            euf::snode const* eq2_rhs = rhs_suffix;

            euf::snode const* pad = nullptr;
            if (padding != 0) {
                // NSB review: can we represent pad_var using a string function?
                // seq_skolem::mk returns an expr_ref, so the result must be kept
                // in one: binding it to a raw expr* drops the only reference and
                // frees the fresh skolem before m_sg.mk ever sees it.
                const expr_ref pad_var(
                    m_sk.mk("eq-split", a.mk_int(padding), eq.m_lhs->get_expr(),
                            eq.m_rhs->get_expr(), eq.m_lhs->get_sort()), m);
                pad = m_sg.mk(pad_var);
                if (padding > 0) {
                    // LHS prefix is longer by |padding|, so RHS prefix is a
                    // prefix of it: lhs_prefix = rhs_prefix·pad, and the extra
                    // pad is what rhs_suffix starts with: rhs_suffix = pad·lhs_suffix.
                    eq1_rhs = m_sg.mk_concat(rhs_prefix, pad);
                    eq2_lhs = m_sg.mk_concat(pad, lhs_suffix);
                }
                else {
                    // Mirror image: RHS prefix is longer by |padding|.
                    eq1_lhs = m_sg.mk_concat(lhs_prefix, pad);
                    eq2_rhs = m_sg.mk_concat(pad, rhs_suffix);
                }
            }

            // Create single progress child.
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, "eq split", true);

            // Remove the original equation and add the two new ones.
            auto& eqs = child->str_eqs();
            eqs[eq_idx] = eqs.back();
            eqs.pop_back();
            eqs.push_back(str_eq(m, eq1_lhs, eq1_rhs, eq.m_dep));
            eqs.push_back(str_eq(m, eq2_lhs, eq2_rhs, eq.m_dep));

            // Int constraints on the edge.
            // 1) len(pad) = |padding|  (if padding variable was created)
            if (pad && pad->get_expr()) {
                const expr_ref len_pad(m_seq.str.mk_length(pad->get_expr()), m);
                const expr_ref abs_pad(a.mk_int(std::abs(padding)), m);
                e->add_side_constraint(mk_constraint(m.mk_eq(len_pad, abs_pad), eq.m_dep));
            }
            // 2) len(eq1_lhs) = len(eq1_rhs)
            const expr_ref l1 = compute_length_expr(eq1_lhs);
            const expr_ref r1 = compute_length_expr(eq1_rhs);
            e->add_side_constraint(mk_constraint(m.mk_eq(l1, r1), eq.m_dep));

            // 3) len(eq2_lhs) = len(eq2_rhs)
            const expr_ref l2 = compute_length_expr(eq2_lhs);
            const expr_ref r2 = compute_length_expr(eq2_rhs);
            e->add_side_constraint(mk_constraint(m.mk_eq(l2, r2), eq.m_dep));

            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Helper: find a power token in any str_eq
    // -----------------------------------------------------------------------

    euf::snode const* nielsen_graph::find_power_token(nielsen_node* node) {
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            SASSERT(eq.well_formed());
            euf::snode_vector toks;
            eq.m_lhs->collect_tokens(toks);
            for (euf::snode const* t : toks) {
                if (t->is_power())
                    return t;
            }
            toks.reset();
            eq.m_rhs->collect_tokens(toks);
            for (euf::snode const* t : toks) {
                if (t->is_power())
                    return t;
            }
        }
        return nullptr;
    }

    // -----------------------------------------------------------------------
    // Helper: find a power token facing a constant (char) head
    // Returns true if found, sets power, other_head, eq_out.
    // -----------------------------------------------------------------------

    bool nielsen_graph::find_power_vs_non_var(nielsen_node* node,
                                            euf::snode const*& power,
                                            euf::snode const*& other_head,
                                            str_eq const*& eq_out,
                                            bool& fwd) {
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            for (unsigned od = 0; od < 2; ++od) {
                const bool local_fwd = (od == 0);
                euf::snode const* lhead = dir_token(eq.m_lhs, local_fwd);
                euf::snode const* rhead = dir_token(eq.m_rhs, local_fwd);
                // Match power vs any non-variable, non-empty token (char, unit,
                // power with different base, etc.).
                // Same-base power vs power is handled by NumCmp (priority 3).
                // Power vs variable is handled by PowerSplit (priority 11).
                // Power vs empty is handled by PowerEpsilon (priority 2).
                if (lhead && lhead->is_power() && rhead && !rhead->is_var() && !rhead->is_empty()) {
                    power = lhead;
                    other_head = rhead;
                    eq_out = &eq;
                    fwd = local_fwd;
                    return true;
                }
                if (rhead && rhead->is_power() && lhead && !lhead->is_var() && !lhead->is_empty()) {
                    power = rhead;
                    other_head = lhead;
                    eq_out = &eq;
                    fwd = local_fwd;
                    return true;
                }
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Helper: find a power token facing a variable head
    // -----------------------------------------------------------------------

    bool nielsen_graph::find_power_vs_var(nielsen_node* node,
                                          euf::snode const*& power,
                                          euf::snode const*& var_head,
                                          str_eq const*& eq_out,
                                          bool& fwd) {
        for (str_eq const& eq : node->str_eqs()) {
            SASSERT(eq.well_formed() && !eq.is_trivial());

            for (unsigned od = 0; od < 2; ++od) {
                const bool local_fwd = (od == 0);
                euf::snode const* lhead = dir_token(eq.m_lhs, local_fwd);
                euf::snode const* rhead = dir_token(eq.m_rhs, local_fwd);
                if (lhead && lhead->is_power() && rhead && rhead->is_var()) {
                    power = lhead;
                    var_head = rhead;
                    eq_out = &eq;
                    fwd = local_fwd;
                    return true;
                }
                if (rhead && rhead->is_power() && lhead && lhead->is_var()) {
                    power = rhead;
                    var_head = lhead;
                    eq_out = &eq;
                    fwd = local_fwd;
                    return true;
                }
            }
        }
        return false;
    }

    bool nielsen_graph::find_power_vs_var(nielsen_node* node,
                                          euf::snode const*& power,
                                          str_mem const*& mem_out,
                                          bool& fwd) {
        for (str_mem const& mem : node->str_mems()) {
            SASSERT(mem.well_formed() && !mem.is_trivial(node));

            for (unsigned od = 0; od < 2; ++od) {
                const bool local_fwd = (od == 0);
                euf::snode const* lhead = dir_token(mem.m_str, local_fwd);
                if (lhead && lhead->is_power()) {
                    power = lhead;
                    mem_out = &mem;
                    fwd = local_fwd;
                    return true;
                }
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_power_epsilon
    // Fires only when one side of an equation is empty and the other side
    // starts with a power token u^n.  In that case, branch:
    //   (1) base u → ε (base is empty, so u^n = ε)
    //   (2) u^n → ε (the power is zero, replace power with empty)
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_power_epsilon(nielsen_node* node) {
        // Match only when one equation side is empty and the other starts
        // with a power.
        euf::snode const* power = nullptr;
        dep_tracker dep = m_dep_mgr.mk_empty();
        for (str_eq const& eq : node->str_eqs()) {
            if (eq.is_trivial())
                continue;
            SASSERT(eq.well_formed());
            if (eq.m_lhs->is_empty() && eq.m_rhs->first() && eq.m_rhs->first()->is_power()) {
                power = eq.m_rhs->first();
                dep = eq.m_dep;
                break;
            }
            if (eq.m_rhs->is_empty() && eq.m_lhs->first() && eq.m_lhs->first()->is_power()) {
                power = eq.m_lhs->first();
                dep = eq.m_dep;
                break;
            }
        }
        if (!power)
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode const* base = power->arg0();

        nielsen_node* child;
        nielsen_edge* e;

        // Branch 1: base → ε (if base is a variable, substitute it to empty)
        // This makes u^n = ε^n = ε for any n.
        if (base->is_var()) {
            child = mk_child(node);
            e = mk_edge(node, child, "power power 0", true);
            const nielsen_subst s1(base, m_sg.mk_empty_seq(base->get_sort()), dep);
            e->add_subst(s1);
            child->apply_subst(m_sg, s1);
            // sgraph::subst does not descend into power nodes, so u → ε alone
            // leaves the triggering power u^n — and hence the equation — intact:
            // the child would be an exact string-sibling of this node and get
            // loop-cut without progress.  Also substitute the power itself
            // (sound: ε^n = ε for every n).
            const nielsen_subst s1b(power, m_sg.mk_empty_seq(power->get_sort()), dep);
            e->add_subst(s1b);
            child->apply_subst(m_sg, s1b);
        }

        // Branch 2: replace the power token itself with ε.
        // u^n = ε  ⟺  n = 0 ∨ u = ε, so record that disjunction as a side
        // constraint.  Without it the exponent stays unconstrained while path
        // constraints mentioning it survive (e.g. |x| = n·|base| + |s| from a
        // gpower introduction, or n ≥ 1 from a peel), so the outer arithmetic
        // could pick n ≥ 1 with a non-empty ground base — a length assignment
        // the string model (power = ε) cannot realize.  A bare n = 0 would be
        // too strong: for a compound base containing variables the u = ε,
        // n ≥ 1 models are covered only by this branch (branch 1 fires solely
        // for single-variable bases).
        child = mk_child(node);
        e = mk_edge(node, child, "power base 0", true);
        const nielsen_subst s2(power, m_sg.mk_empty_seq(power->get_sort()), dep);
        e->add_subst(s2);
        child->apply_subst(m_sg, s2);
        expr* exp_n = get_power_exponent(power);
        SASSERT(exp_n);
        const expr_ref len_base = compute_length_expr(base);
        e->add_side_constraint(mk_constraint(
            m.mk_or(a.mk_eq(exp_n, a.mk_int(0)),
                    a.mk_eq(len_base, a.mk_int(0))),
            dep));

        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_num_cmp
    // For equations involving two power tokens u^m and u^n with the same base,
    // branch on the numeric relationship: m <= n vs n < m.
    // Generates proper integer side constraints for each branch.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_num_cmp(nielsen_node* node) {

        // Look for two directional endpoint power tokens with the same base.
        for (str_eq const& eq : node->str_eqs()) {
            SASSERT(eq.well_formed());
            if (eq.is_trivial())
                continue;
            for (unsigned od = 0; od < 2; ++od) {
                const bool fwd = (od == 0);
                euf::snode const* lhead = dir_token(eq.m_lhs, fwd);
                euf::snode const* rhead = dir_token(eq.m_rhs, fwd);
                if (!lhead || !rhead)
                    continue;
                if (!lhead->is_power() || !rhead->is_power())
                    continue;
                if (lhead->num_args() < 1 || rhead->num_args() < 1)
                    continue;
                // same base: compare the two powers
                if (lhead->arg0() != rhead->arg0())
                    continue;

                // Skip if the exponents differ by a constant — simplify_and_init's
                // directional power elimination already handles that case.
                expr* exp_m = get_power_exponent(lhead);
                expr* exp_n = get_power_exponent(rhead);
                if (!exp_m || !exp_n)
                    continue;
                rational diff;
                SASSERT(!get_const_power_diff(exp_n, exp_m, a, diff)); // handled by simplification

                // Both children clone the node's string constraints verbatim (only
                // the edge's integer side constraint differs) — mark them as
                // arith splits so they are exempt from the sibling loop-cut and
                // the unsat cache (see search_dfs / is_signature_alias).
                // Branch 1 (explored first): n < m  (add constraint c ≥ p + 1)
                {
                    nielsen_node *child = mk_child(node);
                    child->set_arith_split();
                    nielsen_edge *e = mk_edge(node, child, "power cmp &lt;", true);
                    const expr_ref n_plus_1(a.mk_add(exp_n, a.mk_int(1)), m);
                    e->add_side_constraint(mk_constraint(a.mk_ge(exp_m, n_plus_1), eq.m_dep));
                }
                // Branch 2 (explored second): m <= n  (add constraint p ≥ c)
                {
                    nielsen_node *child = mk_child(node);
                    child->set_arith_split();
                    nielsen_edge *e = mk_edge(node, child, "power cmp &ge;", true);
                    e->add_side_constraint(mk_constraint(a.mk_ge(exp_n, exp_m), eq.m_dep));
                }
                return true;
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_split_power_elim
    // When one side starts with a power w^p, call CommPower on the other
    // side to count base-pattern occurrences c. If c > 0 and the ordering
    // between p and c cannot be determined, create two branches:
    //   Branch 1: p < c   (add constraint c ≥ p + 1)
    //   Branch 2: c ≤ p   (add constraint p ≥ c)
    // After branching, simplify_and_init's CommPower pass (3c) can resolve
    // the ordering deterministically and cancel the matched portion.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_split_power_elim(nielsen_node* node) {

        for (str_eq const& eq : node->str_eqs()) {
            SASSERT(eq.well_formed());
            if (eq.is_trivial())
                continue;

            for (int side = 0; side < 2; ++side) {
                // both sides are non-null by str_eq's well_formed() invariant
                euf::snode const* pow_side   = (side == 0) ? eq.m_lhs : eq.m_rhs;
                euf::snode const* other_side = (side == 0) ? eq.m_rhs : eq.m_lhs;

                for (unsigned od = 0; od < 2; ++od) {
                    const bool fwd = od == 0;
                    euf::snode const* end_tok = dir_token(pow_side, fwd);
                    if (!end_tok || !end_tok->is_power())
                        continue;
                    euf::snode const* base_sn = end_tok->arg0();
                    expr* pow_exp = get_power_exp_expr(end_tok, m_seq);
                    SASSERT(base_sn && pow_exp);   // guaranteed for an s_power token

                    auto [count, consumed] = comm_power(base_sn, other_side, m, a, m_seq, fwd);
                    if (!count.get() || consumed == 0)
                        continue;

                    expr_ref norm_count = normalize_arith(m_rw, count);

                    // Skip if ordering is already deterministic — simplify_and_init
                    // pass 3c should have handled it.
                    rational diff;
                    if (get_const_power_diff(norm_count, pow_exp, a, diff))
                        continue;

                    // Both children clone the node's string constraints verbatim —
                    // mark them as arith splits, exempt from the sibling loop-cut
                    // and the unsat cache (see search_dfs / is_signature_alias).
                    // Branch 1: pow_exp < count (i.e., count >= pow_exp + 1)
                    {
                        nielsen_node *child = mk_child(node);
                        child->set_arith_split();
                        nielsen_edge *e = mk_edge(node, child, "power elim &gt;", true);
                        const expr_ref pow_plus1(a.mk_add(pow_exp, a.mk_int(1)), m);
                        e->add_side_constraint(mk_constraint(a.mk_ge(norm_count, pow_plus1), eq.m_dep));
                    }
                    // Branch 2: count <= pow_exp (i.e., pow_exp >= count)
                    {
                        nielsen_node *child = mk_child(node);
                        child->set_arith_split();
                        nielsen_edge *e = mk_edge(node, child, "power elim &le;", true);
                        e->add_side_constraint(mk_constraint(a.mk_ge(pow_exp, norm_count), eq.m_dep));
                    }
                    return true;
                }
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Helper: concrete string value of a ground token run (ε, char, or a
    // concat of chars).  Returns false on any non-concrete token.
    // -----------------------------------------------------------------------

    static bool ground_zstring(euf::snode const* s, seq_util& seq, zstring& out) {
        out.reset();
        if (!s)
            return false;
        if (s->is_empty())
            return true;
        euf::snode_vector toks;
        s->collect_tokens(toks);
        for (euf::snode const* t : toks) {
            unsigned val;
            if (!t->is_char())
                return false;
            VERIFY(seq.is_const_char(to_app(t->get_expr())->get_arg(0), val));
            out += zstring(val);
        }
        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_fine_wilf
    // For an equation  U^n · V = Y · W^m · Z  (up to direction / side swap)
    // where U^n is the directional head of one side, Y a possibly-empty run
    // of concrete chars and W^m the first power on the other side with a
    // DIFFERENT base, split on the overlap length
    //     O = min(n·|U| − |Y|, m·|W|)
    // against the Fine & Wilf threshold T = |U| + |W| (exact bound is
    // T − gcd(|U|,|W|); dropping the gcd term is a sound weakening).
    // The overlap word has periods |U| and |W|; O ≥ T forces (F&W) the
    // |Y|-rotated conjugate of U and W to share a primitive root, so one of
    // the powers can be eliminated.  The three cases partition all models:
    //   Case 1 (O < T): one exponent is bounded.
    //   Case 2 (O ≥ T, LHS power ends first):  U^n eliminated.
    //   Case 3 (O ≥ T, RHS power ends first):  W^m eliminated.
    // Ground bases (fast path): the conjugate/prefix conditions are decided
    // concretely (failure prunes cases 2/3 — they are F&W-unsat), the cut
    // position in the other base is enumerated, and case 1 unrolls the
    // concretely-bounded exponent — every child is a progress edge.
    // Symbolic bases: fresh cut variables axiomatize the alignment
    // (U^n = Y·R1, W^m = R1·R2, V = R2·Z; both directions of the
    // equivalence hold, no commutativity lemma needed) and case 1 is an
    // arith-split child guarded against refire via m_fw_applied.
    // Preempts apply_const_num_unwinding's divergent one-copy peel loop on
    // different-base power vs power heads.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_fine_wilf(nielsen_node* node) {

        // Per-modifier cap on ground enumeration fan-out; larger instances
        // fall back to the symbolic encoding (still linear for ground bases).
        static constexpr unsigned FW_ENUM_CAP = 64;

        for (unsigned eq_idx = 0; eq_idx < node->str_eqs().size(); ++eq_idx) {
            str_eq const& eq = node->str_eqs()[eq_idx];
            if (eq.is_trivial())
                continue;

            for (unsigned od = 0; od < 2; ++od) {
                const bool fwd = od == 0;
                for (unsigned sd = 0; sd < 2; ++sd) {
                    euf::snode const* sideA = sd == 0 ? eq.m_lhs : eq.m_rhs;
                    euf::snode const* sideB = sd == 0 ? eq.m_rhs : eq.m_lhs;

                    euf::snode const* upow = dir_token(sideA, fwd);
                    if (!upow || !upow->is_power() || upow->num_args() < 1)
                        continue;

                    // other side: concrete-char run Y, then a power W^m
                    euf::snode_vector btoks;
                    collect_tokens_dir(sideB, fwd, btoks);
                    unsigned yi = 0;
                    while (yi < btoks.size() && btoks[yi]->is_char())
                        ++yi;
                    if (yi >= btoks.size() || !btoks[yi]->is_power() || btoks[yi]->num_args() < 1)
                        continue;
                    euf::snode const* wpow = btoks[yi];
                    // same base: NumCmp (priority 3) / simplify 3c–3e territory
                    if (wpow->arg0() == upow->arg0())
                        continue;

                    expr* exp_n = get_power_exponent(upow);
                    expr* exp_m = get_power_exponent(wpow);
                    expr* u_base_e = get_power_base_expr(upow, m_seq);
                    expr* w_base_e = get_power_base_expr(wpow, m_seq);
                    if (!exp_n || !exp_m || !u_base_e || !w_base_e)
                        continue;

                    const uint64_t key = (uint64_t(eq.m_lhs->id()) << 33) |
                                         (uint64_t(eq.m_rhs->id()) << 1) | (fwd ? 1 : 0);
                    if (node->fw_applied(key))
                        continue;

                    // Mirror-space values (direction folded away: for fwd=false
                    // all strings are reversed, so the overlap is again at the
                    // "front"; real snodes are rebuilt via dir_concat + reverse).
                    zstring u_s, w_s;
                    const bool u_ground = ground_zstring(upow->arg0(), m_seq, u_s);
                    const bool w_ground = ground_zstring(wpow->arg0(), m_seq, w_s);
                    // ε-base powers are degenerate (handled by the simplify
                    // passes / power epsilon) — not our pattern.
                    if ((u_ground && u_s.empty()) || (w_ground && w_s.empty()))
                        continue;
                    zstring mu = fwd ? u_s : u_s.reverse();
                    zstring mw = fwd ? w_s : w_s.reverse();
                    zstring my;
                    for (unsigned i = 0; i < yi; ++i) {
                        unsigned val;
                        VERIFY(m_seq.is_const_char(to_app(btoks[i]->get_expr())->get_arg(0), val));
                        my += zstring(val);
                    }
                    const unsigned Ly = my.length();

                    // V = sideA minus the head power; Z = sideB after W^m
                    euf::snode const* v_sn = nullptr;
                    {
                        euf::snode_vector atoks;
                        collect_tokens_dir(sideA, fwd, atoks);
                        SASSERT(!atoks.empty() && atoks[0] == upow);
                        for (unsigned i = 1; i < atoks.size(); ++i)
                            v_sn = dir_concat(m_sg, v_sn, atoks[i], fwd);
                    }
                    if (!v_sn)
                        v_sn = m_sg.mk_empty_seq(sideA->get_sort());
                    euf::snode const* z_sn = nullptr;
                    for (unsigned i = yi + 1; i < btoks.size(); ++i)
                        z_sn = dir_concat(m_sg, z_sn, btoks[i], fwd);
                    if (!z_sn)
                        z_sn = m_sg.mk_empty_seq(sideB->get_sort());
                    euf::snode const* y_sn = nullptr;
                    for (unsigned i = 0; i < yi; ++i)
                        y_sn = dir_concat(m_sg, y_sn, btoks[i], fwd);

                    const expr_ref len_upow = compute_length_expr(upow); // n·|U|
                    const expr_ref len_wpow = compute_length_expr(wpow); // m·|W|
                    const expr_ref zero(a.mk_int(0), m);
                    const dep_tracker dep = eq.m_dep;

                    // Ground feasibility of cases 2/3 (both require O ≥ T, and
                    // by F&W then Y ≺ U^ω and rot(U, Ly mod |U|)·W = W·rot(...)).
                    // gen23=false ⟹ cases 2/3 are unsat and are not generated.
                    bool gen23 = true;
                    if (u_ground && w_ground) {
                        const unsigned Lu = mu.length();
                        for (unsigned i = 0; i < Ly && gen23; ++i)
                            gen23 = my[i] == mu[i % Lu];
                        if (gen23) {
                            const unsigned r = Ly % Lu;
                            const zstring rot = mu.extract(r, Lu - r) + mu.extract(0, r);
                            gen23 = (rot + mw) == (mw + rot);
                        }
                    }

                    // Refire guard: the symbolic case-1 child keeps the equation
                    // verbatim; without the mark the identical split would be
                    // re-emitted below it forever (arith splits escape the
                    // loop-cut).  Set before mk_child so children inherit it.
                    node->mark_fw_applied(key);

                    const unsigned Lu = mu.length(), Lw = mw.length();
                    const bool ground = u_ground && w_ground &&
                        (Ly + Lu + Lw - 1) / Lu + (Lu + Lw - 1) / Lw + 2 +
                            (gen23 ? Lu + Lw : 0) <= FW_ENUM_CAP;

                    if (ground) {
                        // ---- ground fast path: all children progress ----
                        const unsigned N = (Ly + Lu + Lw - 1) / Lu; // max n: n·Lu < Ly+Lu+Lw
                        const unsigned M = (Lu + Lw - 1) / Lw;      // max m: m·Lw < Lu+Lw
                        const auto unroll = [&](euf::snode const* base, sort* srt, unsigned c) {
                            euf::snode const* r = c == 0 ? m_sg.mk_empty_seq(srt) : base;
                            for (unsigned i = 1; i < c; ++i)
                                r = m_sg.mk_concat(r, base);
                            return r;
                        };

                        // Case 1a: n = 0..N (⟺ n·Lu − Ly < T), unroll U^n.
                        for (unsigned c = 0; c <= N; ++c) {
                            nielsen_node* child = mk_child(node);
                            nielsen_edge* e = mk_edge(node, child, "fine-wilf n", true);
                            const nielsen_subst s(upow, unroll(upow->arg0(), upow->get_sort(), c), dep);
                            e->add_subst(s);
                            child->apply_subst(m_sg, s);
                            e->add_side_constraint(mk_constraint(a.mk_eq(exp_n, a.mk_int(c)), dep));
                        }
                        // Case 1b: m = 0..M (⟺ m·Lw < T) ∧ n > N (disjoint from 1a).
                        for (unsigned c = 0; c <= M; ++c) {
                            nielsen_node* child = mk_child(node);
                            nielsen_edge* e = mk_edge(node, child, "fine-wilf m", true);
                            const nielsen_subst s(wpow, unroll(wpow->arg0(), wpow->get_sort(), c), dep);
                            e->add_subst(s);
                            child->apply_subst(m_sg, s);
                            e->add_side_constraint(mk_constraint(a.mk_eq(exp_m, a.mk_int(c)), dep));
                            e->add_side_constraint(mk_constraint(a.mk_ge(exp_n, a.mk_int(N + 1)), dep));
                        }
                        if (gen23) {
                            // Case 2: U^n ends inside W^m — cut W at mirror-phase p:
                            // n·Lu = Ly + k·Lw + p.  Remainder: V = Q'·W^(m−k−1)·Z
                            // (p = 0: V = W^(m−k)·Z, covering the k = m boundary).
                            const expr_ref k_e = m_sk.mk("fw.k", eq.m_lhs->get_expr(), eq.m_rhs->get_expr(),
                                                         a.mk_int(fwd ? 1 : 0), a.mk_int());
                            for (unsigned p = 0; p < Lw; ++p) {
                                nielsen_node* child = mk_child(node);
                                nielsen_edge* e = mk_edge(node, child, "fine-wilf elim L", true);
                                expr_ref rem_exp(p == 0 ? a.mk_sub(exp_m, k_e)
                                                        : a.mk_sub(exp_m, a.mk_add(k_e, a.mk_int(1))), m);
                                rem_exp = normalize_arith(m_rw, rem_exp);
                                euf::snode const* pow_sn = m_sg.mk(expr_ref(m_seq.str.mk_power(w_base_e, rem_exp), m));
                                euf::snode const* rhs_new = dir_concat(m_sg, pow_sn, z_sn, fwd);
                                if (p > 0) {
                                    const zstring q_m = mw.extract(p, Lw - p);
                                    euf::snode const* qp_sn = m_sg.mk(m_seq.str.mk_string(fwd ? q_m : q_m.reverse()));
                                    rhs_new = dir_concat(m_sg, qp_sn, rhs_new, fwd);
                                }
                                auto& eqs = child->str_eqs();
                                eqs[eq_idx] = eqs.back();
                                eqs.pop_back();
                                eqs.push_back(str_eq(m, v_sn, rhs_new, dep));
                                // n·Lu = Ly + k·Lw + p
                                e->add_side_constraint(mk_constraint(a.mk_eq(len_upow,
                                    a.mk_add(a.mk_int(Ly + p), a.mk_mul(a.mk_int(Lw), k_e))), dep));
                                // overlap ≥ T (disjoint from case 1)
                                e->add_side_constraint(mk_constraint(
                                    a.mk_ge(len_upow, a.mk_int(Ly + Lu + Lw)), dep));
                                e->add_side_constraint(mk_constraint(a.mk_ge(k_e, zero), dep));
                                e->add_side_constraint(mk_constraint(
                                    a.mk_ge(exp_m, p == 0 ? k_e.get() : a.mk_add(k_e, a.mk_int(1))), dep));
                            }
                            // Case 3: W^m ends strictly inside U^n — cut U at
                            // mirror-phase p: Ly + m·Lw = k·Lu + p.  Remainder:
                            // Q''·U^(n−k−1)·V = Z (p = 0: U^(n−k)·V = Z).
                            const expr_ref k2_e = m_sk.mk("fw.k2", eq.m_lhs->get_expr(), eq.m_rhs->get_expr(),
                                                          a.mk_int(fwd ? 1 : 0), a.mk_int());
                            for (unsigned p = 0; p < Lu; ++p) {
                                nielsen_node* child = mk_child(node);
                                nielsen_edge* e = mk_edge(node, child, "fine-wilf elim R", true);
                                expr_ref rem_exp(p == 0 ? a.mk_sub(exp_n, k2_e)
                                                        : a.mk_sub(exp_n, a.mk_add(k2_e, a.mk_int(1))), m);
                                rem_exp = normalize_arith(m_rw, rem_exp);
                                euf::snode const* pow_sn = m_sg.mk(expr_ref(m_seq.str.mk_power(u_base_e, rem_exp), m));
                                euf::snode const* lhs_new = dir_concat(m_sg, pow_sn, v_sn, fwd);
                                if (p > 0) {
                                    const zstring q_m = mu.extract(p, Lu - p);
                                    euf::snode const* qq_sn = m_sg.mk(m_seq.str.mk_string(fwd ? q_m : q_m.reverse()));
                                    lhs_new = dir_concat(m_sg, qq_sn, lhs_new, fwd);
                                }
                                auto& eqs = child->str_eqs();
                                eqs[eq_idx] = eqs.back();
                                eqs.pop_back();
                                eqs.push_back(str_eq(m, lhs_new, z_sn, dep));
                                // Ly + m·Lw = k·Lu + p
                                e->add_side_constraint(mk_constraint(
                                    a.mk_eq(a.mk_add(a.mk_int(Ly), len_wpow),
                                            a.mk_add(a.mk_int(p), a.mk_mul(a.mk_int(Lu), k2_e))), dep));
                                // overlap ≥ T (disjoint from case 1)
                                e->add_side_constraint(mk_constraint(
                                    a.mk_ge(len_wpow, a.mk_int(Lu + Lw)), dep));
                                e->add_side_constraint(mk_constraint(a.mk_ge(k2_e, zero), dep));
                                // strict: W^m ends before U^n does
                                e->add_side_constraint(mk_constraint(
                                    a.mk_ge(exp_n, a.mk_add(k2_e, a.mk_int(1))), dep));
                            }
                        }
                        return true;
                    }

                    // ---- symbolic path ----
                    const expr_ref lu_e = compute_length_expr(upow->arg0());
                    const expr_ref lw_e = compute_length_expr(wpow->arg0());
                    const expr_ref t_e(a.mk_add(lu_e, lw_e), m);
                    const expr_ref ly_e(a.mk_int(Ly), m);

                    // Case 1: small overlap — string constraints kept verbatim,
                    // only the (possibly nonlinear) bound is added.
                    {
                        nielsen_node* child = mk_child(node);
                        child->set_arith_split();
                        nielsen_edge* e = mk_edge(node, child, "fine-wilf small", true);
                        e->add_side_constraint(mk_constraint(
                            m.mk_or(a.mk_lt(a.mk_sub(len_upow, ly_e), t_e),
                                    a.mk_lt(len_wpow, t_e)), dep));
                    }
                    if (gen23) {
                        // Case 2: U^n ends inside W^m.  Fresh cuts R1 (overlap
                        // beyond Y) and R2 (rest of W^m):
                        //   U^n = Y·R1,  W^m = R1·R2,  V = R2·Z.
                        {
                            const expr_ref r1_e = m_sk.mk("fw.r1", eq.m_lhs->get_expr(), eq.m_rhs->get_expr(),
                                                          a.mk_int(fwd ? 1 : 0), sideA->get_sort());
                            const expr_ref r2_e = m_sk.mk("fw.r2", eq.m_lhs->get_expr(), eq.m_rhs->get_expr(),
                                                          a.mk_int(fwd ? 1 : 0), sideA->get_sort());
                            euf::snode const* r1_sn = m_sg.mk(r1_e);
                            euf::snode const* r2_sn = m_sg.mk(r2_e);
                            const expr_ref len_r1(m_seq.str.mk_length(r1_e), m);
                            const expr_ref len_r2(m_seq.str.mk_length(r2_e), m);

                            nielsen_node* child = mk_child(node);
                            nielsen_edge* e = mk_edge(node, child, "fine-wilf elim L", false);
                            auto& eqs = child->str_eqs();
                            eqs[eq_idx] = eqs.back();
                            eqs.pop_back();
                            eqs.push_back(str_eq(m, upow, dir_concat(m_sg, y_sn, r1_sn, fwd), dep));
                            eqs.push_back(str_eq(m, wpow, dir_concat(m_sg, r1_sn, r2_sn, fwd), dep));
                            eqs.push_back(str_eq(m, v_sn, dir_concat(m_sg, r2_sn, z_sn, fwd), dep));
                            // |R1| = n·|U| − Ly  and the F&W threshold
                            e->add_side_constraint(mk_constraint(
                                a.mk_eq(a.mk_add(ly_e, len_r1), len_upow), dep));
                            e->add_side_constraint(mk_constraint(a.mk_ge(len_r1, t_e), dep));
                            // |R1| + |R2| = m·|W|; |R2| ≥ 0 covers the boundary
                            e->add_side_constraint(mk_constraint(
                                a.mk_eq(a.mk_add(len_r1, len_r2), len_wpow), dep));
                            e->add_side_constraint(mk_constraint(a.mk_ge(len_r2, zero), dep));
                        }
                        // Case 3: W^m ends strictly inside U^n.  Fresh cuts
                        // S1 = Y·W^m and S2 (rest of U^n):
                        //   U^n = S1·S2,  S1 = Y·W^m,  Z = S2·V.
                        {
                            const expr_ref s1_e = m_sk.mk("fw.s1", eq.m_lhs->get_expr(), eq.m_rhs->get_expr(),
                                                          a.mk_int(fwd ? 1 : 0), sideA->get_sort());
                            const expr_ref s2_e = m_sk.mk("fw.s2", eq.m_lhs->get_expr(), eq.m_rhs->get_expr(),
                                                          a.mk_int(fwd ? 1 : 0), sideA->get_sort());
                            euf::snode const* s1_sn = m_sg.mk(s1_e);
                            euf::snode const* s2_sn = m_sg.mk(s2_e);
                            const expr_ref len_s1(m_seq.str.mk_length(s1_e), m);
                            const expr_ref len_s2(m_seq.str.mk_length(s2_e), m);

                            nielsen_node* child = mk_child(node);
                            nielsen_edge* e = mk_edge(node, child, "fine-wilf elim R", false);
                            auto& eqs = child->str_eqs();
                            eqs[eq_idx] = eqs.back();
                            eqs.pop_back();
                            eqs.push_back(str_eq(m, upow, dir_concat(m_sg, s1_sn, s2_sn, fwd), dep));
                            eqs.push_back(str_eq(m, s1_sn, dir_concat(m_sg, y_sn, wpow, fwd), dep));
                            eqs.push_back(str_eq(m, z_sn, dir_concat(m_sg, s2_sn, v_sn, fwd), dep));
                            // |S1| = Ly + m·|W|, m·|W| ≥ T, strictness |S2| ≥ 1,
                            // |S1| + |S2| = n·|U|
                            e->add_side_constraint(mk_constraint(
                                a.mk_eq(len_s1, a.mk_add(ly_e, len_wpow)), dep));
                            e->add_side_constraint(mk_constraint(a.mk_ge(len_wpow, t_e), dep));
                            e->add_side_constraint(mk_constraint(a.mk_ge(len_s2, a.mk_int(1)), dep));
                            e->add_side_constraint(mk_constraint(
                                a.mk_eq(a.mk_add(len_s1, len_s2), len_upow), dep));
                        }
                    }
                    return true;
                }
            }
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_const_num_unwinding
    // For a power token u^n facing a constant (char) head,
    // branch: (1) n = 0 → u^n = ε, (2) n >= 1 → peel one u from power.
    // Generates integer side constraints for each branch.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_const_num_unwinding(nielsen_node* node) {

        euf::snode const* power = nullptr;
        euf::snode const* other_head = nullptr;
        str_eq const *eq = nullptr;
        bool fwd = true;
        if (!find_power_vs_non_var(node, power, other_head, eq, fwd))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode const* base = power->arg0();
        expr *exp_n = get_power_exponent(power);
        expr *zero = a.mk_int(0);
        expr *one = a.mk_int(1);

        // Branch 1 (explored first): n = 0 → replace power with ε (progress)
        // Side constraint: n = 0
        nielsen_node *child = mk_child(node);
        nielsen_edge *e = mk_edge(node, child, "unwinding 0", true);
        const nielsen_subst s1(power, m_sg.mk_empty_seq(power->get_sort()), eq->m_dep);
        e->add_subst(s1);
        child->apply_subst(m_sg, s1);
        if (exp_n)
            e->add_side_constraint(mk_constraint(a.mk_eq(exp_n, zero), eq->m_dep));

        // Branch 2 (explored second): n >= 1 → peel one u: replace u^n with u · u^(n-1)
        // Side constraint: n >= 1
        // Use a nested power base^(n-1) rather than a fresh string variable, so
        // simplify_and_init can merge and cancel adjacent same-base powers.
        const seq_util &seq = m_sg.get_seq_util();
        expr *power_e = power->get_expr();
        SASSERT(power_e);
        expr *base_expr = to_app(power_e)->get_arg(0);
        const expr_ref n_minus_1 = normalize_arith(m_rw, a.mk_sub(exp_n, one));
        const expr_ref nested_pow(seq.str.mk_power(base_expr, n_minus_1), m);
        euf::snode const* nested_power_snode = m_sg.mk(nested_pow);

        euf::snode const* replacement = dir_concat(m_sg, base, nested_power_snode, fwd);
        child = mk_child(node);
        e = mk_edge(node, child, "unwinding &gt;", true);
        const nielsen_subst s2(power, replacement, eq->m_dep);
        e->add_subst(s2);
        child->apply_subst(m_sg, s2);
        if (exp_n)
            e->add_side_constraint(mk_constraint(a.mk_ge(exp_n, one), eq->m_dep));

        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_gpower_intr
    // Generalized power introduction: for an equation where one side's head
    // is a variable v and the other side has a ground prefix followed by a
    // variable x that forms a dependency cycle back to v, introduce
    // v = base^n · suffix where base is the ground prefix.
    // Generates side constraints n >= 0 and 0 <= len(suffix) < len(base).
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_gpower_intr(nielsen_node* node) {
        for (str_eq const& eq : node->str_eqs()) {
            SASSERT(eq.well_formed());
            if (eq.is_trivial())
                continue;

            // Try both directions
            for (unsigned od = 0; od < 2; ++od) {
                const bool fwd = (od == 0);
                euf::snode const* lhead = dir_token(eq.m_lhs, fwd);
                euf::snode const* rhead = dir_token(eq.m_rhs, fwd);
                if (!lhead || !rhead)
                    continue;

                // Orientation 1: RHS directional head is var, scan LHS in that
                // direction for ground prefix + matching cycle var.
                if (rhead->is_var() && !lhead->is_var()) {
                    euf::snode_vector toks;
                    collect_tokens_dir(eq.m_lhs, fwd, toks);
                    euf::snode_vector ground_prefix;
                    euf::snode const* target_var = nullptr;
                    for (unsigned i = 0; i < toks.size(); ++i) {
                        if (toks[i]->is_var()) {
                            target_var = toks[i];
                            break;
                        }
                        ground_prefix.push_back(toks[i]);
                    }
                    if (target_var && !ground_prefix.empty() && target_var->id() == rhead->id()) {
                        if (fire_gpower_intro(node, eq, rhead, ground_prefix, fwd))
                            return true;
                    }
                }

                // Orientation 2: LHS directional head is var, scan RHS analogously.
                if (lhead->is_var() && !rhead->is_var()) {
                    euf::snode_vector toks;
                    collect_tokens_dir(eq.m_rhs, fwd, toks);
                    euf::snode_vector ground_prefix;
                    euf::snode const* target_var = nullptr;
                    for (unsigned i = 0; i < toks.size(); ++i) {
                        if (toks[i]->is_var()) {
                            target_var = toks[i];
                            break;
                        }
                        ground_prefix.push_back(toks[i]);
                    }
                    if (target_var && !ground_prefix.empty() && target_var->id() == lhead->id()) {
                        if (fire_gpower_intro(node, eq, lhead, ground_prefix, fwd))
                            return true;
                    }
                }
            }
            // TODO: Extend to transitive cycles across multiple equations
            // Currently only self-cycles are detected.
        }
        return false;
    }

    bool nielsen_graph::fire_gpower_intro(
        nielsen_node* node, str_eq const& eq,
        euf::snode const* var, euf::snode_vector const& ground_prefix_orig, const bool fwd) {

        // Compress repeated patterns in the ground prefix.
        // e.g., [a,b,a,b] has minimal period 2 → use [a,b] as the power base.
        // This ensures we use the minimal repeating unit: x = (ab)^n · suffix
        // instead of x = (abab)^n · suffix.
        euf::snode_vector ground_prefix;
        const unsigned n = ground_prefix_orig.size();
        unsigned period = n;
        for (unsigned p = 1; p <= n / 2; ++p) {
            if (n % p != 0)
                continue;
            bool match = true;
            for (unsigned i = p; i < n && match; ++i)
                match = ground_prefix_orig[i]->id() == ground_prefix_orig[i % p]->id();
            if (match) {
                period = p;
                break;
            }
        }
        for (unsigned i = 0; i < period; ++i) {
            ground_prefix.push_back(ground_prefix_orig[i]);
        }

        // If the compressed prefix is a single power snode, unwrap it to use
        // its base tokens, avoiding nested powers.
        // E.g., [(ab)^3] → [a, b] so we get (ab)^n instead of ((ab)^3)^n.
        if (ground_prefix.size() == 1 && ground_prefix[0]->is_power()) {
            expr* base_e = get_power_base_expr(ground_prefix[0], m_seq);
            if (base_e) {
                euf::snode const* base_sn = m_sg.mk(base_e);
                if (base_sn) {
                    euf::snode_vector base_toks;
                    collect_tokens_dir(base_sn, fwd, base_toks);
                    if (!base_toks.empty()) {
                        ground_prefix.reset();
                        ground_prefix.append(base_toks);
                    }
                }
            }
        }

        const unsigned base_len = ground_prefix.size();

        // Build base string expression from ground prefix tokens.
        // Each s_char snode's get_expr() is already seq.unit(ch) (a string).
        expr_ref base_str(m);
        for (unsigned i = 0; i < base_len; ++i) {
            expr* tok_expr = ground_prefix[i]->get_expr();
            if (!tok_expr) return false;
            if (i == 0)
                base_str = tok_expr;
            else if (fwd)
                base_str = m_seq.str.mk_concat(base_str, tok_expr);
            else
                base_str = m_seq.str.mk_concat(tok_expr, base_str);
        }

        // Create fresh exponent variable and power expression: base^n
        const expr_ref fresh_n = get_or_create_gpower_n_var(var);
        const expr_ref power_expr(m_seq.str.mk_power(base_str, fresh_n), m);
        euf::snode const* power_snode = m_sg.mk(power_expr);
        if (!power_snode)
            return false;

        const expr_ref zero(a.mk_int(0), m);

        // Generate children:
        // P(t0 · t1 · ... · t_{k-1}) = P(t0) | t0·P(t1) | ... | t0·...·t_{k-2}·P(t_{k-1})
        // For char tokens P(c) = {ε}, for power tokens P(u^m) = {u^m', 0 ≤ m' ≤ m}.
        // Child at position i substitutes var → base^n · t0·...·t_{i-1} · P(t_i).
        for (unsigned i = 0; i < base_len; ++i) {
            euf::snode const* tok = ground_prefix[i];

            // Skip char position when preceding token is a power:
            // The power case at i-1 with 0 ≤ m' ≤ exp already covers m' = exp,
            // which produces the same result. Using the original exponent here
            // creates a rigid coupling that causes cycling.
            if (!tok->is_power() && i > 0 && ground_prefix[i - 1]->is_power())
                continue;

            // Build full-token prefix: ground_prefix[0..i-1]
            euf::snode const* prefix_sn = nullptr;
            for (unsigned j = 0; j < i; ++j)
                prefix_sn = (j == 0) ? ground_prefix[0] : dir_concat(m_sg, prefix_sn, ground_prefix[j], fwd);

            euf::snode const* replacement;
            expr_ref fresh_m(m);

            if (tok->is_power()) {
                // Token is a power u^exp: use fresh m' with 0 ≤ m' ≤ exp
                const expr * inner_exp = get_power_exponent(tok);
                expr* inner_base = get_power_base_expr(tok, m_seq);
                if (inner_exp && inner_base) {
                    fresh_m = get_or_create_gpower_m_var(var);
                    expr_ref partial_pow(m_seq.str.mk_power(inner_base, fresh_m), m);
                    euf::snode const* partial_sn = m_sg.mk(partial_pow);
                    euf::snode const* suffix_sn = prefix_sn ? dir_concat(m_sg, prefix_sn, partial_sn, fwd) : partial_sn;
                    replacement = dir_concat(m_sg, power_snode, suffix_sn, fwd);
                }
                else {
                    // Fallback: use full token (shouldn't normally happen)
                    euf::snode const* suffix_sn = prefix_sn ? dir_concat(m_sg, prefix_sn, tok, fwd) : tok;
                    replacement = dir_concat(m_sg, power_snode, suffix_sn, fwd);
                }
            }
            else
                // Token is a char: P(char) = ε, suffix = just the prefix
                replacement = prefix_sn ? dir_concat(m_sg, power_snode, prefix_sn, fwd) : power_snode;

            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, "power intr", true);
            // The replacement is built from power tokens whose bases must not
            // contain `var` (deep check: collect_tokens is opaque to bases).
            SASSERT(!deep_contains_var(replacement, var));
            nielsen_subst s(var, replacement, eq.m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);

            // Side constraint: n >= 0
            e->add_side_constraint(mk_constraint(a.mk_ge(fresh_n, zero), eq.m_dep));

            // Side constraints for fresh partial exponent
            if (fresh_m.get()) {
                expr* inner_exp = get_power_exponent(tok);
                // m' >= 0
                e->add_side_constraint(mk_constraint(a.mk_ge(fresh_m, zero), eq.m_dep));
                // m' <= inner_exp
                e->add_side_constraint(mk_constraint(a.mk_ge(inner_exp, fresh_m), eq.m_dep));
            }
        }
        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_signature_split
    // Heuristic equation split based on a shortest prefix signature (i, j):
    // prefixes u[0..i-1], v[0..j-1] must contain at least one variable and
    // every variable in one prefix must occur in the other prefix.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_signature_split(nielsen_node* node) {
        auto first_var_pos = [](euf::snode_vector const& toks) {
            for (unsigned k = 0; k < toks.size(); ++k)
                if (toks[k]->is_var())
                    return k;
            return toks.size();
        };

        auto const& eqs = node->str_eqs();
        for (unsigned eq_idx = 0; eq_idx < eqs.size(); ++eq_idx) {
            str_eq const& eq = eqs[eq_idx];
            SASSERT(eq.well_formed());
            if (eq.is_trivial())
                continue;

            euf::snode_vector lhs_toks, rhs_toks;
            eq.m_lhs->collect_tokens(lhs_toks);
            eq.m_rhs->collect_tokens(rhs_toks);

            // Start from the first variable on each side; if one side has no
            // variable, this equation has no usable signature.
            const unsigned i0 = first_var_pos(lhs_toks);
            const unsigned j0 = first_var_pos(rhs_toks);
            if (i0 == lhs_toks.size() || j0 == rhs_toks.size())
                continue;

            std::unordered_map<expr*, unsigned> lhs_first, rhs_first;
            lhs_first.reserve(lhs_toks.size());
            rhs_first.reserve(rhs_toks.size());

            for (unsigned k = 0; k < lhs_toks.size(); ++k) {
                if (!lhs_toks[k]->is_var())
                    continue;
                expr* x = lhs_toks[k]->get_expr();
                if (!lhs_first.contains(x))
                    lhs_first.emplace(x, k);
            }
            for (unsigned k = 0; k < rhs_toks.size(); ++k) {
                if (!rhs_toks[k]->is_var())
                    continue;
                expr* x = rhs_toks[k]->get_expr();
                if (!rhs_first.contains(x))
                    rhs_first.emplace(x, k);
            }

            svector<unsigned> lhs_need_j(lhs_toks.size(), UINT_MAX);
            svector<unsigned> rhs_need_i(rhs_toks.size(), UINT_MAX);

            // Prefix summary arrays:
            // lhs_need_j[k] = maximum first-occurrence index in rhs for any
            // variable seen in lhs[0..k]. Symmetric for rhs_need_i.
            // A value of UINT_MAX means "no variable requirement yet".
            // A value of UINT_MAX-1 means "fail: some prefix variable does not
            // occur on the opposite side at all".
            constexpr unsigned FAIL_MARK = UINT_MAX - 1;
            unsigned need = UINT_MAX;
            for (unsigned k = 0; k < lhs_toks.size(); ++k) {
                if (lhs_toks[k]->is_var()) {
                    auto it = rhs_first.find(lhs_toks[k]->get_expr());
                    if (it == rhs_first.end())
                        need = FAIL_MARK;
                    else if (need != FAIL_MARK)
                        need = (need == UINT_MAX) ? it->second : std::max(need, it->second);
                }
                lhs_need_j[k] = need;
            }

            need = UINT_MAX;
            for (unsigned k = 0; k < rhs_toks.size(); ++k) {
                if (rhs_toks[k]->is_var()) {
                    auto it = lhs_first.find(rhs_toks[k]->get_expr());
                    if (it == lhs_first.end())
                        need = FAIL_MARK;
                    else if (need != FAIL_MARK)
                        need = (need == UINT_MAX) ? it->second : std::max(need, it->second);
                }
                rhs_need_i[k] = need;
            }

            unsigned i = i0 + 1;
            unsigned j = j0 + 1;

            // Compute least fixpoint for (i, j): grow one side only when the
            // current prefix on the other side requires it.
            bool changed = true;
            while (changed) {
                changed = false;

                const unsigned req_j = lhs_need_j[i - 1];
                if (req_j == FAIL_MARK) {
                    i = lhs_toks.size();
                    break;
                }
                if (req_j != UINT_MAX && req_j + 1 > j) {
                    j = req_j + 1;
                    changed = true;
                }

                const unsigned req_i = rhs_need_i[j - 1];
                if (req_i == FAIL_MARK) {
                    j = rhs_toks.size();
                    break;
                }
                if (req_i != UINT_MAX && req_i + 1 > i) {
                    i = req_i + 1;
                    changed = true;
                }
            }

            if (i >= lhs_toks.size() || j >= rhs_toks.size())
                continue;

            // Decompose u = u1·u2 and v = v1·v2 at signature indices.
            euf::snode const* u1 = m_sg.drop_right(eq.m_lhs, lhs_toks.size() - i);
            euf::snode const* u2 = m_sg.drop_left(eq.m_lhs, i);
            euf::snode const* v1 = m_sg.drop_right(eq.m_rhs, rhs_toks.size() - j);
            euf::snode const* v2 = m_sg.drop_left(eq.m_rhs, j);
            // NSB review: if we keep this skolem function it should include arguments
            // to not clash with other values of i, j
            // Why not use
            // x := str.substr(u2, 0, str.len(u2) - str.len(v1)),
            const auto x_e = m_sk.mk("signature-split", eq.m_lhs->get_expr(), eq.m_rhs->get_expr(), eq.m_lhs->get_sort());
            euf::snode const* x = m_sg.mk(x_e);

            for (unsigned branch = 0; branch < 2; ++branch) {
                nielsen_node* child = mk_child(node);
                mk_edge(node, child, "signature split", true);

                auto& child_eqs = child->str_eqs();
                child_eqs[eq_idx] = child_eqs.back();
                child_eqs.pop_back();

                // Two-way split:
                // (1) u1·x = v1   and   u2 = x·v2
                // (2) u1 = v1·x   and   x·u2 = v2
                if (branch == 0) {
                    child_eqs.push_back(str_eq(m, m_sg.mk_concat(u1, x), v1, eq.m_dep));
                    child_eqs.push_back(str_eq(m, u2, m_sg.mk_concat(x, v2), eq.m_dep));
                }
                else {
                    child_eqs.push_back(str_eq(m, u1, m_sg.mk_concat(v1, x), eq.m_dep));
                    child_eqs.push_back(str_eq(m, m_sg.mk_concat(x, u2), v2, eq.m_dep));
                }
            }
            return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_power_split
    // For a variable x facing a power token u^n, branch:
    //   (1) x = u^m · prefix(u) with m < n (bounded power prefix)
    //   (2) x = u^n · x' (the variable extends past the full power)
    // Generates integer side constraints for the fresh exponent variables.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_power_split(nielsen_node* node) {

        euf::snode const* power = nullptr;
        euf::snode const* var_head = nullptr;
        str_eq const* eq = nullptr;
        bool fwd = true;
        if (!find_power_vs_var(node, power, var_head, eq, fwd))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode const* base = power->arg0();
        const expr_ref zero(a.mk_int(0), m);

        // Branch 1: enumerate all decompositions of the base.
        // x = base^m · prefix_i(base) where 0 <= m < n
        // Uses the same GetDecompose pattern as fire_gpower_intro.
        {
            euf::snode_vector base_toks;
            collect_tokens_dir(base, fwd, base_toks);
            const unsigned base_len = base_toks.size();
            expr* base_expr = get_power_base_expr(power, m_seq);
            if (!base_expr || base_len == 0)
                return false;

            const expr_ref fresh_m = get_or_create_gpower_n_var(var_head);
            const expr_ref power_m_expr(m_seq.str.mk_power(base_expr, fresh_m), m);
            euf::snode const* power_m_sn = m_sg.mk(power_m_expr);
            if (!power_m_sn)
                return false;

            for (unsigned i = 0; i < base_len; ++i) {
                euf::snode const* tok = base_toks[i];

                // Skip char position when preceding token is a power:
                // the power case at i-1 with 0 <= m' <= exp already covers m' = exp.
                if (!tok->is_power() && i > 0 && base_toks[i - 1]->is_power())
                    continue;

                // Build full-token prefix: base_toks[0..i-1]
                euf::snode const* prefix_sn = nullptr;
                for (unsigned j = 0; j < i; ++j)
                    prefix_sn = (j == 0) ? base_toks[0] : dir_concat(m_sg, prefix_sn, base_toks[j], fwd);

                euf::snode const* replacement;
                expr_ref fresh_inner_m(m);

                if (tok->is_power()) {
                    // Token is a power u^exp: decompose with fresh m', 0 <= m' <= exp
                    const expr * inner_exp = get_power_exponent(tok);
                    expr* inner_base = get_power_base_expr(tok, m_seq);
                    if (inner_exp && inner_base) {
                        fresh_inner_m = get_or_create_gpower_m_var(var_head);
                        expr_ref partial_pow(m_seq.str.mk_power(inner_base, fresh_inner_m), m);
                        euf::snode const* partial_sn = m_sg.mk(partial_pow);
                        euf::snode const* suffix_sn = prefix_sn ? dir_concat(m_sg, prefix_sn, partial_sn, fwd) : partial_sn;
                        replacement = dir_concat(m_sg, power_m_sn, suffix_sn, fwd);
                    }
                    else {
                        euf::snode const* suffix_sn = prefix_sn ? dir_concat(m_sg, prefix_sn, tok, fwd) : tok;
                        replacement = dir_concat(m_sg, power_m_sn, suffix_sn, fwd);
                    }
                }
                else
                    // Token is a char: P(char) = ε, suffix is just the prefix
                    replacement = prefix_sn ? dir_concat(m_sg, power_m_sn, prefix_sn, fwd) : power_m_sn;

                nielsen_node* child = mk_child(node);
                nielsen_edge* e = mk_edge(node, child, "power split", true);
                // deep check: the power bases in the replacement must not
                // contain var_head (collect_tokens is opaque to bases)
                SASSERT(!deep_contains_var(replacement, var_head));
                nielsen_subst s(var_head, replacement, eq->m_dep);
                e->add_subst(s);
                child->apply_subst(m_sg, s);

                // Side constraint: n >= 0
                e->add_side_constraint(mk_constraint(a.mk_ge(fresh_m, zero), eq->m_dep));

                // Side constraints for fresh partial exponent
                if (fresh_inner_m.get()) {
                    expr* inner_exp = get_power_exponent(tok);
                    // m' >= 0
                    e->add_side_constraint(mk_constraint(a.mk_ge(fresh_inner_m, zero), eq->m_dep));
                    // m' <= inner_exp
                    e->add_side_constraint(mk_constraint(a.mk_ge(inner_exp, fresh_inner_m), eq->m_dep));
                }
            }
        }

        // Branch 2: x = u^n · x' (variable extends past full power, non-progress).
        // The tail x' is the slice of x after the power.  The substitution must
        // be eliminating (x must not occur in its own replacement): reusing x as
        // its own tail would violate the nielsen_subst invariant AND the lazy
        // |x| = |replacement| edge constraint (add_subst_length_constraints)
        // would degenerate to n·|u| = 0, contradicting this branch's meaning
        // and dropping every model where x extends past a non-empty power.
        {
            euf::snode const* tail = get_tail(var_head, compute_length_expr(power).get(), fwd);
            euf::snode const* replacement = dir_concat(m_sg, power, tail, fwd);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, "power split", false);
            SASSERT(!deep_contains_var(replacement, var_head));
            const nielsen_subst s(var_head, replacement, eq->m_dep);
            e->add_subst(s);
            // |x'| >= 0, i.e. |x| >= n·|u| (the branch condition)
            e->add_side_constraint(mk_constraint(a.mk_ge(compute_length_expr(tail), a.mk_int(0)), eq->m_dep));
            child->apply_subst(m_sg, s);
        }

        return true;
    }

    // -----------------------------------------------------------------------
    // Modifier: apply_var_num_unwinding
    // For a power token u^n facing a variable, branch:
    //   (1) n = 0 → u^n = ε (replace power with empty)
    //   (2) n >= 1 → peel one u from the power
    // Generates integer side constraints for each branch.
    // -----------------------------------------------------------------------

    bool nielsen_graph::apply_var_num_unwinding_eq(nielsen_node* node) {

        euf::snode const* power = nullptr;
        euf::snode const* var_head = nullptr;
        str_eq const* eq = nullptr;
        bool fwd = true;
        if (!find_power_vs_var(node, power, var_head, eq, fwd))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode const* base = power->arg0();
        expr* exp_n = get_power_exponent(power);
        SASSERT(exp_n);
        const expr_ref zero(a.mk_int(0), m);
        const expr_ref one(a.mk_int(1), m);

        // Branch 1: n = 0 → replace u^n with ε (progress)
        // Side constraint: n = 0
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, "unwinding eq 0", true);
            const nielsen_subst s(power, m_sg.mk_empty_seq(power->get_sort()), eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            e->add_side_constraint(mk_constraint(a.mk_ge(exp_n, zero), eq->m_dep));
            e->add_side_constraint(mk_constraint(a.mk_le(exp_n, zero), eq->m_dep));
        }

        // Branch 2: n >= 1 → peel one u: u^n → u · u^(n-1)
        // Side constraint: n >= 1
        {
            const expr_ref power_expr(m_seq.str.mk_power(base->get_expr(), a.mk_sub(exp_n, a.mk_int(1))), m);
            euf::snode const* power_snode = m_sg.mk(power_expr);
            euf::snode const* replacement = dir_concat(m_sg, base, power_snode, fwd);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, "unwinding eq &gt;", false);
            SASSERT(!deep_contains_var(replacement, power));
            const nielsen_subst s(power, replacement, eq->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            e->add_side_constraint(mk_constraint(a.mk_ge(exp_n, one), eq->m_dep));
        }

        return true;
    }

    bool nielsen_graph::apply_var_num_unwinding_mem(nielsen_node* node) {

        euf::snode const* power = nullptr;
        str_mem const* mem = nullptr;
        bool fwd = true;
        if (!find_power_vs_var(node, power, mem, fwd))
            return false;

        SASSERT(power->is_power() && power->num_args() >= 1);
        euf::snode const* base = power->arg0();
        expr* exp_n = get_power_exponent(power);
        SASSERT(exp_n);
        const expr_ref zero(a.mk_int(0), m);
        const expr_ref one(a.mk_int(1), m);

        // Branch 1: n = 0 → replace u^n with ε (progress)
        // Side constraint: n = 0
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, "unwinding mem 0", true);
            const nielsen_subst s(power, m_sg.mk_empty_seq(power->get_sort()), mem->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            e->add_side_constraint(mk_constraint(a.mk_eq(exp_n, zero), mem->m_dep));
        }

        // Branch 2: n >= 1 → peel one u: u^n → u · u^(n-1)
        // Side constraint: n >= 1
        {
            const expr_ref power_expr(m_seq.str.mk_power(base->get_expr(), a.mk_sub(exp_n, a.mk_int(1))), m);
            euf::snode const* power_snode = m_sg.mk(power_expr);

            euf::snode const* replacement = dir_concat(m_sg, base, power_snode, fwd);
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, "unwinding mem &gt;", false);
            SASSERT(!deep_contains_var(replacement, power));
            const nielsen_subst s(power, replacement, mem->m_dep);
            e->add_subst(s);
            child->apply_subst(m_sg, s);
            e->add_side_constraint(mk_constraint(a.mk_ge(exp_n, one), mem->m_dep));
        }

        return true;
    }

    // Cf. axioms::diseq_axiom
    bool nielsen_graph::axiomatize_diseq(nielsen_node* node) {
        SASSERT(node->m_str_eq.empty() &&
                    std::ranges::all_of(node->m_str_mem, [](str_mem const& mem){ return mem.is_primitive(); }));

        if (node->m_str_deq.empty())
            return false;

        const str_deq& first = node->m_str_deq.back();
        euf::snode const* u = first.m_lhs;
        euf::snode const* v = first.m_rhs;

        const expr_ref u_len(compute_length_expr(u), m);
        const expr_ref v_len(compute_length_expr(v), m);
        expr_ref len_eq(m.mk_eq(u_len, v_len), m);
        sort *char_sort = nullptr;
        VERIFY(seq().is_seq(u->get_sort(), char_sort));
        euf::snode const* a = m_sg.mk(seq().str.mk_unit(m_sk.mk("diseq.a", u->get_expr(), v->get_expr(), char_sort).get()));
        euf::snode const* b = m_sg.mk(seq().str.mk_unit(m_sk.mk("diseq.b", u->get_expr(), v->get_expr(), char_sort).get()));
        euf::snode const* w = m_sg.mk(m_sk.mk("diseq.w", u->get_expr(), v->get_expr()).get());
        euf::snode const* up = m_sg.mk(m_sk.mk("diseq.u'", u->get_expr(), v->get_expr()).get());
        euf::snode const* vp = m_sg.mk(m_sk.mk("diseq.v'", u->get_expr(), v->get_expr()).get());
        const expr_ref up_len(compute_length_expr(up), m);
        const expr_ref vp_len(compute_length_expr(vp), m);
        euf::snode const* wau = dir_concat(m_sg, dir_concat(m_sg, w, a, true), up, true);
        euf::snode const* wbv = dir_concat(m_sg, dir_concat(m_sg, w, b, true), vp, true);
        str_eq u_eq(m, u, wau, first.m_dep);
        str_eq v_eq(m, v, wbv, first.m_dep);

        // Branch 1: |u| < |v|
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, "diseq I", true);
            child->m_str_deq.pop_back();
            expr_ref cmp(this->a.mk_lt(u_len, v_len), m);
            m_rw(cmp);
            e->add_side_constraint(constraint(cmp, first.m_dep, m));
        }
        // Branch 2: |v| < |u|
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, "diseq II", true);
            child->m_str_deq.pop_back();
            expr_ref cmp(this->a.mk_lt(v_len, u_len), m);
            m_rw(cmp);
            e->add_side_constraint(constraint(cmp, first.m_dep, m));
        }
        // Branch 3: u = wau' && v = wbv' && |u'| = |v'| && a != b
        {
            nielsen_node* child = mk_child(node);
            nielsen_edge* e = mk_edge(node, child, "diseq III", true);
            child->m_str_deq.pop_back();
            child->add_str_eq(u_eq);
            child->add_str_eq(v_eq);
            child->add_constraint(constraint(m.mk_eq(up_len, vp_len), first.m_dep, m));
            e->add_side_constraint(constraint(m.mk_not(m.mk_eq(a->get_expr(), b->get_expr())), first.m_dep, m));
        }

        return true;
    }
}
