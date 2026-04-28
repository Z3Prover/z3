/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_seq_plugin.cpp

Abstract:

    Plugin structure for sequences/strings.

    Merges equivalence classes taking into account associativity
    of concatenation and algebraic properties of strings and
    regular expressions.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/

#include "ast/euf/euf_seq_plugin.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_sgraph.h"
#include "ast/ast_pp.h"

namespace euf {

    // Check if enode is any kind of concat (str.++ or re.++)
    static bool is_any_concat(enode* n, seq_util const& seq) {
        expr* a = nullptr, *b = nullptr;
        return seq.str.is_concat(n->get_expr(), a, b) || seq.re.is_concat(n->get_expr(), a, b);
    }

    // Collect leaves of a concat tree in left-to-right order.
    // For non-concat nodes, the node itself is a leaf.
    // Handles both str.++ and re.++.
    static void collect_enode_leaves(enode* n, seq_util const& seq, enode_vector& leaves) {
        if (is_any_concat(n, seq)) {
            collect_enode_leaves(n->get_arg(0), seq, leaves);
            collect_enode_leaves(n->get_arg(1), seq, leaves);
        }
        else {
            leaves.push_back(n);
        }
    }

    unsigned enode_concat_hash::operator()(enode* n) const {
        snode* sn = sg.find(n->get_expr());
        if (sn && sn->has_cached_hash())
            return sn->assoc_hash();
        if (!is_any_concat(n, seq))
            return n->get_id();
        enode_vector leaves;
        collect_enode_leaves(n, seq, leaves);
        unsigned h = 0;
        for (enode* l : leaves)
            h = combine_hash(h, l->get_id());
        return h;
    }

    bool enode_concat_eq::operator()(enode* a, enode* b) const {
        if (a == b) return true;
        if (!is_any_concat(a, seq) || !is_any_concat(b, seq))
            return false;
        enode_vector la, lb;
        collect_enode_leaves(a, seq, la);
        collect_enode_leaves(b, seq, lb);
        if (la.size() != lb.size())
            return false;
        for (unsigned i = 0; i < la.size(); ++i)
            if (la[i] != lb[i])
                return false;
        return true;
    }

    seq_plugin::seq_plugin(egraph& g, sgraph* sg):
        plugin(g),
        m_seq(g.get_manager()),
        m_rewriter(g.get_manager()),
        m_sg(sg ? *sg : *alloc(sgraph, g.get_manager(), g, false)),
        m_sg_owned(sg == nullptr),
        m_concat_hash(m_seq, m_sg),
        m_concat_eq(m_seq),
        m_concat_table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, m_concat_hash, m_concat_eq) {
    }

    seq_plugin::~seq_plugin() {
        if (m_sg_owned)
            dealloc(&m_sg);
    }

    void seq_plugin::register_node(enode* n) {
        m_queue.push_back(n);
        push_undo(undo_kind::undo_add_concat);
    }

    void seq_plugin::merge_eh(enode* n1, enode* n2) {
        m_queue.push_back(enode_pair(n1, n2));
        push_undo(undo_kind::undo_add_concat);
    }

    void seq_plugin::push_undo(undo_kind k) {
        m_undo.push_back(k);
        push_plugin_undo(get_id());
    }

    void seq_plugin::propagate() {
        if (m_qhead == m_queue.size())
            return;
        for (; m_qhead < m_queue.size(); ++m_qhead) {
            if (g.inconsistent())
                break;
            if (std::holds_alternative<enode*>(m_queue[m_qhead])) {
                auto n = std::get<enode*>(m_queue[m_qhead]);
                propagate_register_node(n);
            }
            else {
                auto [a, b] = std::get<enode_pair>(m_queue[m_qhead]);
                propagate_merge(a, b);
            }
        }
    }

    void seq_plugin::propagate_register_node(enode* n) {
        if (!m_seq.is_seq(n->get_expr()) && !m_seq.is_re(n->get_expr()))
            return;

        TRACE(seq, tout << "seq register " << g.bpp(n) << "\n");

        if (is_concat(n)) {
            propagate_assoc(n);
            propagate_simplify(n);
        }

        // str.++ identity: concat(a, ε) = a, concat(ε, b) = b
        enode* a, *b;
        if (is_str_concat(n, a, b)) {
            if (is_str_empty(a))
                push_merge(n, b);
            else if (is_str_empty(b))
                push_merge(n, a);
        }

        // re.++ identity: concat(a, epsilon) = a, concat(epsilon, b) = b
        // re.++ absorption: concat(a, ∅) = ∅, concat(∅, b) = ∅
        if (is_re_concat(n, a, b)) {
            if (is_re_epsilon(a))
                push_merge(n, b);
            else if (is_re_epsilon(b))
                push_merge(n, a);
            else if (is_re_empty(a))
                push_merge(n, a);
            else if (is_re_empty(b))
                push_merge(n, b);
        }
    }

    void seq_plugin::propagate_merge(enode* a, enode* b) {
        if (!m_seq.is_seq(a->get_expr()) && !m_seq.is_re(a->get_expr()))
            return;

        TRACE(seq, tout << "seq merge " << g.bpp(a) << " == " << g.bpp(b) << "\n");

        // when equivalence classes merge, re-check concat simplifications
        for (enode* n : enode_class(a)) {
            if (is_concat(n))
                propagate_simplify(n);
        }

        // Re-apply identity and absorption rules over all tracked concat nodes.
        // This handles the case where the merge caused a child to become equivalent
        // to an identity (ε) or absorbing element (∅) that was not known at
        // registration time (e.g. b ~ "" discovered after concat(x, b) was registered).
        for (enode* n : m_concats) {
            enode *na, *nb;
            if (is_str_concat(n, na, nb)) {
                if (is_str_empty(na))
                    push_merge(n, nb);
                else if (is_str_empty(nb))
                    push_merge(n, na);
            }
            if (is_re_concat(n, na, nb)) {
                if (is_re_epsilon(na))
                    push_merge(n, nb);
                else if (is_re_epsilon(nb))
                    push_merge(n, na);
                else if (is_re_empty(na))
                    push_merge(n, na);   // absorb: concat(∅, b) = ∅
                else if (is_re_empty(nb))
                    push_merge(n, nb);   // absorb: concat(a, ∅) = ∅
            }
        }
    }

    //
    // Concat associativity:
    // Instead of creating new expressions, maintain a hash table
    // that respects associativity. When a concat is registered,
    // look up existing concats with the same leaf sequence.
    // If found, merge the existing node with the new one.
    //
    void seq_plugin::propagate_assoc(enode* n) {
        if (!is_concat(n))
            return;

        enode* existing = nullptr;
        if (m_concat_table.find(n, existing)) {
            if (existing != n)
                push_merge(n, existing);
        }
        else {
            m_concat_table.insert(n);
            m_concats.push_back(n);
            push_undo(undo_kind::undo_add_to_table);
        }
    }

    //
    // Concat simplification rules from ZIPT:
    //
    // 1. Kleene star merging: concat(u, v*, v*, w) = concat(u, v*, w)
    //    when adjacent children in a concat chain have congruent star bodies.
    //
    // 2. Nullable absorption: concat(u, .*, v, w) = concat(u, .*, w)
    //    when v is nullable and adjacent to full_seq (.*).
    //
    // 3. Loop merging: concat(body{lo1,hi1}, body{lo2,hi2}) = body{lo1+lo2, hi1+hi2}
    //    when both children are loops over congruent bodies.
    //
    void seq_plugin::propagate_simplify(enode* n) {
        enode* a, *b;
        if (!is_concat(n, a, b))
            return;

        // Rule 1: Kleene star merging
        // concat(v*, v*) = v*
        if (same_star_body(a, b))
            push_merge(n, a);

        // Rule 1 extended (right): concat(v*, concat(v*, c)) = concat(v*, c)
        enode* b1, *b2;
        if (is_concat(b, b1, b2) && same_star_body(a, b1))
            push_merge(n, b);

        // Rule 1 extended (left): concat(concat(c, v*), v*) = concat(c, v*)
        enode* a1, *a2;
        if (is_concat(a, a1, a2) && same_star_body(a2, b))
            push_merge(n, a);

        // Rule 2: Nullable absorption by .*
        // concat(.*, v) = .* when v is nullable
        if (is_full_seq(a) && is_nullable(b))
            push_merge(n, a);

        // concat(v, .*) = .* when v is nullable
        if (is_nullable(a) && is_full_seq(b))
            push_merge(n, b);

        // concat(.*, concat(v, w)) = concat(.*, w) when v nullable
        // handled by associativity + nullable absorption on sub-concats

        // concat(concat(u, v), .*) = concat(u, .*) when v nullable
        // handled by associativity + nullable absorption on sub-concats

        // Rule 3: Loop merging
        // concat(body{lo1,hi1}, body{lo2,hi2}) = body{lo1+lo2, hi1+hi2}
        unsigned lo1, hi1, lo2, hi2;
        if (same_loop_body(a, b, lo1, hi1, lo2, hi2)) {
            ast_manager& m_ast = g.get_manager();
            enode* body_en = a->get_arg(0);
            unsigned lo = lo1 + lo2, hi = hi1 + hi2;
            expr_ref merged_expr(m_seq.re.mk_loop_proper(body_en->get_expr(), lo, hi), m_ast);
            enode* merged_n = g.find(merged_expr);
            if (!merged_n && is_app(merged_expr)) {
                app* merged_app = to_app(merged_expr);
                unsigned nargs = merged_app->get_num_args();
                // mk_loop_proper always produces 0-arg (impossible) or 1-arg results:
                //   - proper loop: 1 arg (the body)
                //   - epsilon (lo+hi==0 degenerate): 1 arg (the empty string)
                //   - body itself (lo=1,hi=1 degenerate): handled by g.find above
                if (nargs == 0) {
                    merged_n = mk(merged_expr, 0, nullptr);
                } else if (nargs == 1) {
                    // The single arg is either body_en or the empty string (epsilon case).
                    // If the empty string is not yet in the graph, skip the merge.
                    expr* arg0_expr = merged_app->get_arg(0);
                    enode* arg0_en = (arg0_expr == body_en->get_expr()) ? body_en : g.find(arg0_expr);
                    if (arg0_en)
                        merged_n = mk(merged_expr, 1, &arg0_en);
                } else {
                    SASSERT(false && "mk_loop_proper should not produce multi-argument expressions");
                }
            }
            if (merged_n)
                push_merge(n, merged_n);
        }
    }

    bool seq_plugin::is_nullable(expr* e) {
        expr_ref result = m_rewriter.is_nullable(e);
        return g.get_manager().is_true(result);
    }

    bool seq_plugin::same_star_body(enode* a, enode* b) {
        if (!is_star(a) || !is_star(b))
            return false;
        // re.star(x) and re.star(y) have congruent bodies if x ~ y
        return a->get_arg(0)->get_root() == b->get_arg(0)->get_root();
    }

    bool seq_plugin::same_loop_body(enode* a, enode* b,
                                    unsigned& lo1, unsigned& hi1,
                                    unsigned& lo2, unsigned& hi2) {
        if (!is_loop(a) || !is_loop(b))
            return false;
        expr* body_a, *body_b;
        if (!m_seq.re.is_loop(a->get_expr(), body_a, lo1, hi1))
            return false;
        if (!m_seq.re.is_loop(b->get_expr(), body_b, lo2, hi2))
            return false;
        enode* na = g.find(body_a);
        enode* nb = g.find(body_b);
        if (!na || !nb)
            return false;
        return na->get_root() == nb->get_root();
    }

    void seq_plugin::undo() {
        auto k = m_undo.back();
        m_undo.pop_back();
        switch (k) {
        case undo_kind::undo_add_concat:
            SASSERT(!m_queue.empty());
            m_queue.pop_back();
            if (m_qhead > m_queue.size())
                m_qhead = m_queue.size();
            break;
        case undo_kind::undo_add_to_table:
            SASSERT(!m_concats.empty());
            m_concat_table.remove(m_concats.back());
            m_concats.pop_back();
            break;
        }
    }

    std::ostream& seq_plugin::display(std::ostream& out) const {
        out << "seq-plugin\n";
        return out;
    }

    void seq_plugin::collect_statistics(statistics& st) const {
        // statistics are collected by sgraph which owns us
    }
}
