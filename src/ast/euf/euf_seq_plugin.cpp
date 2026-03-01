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

    Nikolaj Bjorner (nbjorner) 2026-03-01
    Clemens Eisenhofer 2026-03-01

--*/

#include "ast/euf/euf_seq_plugin.h"
#include "ast/euf/euf_sgraph.h"
#include "ast/euf/euf_egraph.h"
#include "ast/ast_pp.h"

namespace euf {

    seq_plugin::seq_plugin(egraph& g, sgraph& sg):
        plugin(g),
        m_seq(g.get_manager()),
        m_sg(sg) {
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
                auto n = *std::get_if<enode*>(&m_queue[m_qhead]);
                propagate_register_node(n);
            }
            else {
                auto [a, b] = *std::get_if<enode_pair>(&m_queue[m_qhead]);
                propagate_merge(a, b);
            }
        }
    }

    void seq_plugin::propagate_register_node(enode* n) {
        if (!m_seq.is_seq(n->get_expr()) && !m_seq.is_re(n->get_expr()))
            return;

        TRACE(seq, tout << "seq register " << g.bpp(n) << "\n");

        // register in sgraph
        m_sg.mk(n->get_expr());

        if (is_concat(n)) {
            m_concats.push_back(n);
            propagate_assoc(n);
            propagate_simplify(n);
        }

        // n-ary concat: concat(a, b, c) => concat(a, concat(b, c))
        if (is_concat(n) && n->num_args() > 2) {
            auto last = n->get_arg(n->num_args() - 1);
            for (unsigned i = n->num_args() - 1; i-- > 0; )
                last = mk_concat(n->get_arg(i), last);
            push_merge(last, n);
        }

        // empty concat: concat(a, empty) = a, concat(empty, b) = b
        enode* a, *b;
        if (is_concat(n, a, b)) {
            if (is_empty(a))
                push_merge(n, b);
            else if (is_empty(b))
                push_merge(n, a);
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
    }

    //
    // Concat associativity:
    // concat(concat(a, b), c) = concat(a, concat(b, c))
    //
    // This normalizes to right-associated form.
    //
    void seq_plugin::propagate_assoc(enode* n) {
        enode* a, *b;
        if (!is_concat(n, a, b))
            return;

        enode* a1, *a2;
        if (is_concat(a, a1, a2)) {
            // concat(concat(a1, a2), b) => concat(a1, concat(a2, b))
            enode* inner = mk_concat(a2, b);
            enode* outer = mk_concat(a1, inner);
            push_merge(outer, n);
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
    void seq_plugin::propagate_simplify(enode* n) {
        enode* a, *b;
        if (!is_concat(n, a, b))
            return;

        // Rule 1: Kleene star merging
        // concat(v*, v*) = v*
        if (same_star_body(a, b))
            push_merge(n, a);

        // Rule 1 extended: concat(v*, concat(v*, c)) = concat(v*, c)
        enode* b1, *b2;
        if (is_concat(b, b1, b2) && same_star_body(a, b1))
            push_merge(n, b);

        // Rule 2: Nullable absorption by .*
        // concat(.*, v) = .* when v is nullable
        if (is_full_seq(a) && is_nullable(b))
            push_merge(n, a);

        // concat(v, .*) = .* when v is nullable
        if (is_nullable(a) && is_full_seq(b))
            push_merge(n, b);

        // concat(.*, concat(v, w)) = concat(.*, w) when v nullable
        if (is_full_seq(a) && is_concat(b, b1, b2) && is_nullable(b1)) {
            enode* simplified = mk_concat(a, b2);
            push_merge(n, simplified);
        }

        // concat(concat(u, v), .*) = concat(u, .*) when v nullable
        enode* a1, *a2;
        if (is_concat(a, a1, a2) && is_nullable(a2) && is_full_seq(b)) {
            enode* simplified = mk_concat(a1, b);
            push_merge(n, simplified);
        }
    }

    bool seq_plugin::is_nullable(enode* n) {
        snode* s = m_sg.find(n->get_expr());
        if (s)
            return s->is_nullable();
        // empty string is nullable
        if (is_empty(n))
            return true;
        return false;
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

    enode* seq_plugin::mk_concat(enode* a, enode* b) {
        expr* e = m_seq.str.mk_concat(a->get_expr(), b->get_expr());
        enode* args[2] = { a, b };
        return mk(e, 2, args);
    }

    enode* seq_plugin::mk_empty(sort* s) {
        expr* e = m_seq.str.mk_empty(s);
        return mk(e, 0, nullptr);
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
        }
    }

    std::ostream& seq_plugin::display(std::ostream& out) const {
        // sgraph contents are displayed by sgraph::display, not here,
        // since sgraph owns the seq_plugin (not the other way around)
        out << "seq-plugin\n";
        return out;
    }

    void seq_plugin::collect_statistics(statistics& st) const {
        // statistics are collected by sgraph which owns us
    }
}
