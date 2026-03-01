/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_seq_plugin.h

Abstract:

    Plugin structure for sequences/strings.

    Merges equivalence classes taking into account associativity
    of concatenation and algebraic properties of strings and
    regular expressions. Implements features from ZIPT:

    -- Concat associativity: str.++ is associative, so
       concat(a, concat(b, c)) = concat(concat(a, b), c).
       Handled via an AC-style plugin for the concat operator.

    -- Kleene star merging: adjacent identical Kleene stars
       in a concatenation are collapsed, u.v*.v*.w = u.v*.w

    -- Loop merging: adjacent loops over the same body are
       merged, v{l1,h1}.v{l2,h2} = v{l1+l2,h1+h2}

    -- Nullable absorption: a nullable token adjacent to .*
       is absorbed, u.*.v.w = u.*.w when v is nullable.

    The plugin integrates with euf_egraph for congruence closure
    and with sgraph for snode-based string representation.

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-01
    Clemens Eisenhofer 2026-03-01

--*/

#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/euf/euf_plugin.h"
#include "ast/euf/euf_sgraph.h"

namespace euf {

    class egraph;

    class seq_plugin : public plugin {

        enum class undo_kind {
            undo_add_concat,
            undo_push_scope
        };

        seq_util         m_seq;
        sgraph           m_sg;
        svector<undo_kind> m_undo;

        // queue of merges and registrations to process
        vector<std::variant<enode*, enode_pair>> m_queue;
        unsigned         m_qhead = 0;

        // track registered concat nodes for simplification
        enode_vector     m_concats;

        bool is_concat(enode* n) const { return m_seq.str.is_concat(n->get_expr()); }
        bool is_concat(enode* n, enode*& a, enode*& b) {
            return is_concat(n) && n->num_args() == 2 &&
                   (a = n->get_arg(0), b = n->get_arg(1), true);
        }
        bool is_star(enode* n) const { return m_seq.re.is_star(n->get_expr()); }
        bool is_loop(enode* n) const { return m_seq.re.is_loop(n->get_expr()); }
        bool is_empty(enode* n) const { return m_seq.str.is_empty(n->get_expr()); }
        bool is_to_re(enode* n) const { return m_seq.re.is_to_re(n->get_expr()); }
        bool is_full_seq(enode* n) const { return m_seq.re.is_full_seq(n->get_expr()); }

        enode* mk_concat(enode* a, enode* b);
        enode* mk_empty(sort* s);

        void push_undo(undo_kind k);

        void propagate_register_node(enode* n);
        void propagate_merge(enode* a, enode* b);

        // concat associativity: ensure right-associated normal form
        // concat(concat(a, b), c) = concat(a, concat(b, c))
        void propagate_assoc(enode* n);

        // concat simplification:
        // merging Kleene stars, merging loops, absorbing nullables
        void propagate_simplify(enode* n);

        // check if snode is nullable via sgraph metadata
        bool is_nullable(enode* n);

        // check if two enodes have congruent star bodies
        bool same_star_body(enode* a, enode* b);

        // check if two enodes have congruent loop bodies and extract bounds
        bool same_loop_body(enode* a, enode* b, unsigned& lo1, unsigned& hi1, unsigned& lo2, unsigned& hi2);

    public:
        seq_plugin(egraph& g);

        theory_id get_id() const override { return m_seq.get_family_id(); }

        void register_node(enode* n) override;

        void merge_eh(enode* n1, enode* n2) override;

        void diseq_eh(enode*) override {}

        void propagate() override;

        void undo() override;

        void push_scope_eh() override;

        std::ostream& display(std::ostream& out) const override;

        void collect_statistics(statistics& st) const override;

        sgraph& get_sgraph() { return m_sg; }
        sgraph const& get_sgraph() const { return m_sg; }
    };
}
