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

    The plugin integrates with euf_egraph for congruence closure.
    Node registration in sgraph is handled by sgraph itself via
    the egraph's on_make callback, not by the plugin.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/

#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/euf/euf_plugin.h"
#include "util/hashtable.h"

namespace euf {

    class egraph;
    class sgraph;

    // Associativity-respecting hash for enode concat trees.
    // Uses cached snode hash matrices from the sgraph for O(1) hashing.
    // Handles both str.++ (OP_SEQ_CONCAT) and re.++ (OP_RE_CONCAT).
    struct enode_concat_hash {
        seq_util const& seq;
        sgraph& sg;
        enode_concat_hash(seq_util const& s, sgraph& sg) : seq(s), sg(sg) {}
        unsigned operator()(enode* n) const;
    };

    // Associativity-respecting equality for enode concat trees.
    // Handles both str.++ (OP_SEQ_CONCAT) and re.++ (OP_RE_CONCAT).
    struct enode_concat_eq {
        seq_util const& seq;
        enode_concat_eq(seq_util const& s) : seq(s) {}
        bool operator()(enode* a, enode* b) const;
    };

    class seq_plugin : public plugin {

        enum class undo_kind {
            undo_add_concat,
            undo_add_to_table,
        };

        seq_util         m_seq;
        seq_rewriter     m_rewriter;
        sgraph&          m_sg;
        bool             m_sg_owned = false; // whether we own the sgraph
        svector<undo_kind> m_undo;

        // queue of merges and registrations to process
        vector<std::variant<enode*, enode_pair>> m_queue;
        unsigned         m_qhead = 0;

        // track registered concat nodes for simplification
        enode_vector     m_concats;

        // associativity-respecting hash table for concat nodes
        enode_concat_hash m_concat_hash;
        enode_concat_eq   m_concat_eq;
        hashtable<enode*, enode_concat_hash, enode_concat_eq> m_concat_table;

        // string concat predicates
        bool is_str_concat(enode* n) const { return m_seq.str.is_concat(n->get_expr()); }
        bool is_str_concat(enode* n, enode*& a, enode*& b) {
            expr* ea = nullptr, *eb = nullptr;
            return m_seq.str.is_concat(n->get_expr(), ea, eb) &&
                   n->num_args() == 2 &&
                   (a = n->get_arg(0), b = n->get_arg(1), true);
        }

        // regex concat predicates
        bool is_re_concat(enode* n) const { return m_seq.re.is_concat(n->get_expr()); }
        bool is_re_concat(enode* n, enode*& a, enode*& b) {
            expr* ea = nullptr, *eb = nullptr;
            return m_seq.re.is_concat(n->get_expr(), ea, eb) &&
                   n->num_args() == 2 &&
                   (a = n->get_arg(0), b = n->get_arg(1), true);
        }

        // any concat, string or regex
        bool is_concat(enode* n) const { return is_str_concat(n) || is_re_concat(n); }
        bool is_concat(enode* n, enode*& a, enode*& b) {
            return is_str_concat(n, a, b) || is_re_concat(n, a, b);
        }

        bool is_star(enode* n) const { return m_seq.re.is_star(n->get_expr()); }
        bool is_loop(enode* n) const { return m_seq.re.is_loop(n->get_expr()); }

        // string empty: ε for str.++
        // Follows the union-find root so that merges are correctly reflected.
        bool is_str_empty(enode* n) const { return m_seq.str.is_empty(n->get_root()->get_expr()); }
        // regex empty set: ∅ for re.++ (absorbing element)
        // Follows the union-find root so that merges are correctly reflected.
        bool is_re_empty(enode* n) const { return m_seq.re.is_empty(n->get_root()->get_expr()); }
        // regex epsilon: to_re("") for re.++ (identity element)
        // Follows the union-find root so that merges are correctly reflected.
        bool is_re_epsilon(enode* n) const { return m_seq.re.is_epsilon(n->get_root()->get_expr()); }

        bool is_to_re(enode* n) const { return m_seq.re.is_to_re(n->get_expr()); }
        bool is_full_seq(enode* n) const { return m_seq.re.is_full_seq(n->get_expr()); }

        void push_undo(undo_kind k);

        void propagate_register_node(enode* n);
        void propagate_merge(enode* a, enode* b);

        // concat associativity: maintain hash table of concat nodes,
        // merge nodes that are equal modulo associativity
        void propagate_assoc(enode* n);

        // concat simplification:
        // merging Kleene stars, merging loops, absorbing nullables
        void propagate_simplify(enode* n);

        // check if expression is nullable using existing seq_rewriter
        bool is_nullable(expr* e);
        bool is_nullable(enode* n) { return is_nullable(n->get_expr()); }

        // check if two enodes have congruent star bodies
        bool same_star_body(enode* a, enode* b);

        // check if two enodes have congruent loop bodies and extract bounds
        bool same_loop_body(enode* a, enode* b, unsigned& lo1, unsigned& hi1, unsigned& lo2, unsigned& hi2);

    public:
        seq_plugin(egraph& g, sgraph* sg = nullptr);
        ~seq_plugin() override;

        theory_id get_id() const override { return m_seq.get_family_id(); }

        void register_node(enode* n) override;

        void merge_eh(enode* n1, enode* n2) override;

        void diseq_eh(enode*) override {}

        void propagate() override;

        void undo() override;

        std::ostream& display(std::ostream& out) const override;

        void collect_statistics(statistics& st) const override;
    };
}
