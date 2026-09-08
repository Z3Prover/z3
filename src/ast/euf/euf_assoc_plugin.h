/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_assoc_plugin.h

Abstract:

    Completion plugin for associative functions.

--*/

#pragma once

#include <functional>
#include "ast/euf/euf_plugin.h"

namespace euf {

    class assoc_plugin : public plugin {
    public:
        using recognizer = std::function<bool(enode const*)>;

    private:
        using word = enode_vector;

        struct rule {
            word lhs;
            word rhs;
            justification j;
        };

        struct shared {
            enode* n;
            word w;
        };

        struct stats {
            unsigned m_num_rules = 0;
            unsigned m_num_superpositions = 0;
        };

        enum class undo_kind {
            is_queue_eq,
            is_register_shared,
            is_add_rule,
            is_push_scope
        };

        theory_id m_fid;
        recognizer m_is_assoc;
        recognizer m_is_variable;
        recognizer m_is_unit;
        justification::dependency_manager m_dep_manager;
        vector<rule> m_rules;
        vector<shared> m_shared;
        enode_pair_vector m_queued;
        bool_vector m_is_shared;
        svector<undo_kind> m_undo;
        unsigned_vector m_superposition_lim;
        unsigned m_num_superpositions = 0;
        unsigned m_queue_head = 0;
        unsigned m_completion_head = 0;
        unsigned m_max_rules = 64;
        unsigned m_max_superpositions = 256;
        unsigned m_max_word_size = 64;
        unsigned m_max_rewrite_steps = 1024;
        stats m_stats;
        std::function<void(void)> m_undo_notify;

        bool is_assoc(enode const* n) const { return m_is_assoc && m_is_assoc(n); }
        bool is_variable(enode const* n) const { return m_is_variable && m_is_variable(n); }
        bool is_unit(enode const* n) const { return m_is_unit && m_is_unit(n); }

        void push_undo(undo_kind k);
        void flatten(enode* n, word& w) const;
        bool equal(word const& a, word const& b) const;
        bool match(word const& w, unsigned offset, word const& pattern) const;
        int compare(word const& a, word const& b) const;
        bool orient(word& lhs, word& rhs) const;
        justification join(justification j1, justification j2);
        bool reduce(word& w, justification& j, rule const* except = nullptr);
        bool add_rule(word lhs, word rhs, justification j);
        void add_overlaps(rule const& r1, rule const& r2);
        void complete();
        void propagate_shared();

    public:
        assoc_plugin(egraph& g, theory_id fid);

        theory_id get_id() const override { return m_fid; }

        void register_associative(recognizer f) { m_is_assoc = std::move(f); }
        void register_variable(recognizer f) { m_is_variable = std::move(f); }
        void register_unit(recognizer f) { m_is_unit = std::move(f); }

        void set_completion_limits(unsigned max_rules, unsigned max_superpositions,
                                   unsigned max_word_size = 64, unsigned max_rewrite_steps = 1024);

        unsigned num_rules() const { return m_rules.size(); }

        void register_node(enode* n) override;
        void merge_eh(enode* n1, enode* n2) override;
        void undo() override;
        void push_scope_eh() override;
        void propagate() override;
        std::ostream& display(std::ostream& out) const override;
        void collect_statistics(statistics& st) const override;

        void set_undo(std::function<void(void)> u) { m_undo_notify = std::move(u); }
    };
}
