/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_assoc_plugin.cpp

Abstract:

    Completion plugin for associative functions.

--*/

#include "ast/euf/euf_assoc_plugin.h"
#include "ast/euf/euf_egraph.h"

namespace euf {

    assoc_plugin::assoc_plugin(egraph& g, theory_id fid):
        plugin(g),
        m_fid(fid),
        m_dep_manager(get_region()) {
    }

    void assoc_plugin::set_completion_limits(
        unsigned max_rules, unsigned max_superpositions,
        unsigned max_word_size, unsigned max_rewrite_steps) {
        m_max_rules = max_rules;
        m_max_superpositions = max_superpositions;
        m_max_word_size = max_word_size;
        m_max_rewrite_steps = max_rewrite_steps;
    }

    void assoc_plugin::push_undo(undo_kind k) {
        m_undo.push_back(k);
        push_plugin_undo(get_id());
        if (m_undo_notify)
            m_undo_notify();
    }

    void assoc_plugin::flatten(enode* n, word& w) const {
        if (is_assoc(n)) {
            for (auto* arg : enode_args(n))
                flatten(arg, w);
        }
        else {
            w.push_back(n);
        }
    }

    bool assoc_plugin::equal(word const& a, word const& b) const {
        if (a.size() != b.size())
            return false;
        for (unsigned i = 0; i < a.size(); ++i)
            if (a[i]->get_root() != b[i]->get_root())
                return false;
        return true;
    }

    bool assoc_plugin::match(word const& w, unsigned offset, word const& pattern) const {
        if (offset + pattern.size() > w.size())
            return false;
        for (unsigned i = 0; i < pattern.size(); ++i)
            if (w[offset + i]->get_root() != pattern[i]->get_root())
                return false;
        return true;
    }

    int assoc_plugin::compare(word const& a, word const& b) const {
        unsigned a_vars = 0, b_vars = 0, a_units = 0, b_units = 0;
        for (auto* n : a) {
            a_vars += is_variable(n);
            a_units += is_unit(n);
        }
        for (auto* n : b) {
            b_vars += is_variable(n);
            b_units += is_unit(n);
        }
        if (a_vars != b_vars)
            return a_vars > b_vars ? 1 : -1;
        if (a_units != b_units)
            return a_units > b_units ? 1 : -1;
        unsigned sz = std::min(a.size(), b.size());
        for (unsigned i = 0; i < sz; ++i) {
            unsigned ai = a[i]->get_root()->get_id();
            unsigned bi = b[i]->get_root()->get_id();
            if (ai != bi)
                return ai > bi ? 1 : -1;
        }
        if (a.size() == b.size())
            return 0;
        return a.size() > b.size() ? 1 : -1;
    }

    bool assoc_plugin::orient(word& lhs, word& rhs) const {
        int c = compare(lhs, rhs);
        if (c == 0)
            return false;
        if (c < 0)
            std::swap(lhs, rhs);
        return true;
    }

    justification assoc_plugin::join(justification j1, justification j2) {
        auto* d1 = m_dep_manager.mk_leaf(j1);
        auto* d2 = m_dep_manager.mk_leaf(j2);
        return justification::dependent(m_dep_manager.mk_join(d1, d2));
    }

    bool assoc_plugin::reduce(word& w, justification& j, rule const* except) {
        bool changed = false;
        unsigned steps = 0;
        while (steps++ < m_max_rewrite_steps) {
            bool reduced = false;
            for (auto const& r : m_rules) {
                if (&r == except || r.lhs.empty() || r.lhs.size() > w.size())
                    continue;
                for (unsigned i = 0; i + r.lhs.size() <= w.size(); ++i) {
                    if (!match(w, i, r.lhs))
                        continue;
                    word next;
                    next.append(i, w.data());
                    next.append(r.rhs);
                    next.append(w.size() - i - r.lhs.size(), w.data() + i + r.lhs.size());
                    w.swap(next);
                    j = join(j, r.j);
                    changed = reduced = true;
                    break;
                }
                if (reduced)
                    break;
            }
            if (!reduced)
                break;
        }
        return changed;
    }

    bool assoc_plugin::add_rule(word lhs, word rhs, justification j) {
        reduce(lhs, j);
        reduce(rhs, j);
        if (!orient(lhs, rhs) || lhs.empty() || lhs.size() > m_max_word_size || rhs.size() > m_max_word_size)
            return false;
        for (auto const& r : m_rules)
            if (equal(lhs, r.lhs) && equal(rhs, r.rhs))
                return false;
        if (m_rules.size() >= m_max_rules)
            return false;
        m_rules.push_back({ std::move(lhs), std::move(rhs), j });
        ++m_stats.m_num_rules;
        push_undo(undo_kind::is_add_rule);
        return true;
    }

    void assoc_plugin::add_overlaps(rule const& r1, rule const& r2) {
        word lhs1(r1.lhs), rhs1(r1.rhs), lhs2(r2.lhs), rhs2(r2.rhs);
        justification j1 = r1.j, j2 = r2.j;
        int n1 = static_cast<int>(lhs1.size());
        int n2 = static_cast<int>(lhs2.size());
        for (int offset = 1 - n2; offset < n1; ++offset) {
            if (m_stats.m_num_superpositions >= m_max_superpositions)
                return;
            int begin = std::max(0, offset);
            int end = std::min(n1, offset + n2);
            bool overlaps = begin < end;
            for (int i = begin; overlaps && i < end; ++i)
                overlaps = lhs1[i]->get_root() == lhs2[i - offset]->get_root();
            if (!overlaps)
                continue;
            ++m_stats.m_num_superpositions;
            int first = std::min(0, offset);
            int last = std::max(n1, offset + n2);
            word left, right;
            for (int i = first; i < 0; ++i)
                left.push_back(lhs2[i - offset]);
            left.append(rhs1);
            for (int i = n1; i < last; ++i)
                left.push_back(lhs2[i - offset]);
            for (int i = first; i < offset; ++i)
                right.push_back(lhs1[i]);
            right.append(rhs2);
            for (int i = offset + n2; i < last; ++i)
                right.push_back(lhs1[i]);
            add_rule(std::move(left), std::move(right), join(j1, j2));
        }
    }

    void assoc_plugin::complete() {
        while (m_completion_head < m_rules.size() &&
               m_stats.m_num_superpositions < m_max_superpositions) {
            unsigned i = m_completion_head++;
            for (unsigned j = 0; j <= i && m_stats.m_num_superpositions < m_max_superpositions; ++j)
                add_overlaps(m_rules[i], m_rules[j]);
        }
    }

    void assoc_plugin::register_node(enode* n) {
        if ((!is_assoc(n) && !is_variable(n) && !is_unit(n)) ||
            m_is_shared.get(n->get_id(), false))
            return;
        word w;
        flatten(n, w);
        m_is_shared.reserve(n->get_id() + 1, false);
        m_is_shared[n->get_id()] = true;
        m_shared.push_back({ n, std::move(w) });
        push_undo(undo_kind::is_register_shared);
    }

    void assoc_plugin::merge_eh(enode* n1, enode* n2) {
        if (n1 == n2)
            return;
        m_queued.push_back({ n1, n2 });
        push_undo(undo_kind::is_queue_eq);
    }

    void assoc_plugin::push_scope_eh() {
        push_undo(undo_kind::is_push_scope);
    }

    void assoc_plugin::undo() {
        undo_kind k = m_undo.back();
        m_undo.pop_back();
        switch (k) {
        case undo_kind::is_queue_eq:
            m_queued.pop_back();
            m_queue_head = std::min(m_queue_head, m_queued.size());
            break;
        case undo_kind::is_register_shared: {
            auto const& s = m_shared.back();
            m_is_shared[s.n->get_id()] = false;
            m_shared.pop_back();
            break;
        }
        case undo_kind::is_add_rule:
            m_rules.pop_back();
            m_completion_head = std::min(m_completion_head, m_rules.size());
            break;
        case undo_kind::is_push_scope:
            break;
        }
    }

    void assoc_plugin::propagate_shared() {
        for (unsigned i = 0; i < m_shared.size(); ++i) {
            word wi(m_shared[i].w);
            justification ji = justification::axiom(get_id());
            reduce(wi, ji);
            for (unsigned j = 0; j < i; ++j) {
                word wj(m_shared[j].w);
                justification jj = justification::axiom(get_id());
                reduce(wj, jj);
                if (equal(wi, wj))
                    push_merge(m_shared[i].n, m_shared[j].n, join(ji, jj));
            }
        }
    }

    void assoc_plugin::propagate() {
        while (m_queue_head < m_queued.size()) {
            auto [lhs, rhs] = m_queued[m_queue_head++];
            word l, r;
            flatten(lhs, l);
            flatten(rhs, r);
            add_rule(std::move(l), std::move(r), justification::equality(lhs, rhs));
        }
        complete();
        propagate_shared();
    }

    std::ostream& assoc_plugin::display(std::ostream& out) const {
        for (auto const& r : m_rules) {
            for (auto* n : r.lhs)
                out << n->get_root()->get_id() << " ";
            out << "-> ";
            for (auto* n : r.rhs)
                out << n->get_root()->get_id() << " ";
            out << "\n";
        }
        return out;
    }

    void assoc_plugin::collect_statistics(statistics& st) const {
        st.update("assoc rules", m_stats.m_num_rules);
        st.update("assoc superpositions", m_stats.m_num_superpositions);
    }
}
