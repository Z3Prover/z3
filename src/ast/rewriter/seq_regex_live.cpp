/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex_live.cpp

Abstract:

    Shared lazy live-state traversal for regular-expression derivatives.

--*/

#include "ast/rewriter/seq_regex_live.h"
#include "ast/rewriter/seq_rewriter.h"
#include "util/obj_hashtable.h"
#include "util/uint_set.h"

namespace seq {

    struct live_states::search {
        svector<unsigned> m_to_explore;
        unsigned m_explore_head = 0;
        uint_set m_seen;
        vector<svector<unsigned>> m_predecessors;
        bool_vector m_live;
        svector<unsigned> m_live_frontier;
        unsigned m_root_id = 0;
        failure m_failure = failure::none;
        bool m_complete = false;
    };

    struct live_states::imp {
        seq_rewriter& m_rw;
        ast_manager& m;
        seq_util::rex& m_re;
        transition_mode m_mode;
        unsigned m_max_states;
        obj_map<expr, unsigned> m_ids;
        expr_ref_vector m_states;
        vector<svector<unsigned>> m_successors;
        svector<char> m_nullable;
        bool_vector m_expanded;
        obj_map<expr, search*> m_searches;

        imp(seq_rewriter& rw, transition_mode mode, unsigned max_states) :
            m_rw(rw),
            m(rw.m()),
            m_re(rw.u().re),
            m_mode(mode),
            m_max_states(max_states),
            m_states(m) {
        }

        ~imp() {
            reset();
        }

        unsigned intern(expr* r) {
            unsigned id = 0;
            if (m_ids.find(r, id))
                return id;
            id = m_states.size();
            m_ids.insert(r, id);
            m_states.push_back(r);
            m_successors.push_back(svector<unsigned>());
            m_nullable.push_back(2);
            m_expanded.push_back(false);
            return id;
        }

        void resize(search& s) {
            unsigned size = m_states.size();
            if (s.m_predecessors.size() < size)
                s.m_predecessors.resize(size);
            if (s.m_live.size() < size)
                s.m_live.resize(size, false);
        }

        char nullable(unsigned id) {
            if (m_nullable[id] != 2)
                return m_nullable[id];
            expr* r = m_states.get(id);
            lbool n = m_re.get_info(r).nullable;
            if (n == l_undef) {
                expr_ref f = m_rw.is_nullable(r);
                n = m.is_true(f) ? l_true : m.is_false(f) ? l_false : l_undef;
            }
            if (n == l_true) m_nullable[id] = 1;
            else if (n == l_false) m_nullable[id] = 0;
            else m_nullable[id] = 3;
            return m_nullable[id];
        }

        void mark_live(search& s, unsigned id) {
            svector<unsigned> todo;
            todo.push_back(id);
            while (!todo.empty()) {
                id = todo.back();
                todo.pop_back();
                if (!s.m_seen.contains(id) || s.m_live[id])
                    continue;
                s.m_live[id] = true;
                s.m_live_frontier.push_back(id);
                for (unsigned predecessor : s.m_predecessors[id])
                    todo.push_back(predecessor);
            }
        }

        bool add_state(search& s, unsigned id) {
            if (s.m_seen.contains(id))
                return true;
            if (s.m_to_explore.size() >= m_max_states) {
                s.m_failure = failure::state_cap;
                return false;
            }
            resize(s);
            s.m_seen.insert(id);
            s.m_to_explore.push_back(id);
            if (nullable(id) != 0)
                mark_live(s, id);
            return true;
        }

        bool expand_state(unsigned id, failure& f) {
            if (m_expanded[id])
                return true;
            if (!m.inc()) {
                f = failure::resource;
                return false;
            }
            m_expanded[id] = true;
            nullable(id);
            auto const& cofactors = m_rw.get_derive().get_cached_cofactors(m_mode, m_states.get(id));
            for (auto const& [guard, target] : cofactors) {
                if (m_re.is_empty(target))
                    continue;
                unsigned target_id = intern(target);
                if (!m_successors[id].contains(target_id))
                    m_successors[id].push_back(target_id);
            }
            return true;
        }

        void close(search& s) {
            s.m_complete = true;
        }

        void expand(search& s) {
            if (s.m_complete || s.m_failure != failure::none)
                return;
            if (s.m_explore_head == s.m_to_explore.size()) {
                close(s);
                return;
            }

            unsigned id = s.m_to_explore[s.m_explore_head++];
            if (!expand_state(id, s.m_failure))
                return;
            resize(s);
            for (unsigned target : m_successors[id]) {
                if (!add_state(s, target))
                    return;
                if (!s.m_predecessors[target].contains(id))
                    s.m_predecessors[target].push_back(id);
                if (s.m_live[target])
                    mark_live(s, id);
            }
        }

        bool ensure(search& s, unsigned index) {
            while (index >= s.m_live_frontier.size() &&
                   !s.m_complete &&
                   s.m_failure == failure::none)
                expand(s);
            return index < s.m_live_frontier.size();
        }

        search* get_search(expr* root) {
            search* s = nullptr;
            if (m_searches.find(root, s))
                return s;
            s = alloc(search);
            unsigned root_id = intern(root);
            s->m_root_id = root_id;
            add_state(*s, root_id);
            m_searches.insert(root, s);
            return s;
        }

        void reset() {
            for (auto const& [root, s] : m_searches)
                dealloc(s);
            m_searches.reset();
            m_ids.reset();
            m_states.reset();
            m_successors.reset();
            m_nullable.reset();
            m_expanded.reset();
        }
    };

    live_states::live_states(seq_rewriter& rw, transition_mode mode, unsigned max_states) :
        m_imp(alloc(imp, rw, mode, max_states)) {
    }

    live_states::~live_states() {
        dealloc(m_imp);
    }

    expr* live_states::iterator::operator*() const {
        return m_owner->get_live(m_search, m_index);
    }

    live_states::iterator& live_states::iterator::operator++() {
        ++m_index;
        return *this;
    }

    bool live_states::iterator::operator!=(iterator const& other) const {
        if (other.m_end)
            return m_owner->ensure(m_search, m_index);
        return m_owner != other.m_owner ||
               m_search != other.m_search ||
               m_index != other.m_index ||
               m_end != other.m_end;
    }

    live_states::iterator live_states::reachable::begin() const {
        return iterator(m_owner, m_search, 0, false);
    }

    live_states::iterator live_states::reachable::end() const {
        return iterator(m_owner, m_search, 0, true);
    }

    bool live_states::reachable::failed() const {
        return m_owner->get_failure(m_search) != failure::none;
    }

    live_states::failure live_states::reachable::failure_reason() const {
        return m_owner->get_failure(m_search);
    }

    bool live_states::reachable::is_dead() {
        return !m_owner->ensure(m_search, 0) && !failed();
    }

    live_states::reachable live_states::reachable_live(expr* r) {
        return reachable(this, m_imp->get_search(r));
    }

    bool live_states::contains(expr* r) const {
        return m_imp->m_ids.contains(r);
    }

    unsigned live_states::state_id(expr* r) {
        return m_imp->intern(r) + 1;
    }

    unsigned live_states::num_states() const {
        return m_imp->m_states.size();
    }

    void live_states::reset() {
        m_imp->reset();
    }

    bool live_states::ensure(search* s, unsigned index) {
        return m_imp->ensure(*s, index);
    }

    /*
      Yield the root before the rest of the frontier.

      States enter m_live_frontier in the order their liveness is *discovered*, which is
      bottom-up: a nullable state is marked first and liveness then propagates backwards to
      its predecessors, so the root -- reachable to every state, and rarely nullable itself
      -- is typically marked last.  Callers use this order as a search order, and the
      eager traversal this replaced emitted states in interning order with the root at
      index 0.  Dropping the root to the back therefore reordered the consumer's search and
      cost several benchmarks their witness-first branch.

      The remap is well defined because every state in the search is reachable from the
      root, so liveness of any state propagates to the root within the same expand() step:
      whenever the frontier is non-empty at an ensure() boundary the root is already live
      and present in it, and the element count is unchanged.
    */
    expr* live_states::get_live(search* s, unsigned index) const {
        unsigned root = s->m_root_id;
        if (!s->m_live.get(root, false))
            return m_imp->m_states.get(s->m_live_frontier[index]);
        if (index == 0)
            return m_imp->m_states.get(root);
        for (unsigned i = 0, seen = 0; i < s->m_live_frontier.size(); ++i) {
            if (s->m_live_frontier[i] == root)
                continue;
            if (++seen == index)
                return m_imp->m_states.get(s->m_live_frontier[i]);
        }
        return m_imp->m_states.get(s->m_live_frontier[index]);
    }

    live_states::failure live_states::get_failure(search* s) const {
        return s->m_failure;
    }

}
