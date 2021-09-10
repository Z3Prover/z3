/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat search state

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/boolean.h"
#include "math/polysat/types.h"

namespace polysat {

    typedef std::pair<pvar, rational> assignment_item_t;
    typedef vector<assignment_item_t> assignment_t;

    enum class search_item_k
    {
        assignment,
        boolean,
    };

    class search_item {
        search_item_k m_kind;
        union {
            pvar m_var;
            sat::literal m_lit;
        };

        search_item(pvar var): m_kind(search_item_k::assignment), m_var(var) {}
        search_item(sat::literal lit): m_kind(search_item_k::boolean), m_lit(lit) {}
    public:
        static search_item assignment(pvar var) { return search_item(var); }
        static search_item boolean(sat::literal lit) { return search_item(lit); }
        bool is_assignment() const { return m_kind == search_item_k::assignment; }
        bool is_boolean() const { return m_kind == search_item_k::boolean; }
        search_item_k kind() const { return m_kind; }
        pvar var() const { SASSERT(is_assignment()); return m_var; }
        sat::literal lit() const { SASSERT(is_boolean()); return m_lit; }
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, search_item const& s) { return s.display(out); }


    class search_state {

        vector<search_item> m_items;
        assignment_t        m_assignment;  // First-order part of the search state

    public:
        unsigned size() const { return m_items.size(); }
        search_item const& back() const { return m_items.back(); }
        search_item const& operator[](unsigned i) const { return m_items[i]; }

        assignment_t const& assignment() const { return m_assignment; }

        void push_assignment(pvar p, rational const& r);
        void push_boolean(sat::literal lit);
        void pop();

        using const_iterator = decltype(m_items)::const_iterator;
        const_iterator begin() const { return m_items.begin(); }
        const_iterator end() const { return m_items.end(); }

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, search_state const& s) { return s.display(out); }


    // Go backwards over the search_state
    class search_iterator {

        search_state*   m_search;

        unsigned current;
        unsigned first;

        struct idx_range {
            unsigned current;
            unsigned first;  // highest index + 1
        };
        vector<idx_range>     m_index_stack;

    public:
        search_iterator(search_state& search):
            m_search(&search) {
            first = m_search->size();
            current = first;  // we start one before the beginning, then it also works for empty m_search
        }

        search_item const& operator*() const {
            return (*m_search)[current];
        }

        unsigned last() {
            return m_index_stack.empty() ? 0 : m_index_stack.back().first;
        }

        bool next() {
            if (current > last()) {
                --current;
                return true;
            }
            else {
                SASSERT(current == last());
                if (m_index_stack.empty())
                    return false;
                current = m_index_stack.back().current;
                first = m_index_stack.back().first;
                m_index_stack.pop_back();
                return true;
            }
        }

        // to be called after all saturations for a step are done
        void push_block() {
            if (first != m_search->size()) {
                m_index_stack.push_back({current, first});
                first = m_search->size();
                current = first - 1;
            }
        }
    };

}
