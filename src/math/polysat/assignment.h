/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat substitution and assignment

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once
#include "math/polysat/types.h"

namespace polysat {

    using assignment_item_t = std::pair<pvar, rational>;

    class substitution_iterator {
        pdd m_current;
        substitution_iterator(pdd current) : m_current(std::move(current)) {}
        friend class substitution;

    public:
        using value_type = assignment_item_t;
        using difference_type = std::ptrdiff_t;
        using pointer = value_type const*;
        using reference = value_type const&;
        using iterator_category = std::input_iterator_tag;

        substitution_iterator& operator++() {
            SASSERT(!m_current.is_val());
            m_current = m_current.hi();
            return *this;
        }

        value_type operator*() const {
            SASSERT(!m_current.is_val());
            return { m_current.var(), m_current.lo().val() };
        }

        bool operator==(substitution_iterator const& other) const { return m_current == other.m_current; }
        bool operator!=(substitution_iterator const& other) const { return !operator==(other); }
    };

    /** Substitution for a single bit width. */
    class substitution {
        pdd m_subst;

        substitution(pdd p);

    public:
        substitution(dd::pdd_manager& m);
        substitution add(pvar var, rational const& value) const;
        pdd apply_to(pdd const& p) const;

        bool value(pvar var, rational& out_value) const;

        bool empty() const { return m_subst.is_one(); }

        pdd const& to_pdd() const { return m_subst; }
        unsigned bit_width() const { return to_pdd().power_of_2(); }

        bool operator==(substitution const& other) const { return &m_subst.manager() == &other.m_subst.manager() && m_subst == other.m_subst; }
        bool operator!=(substitution const& other) const { return !operator==(other); }

        std::ostream& display(std::ostream& out) const;

        using const_iterator = substitution_iterator;
        const_iterator begin() const { return {m_subst}; }
        const_iterator end() const { return {m_subst.manager().one()}; }
    };

    /** Full variable assignment, may include variables of varying bit widths. */
    class assignment {
        solver*                                 m_solver;
        vector<assignment_item_t>               m_pairs;  // TODO: do we still need this?
        mutable scoped_ptr_vector<substitution> m_subst;
        vector<substitution>                    m_subst_trail;

        substitution& subst(unsigned sz);
        solver& s() const { return *m_solver; }
    public:
        assignment(solver& s);
        // prevent implicit copy, use clone() if you do need a copy
        assignment(assignment const&) = delete;
        assignment& operator=(assignment const&) = delete;
        assignment(assignment&&) = default;
        assignment& operator=(assignment&&) = default;
        assignment clone() const;

        void push(pvar var, rational const& value);
        void pop();

        pdd apply_to(pdd const& p) const;

        bool empty() const { return pairs().empty(); }
        substitution const& subst(unsigned sz) const;
        vector<assignment_item_t> const& pairs() const { return m_pairs; }
        using const_iterator = decltype(m_pairs)::const_iterator;
        const_iterator begin() const { return pairs().begin(); }
        const_iterator end() const { return pairs().end(); }

        std::ostream& display(std::ostream& out) const;
    };

    using assignment_t = assignment;

    inline std::ostream& operator<<(std::ostream& out, substitution const& sub) { return sub.display(out); }

    inline std::ostream& operator<<(std::ostream& out, assignment const& a) { return a.display(out); }
}
