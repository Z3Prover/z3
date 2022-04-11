/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat search state

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/search_state.h"
#include "math/polysat/solver.h"

namespace polysat {

    std::ostream& search_state::display(search_item const& item, std::ostream& out) const {
        rational r;
        switch (item.kind()) {
        case search_item_k::assignment:
            if (value(item.var(), r))
                return out << "v" << item.var() << " := " << r;
            else
                return out << "v" << item.var() << " := *";
        case search_item_k::boolean:
            return out << item.lit();
        }
        UNREACHABLE();
        return out;
    }

    std::ostream& search_state::display(std::ostream& out) const {
        for (auto const& item : m_items)
            display(item, out) << " ";
        return out;        
    }

    bool search_state::value(pvar v, rational& val) const {
        for (auto const& [p, r] : m_assignment)
            if (v == p) {
                val = r;
                return true;
            }
        return false;
    }

    void search_state::push_assignment(pvar p, rational const& r) {
        m_items.push_back(search_item::assignment(p));
        m_assignment.push_back({p, r});
        unsigned sz = s.size(p);
        pdd& s = assignment(sz);
        m_subst_trail.push_back(s);
        s = s.subst_add(p, r);
        SASSERT(s == *m_subst[sz]);
    }

    pdd& search_state::assignment(unsigned sz) const {
        m_subst.reserve(sz + 1);
        if (!m_subst[sz])
            m_subst.set(sz, alloc(pdd, s.sz2pdd(sz).one()));
        return *m_subst[sz];
    }

    void search_state::pop_assignment() {
        m_assignment.pop_back();
        pdd& s = m_subst_trail.back();
        auto& m = s.manager();
        unsigned sz = m.power_of_2();
        *m_subst[sz] = s;
        m_subst_trail.pop_back();
    }

    void search_state::push_boolean(sat::literal lit) {
        m_items.push_back(search_item::boolean(lit));
    }

    void search_state::pop() {
        auto const& item = m_items.back();
        if (item.is_assignment() && !m_assignment.empty() && item.var() == m_assignment.back().first) 
            pop_assignment();
        m_items.pop_back();
    }

}
