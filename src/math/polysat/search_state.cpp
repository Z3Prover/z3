/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat search state

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/search_state.h"

namespace polysat {

    std::ostream& search_item::display(std::ostream& out) const {
        switch (kind()) {
        case search_item_k::assignment:
            return out << "assignment(v" << var() << ")";
        case search_item_k::boolean:
            return out << "boolean(" << lit() << ")";
        }
        UNREACHABLE();
        return out;
    }

    void search_state::push_assignment(pvar p, rational const& r) {
        m_items.push_back(search_item::assignment(p));
        m_assignment.push_back({p, r});
    }

    void search_state::push_boolean(bool_lit lit) {
        m_items.push_back(search_item::boolean(lit));
    }

    void search_state::pop() {
        auto const& item = m_items.back();
        if (item.is_assignment()) {
            m_assignment.pop_back();
        }
        m_items.pop_back();
    }

}
