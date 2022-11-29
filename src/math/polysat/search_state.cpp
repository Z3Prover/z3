/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat search state

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/

#include "math/polysat/search_state.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    std::ostream& search_state::display_verbose(search_item const& item, std::ostream& out) const {
        switch (item.kind()) {
        case search_item_k::assignment: {
            pvar const var = item.var();
            rational const& val = s.m_value[var];
            auto const& j = s.m_justification[var];
            out << "v" << std::setw(3) << std::left << var << " := ";
            out << std::setw(30) << std::left << num_pp(s, var, val);
            out << " @" << j.level();
            switch (j.kind()) {
            case justification_k::decision:
                return out << " by decision";
            case justification_k::propagation:
                return out << " by " << viable::var_pp(s.m_viable, var);
            case justification_k::unassigned:
                return out << " unassigned";
            }
        }
        case search_item_k::boolean: {
            sat::literal const lit = item.lit();
            out << rpad(4, lit);
            out << ": " << rpad(32, s.lit2cnstr(lit));
            out << " @" << s.m_bvars.level(lit);
            if (s.m_bvars.is_assumption(lit))
                out << " assumption";
            else if (s.m_bvars.is_bool_propagation(lit)) {
                clause* reason = s.m_bvars.reason(lit);
                out << " bool propagation " << show_deref(reason);
                for (auto l2 : *reason) {
                    out << "\n\t" << rpad(4, l2) << ": " << rpad(16, s.lit2cnstr(l2)) << "   " << bool_justification_pp(s.m_bvars, l2);
                }
            }
            else if (s.m_bvars.is_evaluation(lit)) {
                out << " evaluated";
            }
            else {
                SASSERT(s.m_bvars.is_decision(lit));
                out << " decision";
            }
            return out;
        }
        }
        UNREACHABLE();
        return out;
    }

    std::ostream& search_state::display_verbose(std::ostream& out) const {
        out << "Search state:\n";
        for (auto const& item : m_items)
            display_verbose(item, out) << "\n";
        return out;
    }

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
        m_assignment.push(p, r);
    }

    void search_state::push_boolean(sat::literal lit) {
        m_items.push_back(search_item::boolean(lit));
    }

    void search_state::pop() {
        auto const& item = m_items.back();
        if (item.is_assignment()) {
            SASSERT_EQ(item.var(), m_assignment.pairs().back().first);
            m_assignment.pop();
        }
        m_items.pop_back();
    }

}
