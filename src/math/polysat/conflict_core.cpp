/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#include "math/polysat/conflict_core.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"

namespace polysat {

    std::ostream& conflict_core::display(std::ostream& out) const {
        bool first = true;
        for (auto c : m_constraints) {
            if (first)
                first = false;
            else
                out << "  ;  ";
            out << c;
        }
        /*
        for (unsigned i = 0; i < m_num_assignments; ++i) {
            auto& [v, x] = m_solver.assignment().get(i);
            if (first)
                first = false;
            else
                out << "  ;  ";
            out << v << " := " << x;
        }
        */
        if (m_needs_model)
            out << "  ;  + current model";
        return out;
    }

    void conflict_core::set(std::nullptr_t) {
        SASSERT(empty());
        m_constraints.push_back({});
        // m_num_assignments = 0;
        m_needs_model = false;
    }

    void conflict_core::set(constraint_literal c) {
        LOG("Conflict: " << c);
        SASSERT(empty());
        m_constraints.push_back(std::move(c));
        // m_num_assignments = m_solver.assignment().size();
        m_needs_model = true;
    }

    void conflict_core::set(pvar v, ptr_vector<constraint> const& cjust_v) {
        SASSERT(empty());
        NOT_IMPLEMENTED_YET();
        // m_constraints.append(cjust_v);  // TODO: constraint/literal mismatch
        // m_num_assignments = m_solver.assignment().size();
        m_needs_model = true;

        // previously:
        // SASSERT(!is_conflict());
        // m_conflict.append(m_cjust[v]);
        // if (m_cjust[v].empty())
        //     m_conflict.push_back(nullptr);
        // LOG("Conflict for v" << v << ": " << m_conflict);
    }

}
