/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat justification

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once
#include "math/polysat/types.h"


namespace polysat {


    /**
     * Justification kind for a variable assignment.
     */
    enum class justification_k {
        unassigned,
        decision,
        propagation_by_viable,
        propagation_by_slicing,
    };

    class justification {
        justification_k m_kind;
        unsigned        m_level;
        justification(justification_k k, unsigned lvl): m_kind(k), m_level(lvl) {}
    public:
        justification(): m_kind(justification_k::unassigned) {}
        static justification unassigned() { return justification(justification_k::unassigned, 0); }
        static justification decision(unsigned lvl) { return justification(justification_k::decision, lvl); }
        static justification propagation_by_viable(unsigned lvl) { return justification(justification_k::propagation_by_viable, lvl); }
        static justification propagation_by_slicing(unsigned lvl) { return justification(justification_k::propagation_by_slicing, lvl); }
        bool is_decision() const { return m_kind == justification_k::decision; }
        bool is_unassigned() const { return m_kind == justification_k::unassigned; }
        bool is_propagation_by_viable() const { return m_kind == justification_k::propagation_by_viable; }
        bool is_propagation_by_slicing() const { return m_kind == justification_k::propagation_by_slicing; }
        justification_k kind() const { return m_kind; }
        unsigned level() const { SASSERT(!is_unassigned()); return m_level; }
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, justification const& j) { return j.display(out); }

}
