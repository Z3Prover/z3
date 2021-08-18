/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/constraint.h"

namespace polysat {

    /** Conflict state, represented as core (~negation of clause). */
    class conflict_core {
        vector<constraint_literal> m_constraints;

        /** True iff the conflict depends on the current variable assignment. (If so, additional constraints must be added to the final learned clause.) */
        bool m_needs_model = false;
        // NOTE: for now we keep this simple implementation.
        //       The drawback is that we may get weaker lemmas in some cases (but they are still correct).
        //       For example: if we have 4x+y=2 and y=0, then we have a conflict no matter the value of x, so we should drop x=? from the core.

    public:

        vector<constraint_literal> const& constraints() const { return m_constraints; }
        bool needs_model() const { return m_needs_model; }

        bool empty() const {
            return m_constraints.empty() && !m_needs_model;
        }

        void reset() {
            m_constraints.reset();
            m_needs_model = false;
            SASSERT(empty());
        }

        /** for bailing out with a conflict at the base level */
        void set(std::nullptr_t);
        /** conflict because the constraint c is false under current variable assignment */
        void set(constraint_literal c);
        /** conflict because there is no viable value for the variable v */
        void set(pvar v, vector<constraint_literal> const& cjust_v);

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, conflict_core const& c) { return c.display(out); }

}
