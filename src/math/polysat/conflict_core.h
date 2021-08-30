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
        vector<signed_constraint> m_constraints;

        /** Storage for new constraints that may not yet have a boolean variable yet */
        ptr_vector<constraint> m_storage;

        // If this is not null_var, the conflict was due to empty viable set for this variable.
        // Can be treated like "v = x" for any value x.
        pvar m_conflict_var = null_var;

        /** True iff the conflict depends on the current variable assignment. (If so, additional constraints must be added to the final learned clause.) */
        bool m_needs_model = false;
        // NOTE: for now we keep this simple implementation.
        //       The drawback is that we may get weaker lemmas in some cases (but they are still correct).
        //       For example: if we have 4x+y=2 and y=0, then we have a conflict no matter the value of x, so we should drop x=? from the core.

    public:
        ~conflict_core() {
            gc();
        }

        vector<signed_constraint> const& constraints() const { return m_constraints; }
        bool needs_model() const { return m_needs_model; }

        bool empty() const {
            return m_constraints.empty() && !m_needs_model;
        }

        void reset() {
            m_constraints.reset();
            m_needs_model = false;
            gc();
            SASSERT(empty());
        }

        /** for bailing out with a conflict at the base level */
        void set(std::nullptr_t);
        /** conflict because the constraint c is false under current variable assignment */
        void set(signed_constraint c);
        /** conflict because there is no viable value for the variable v */
        void set(pvar v, vector<signed_constraint> const& cjust_v);

        /** Garbage-collect temporary constraints */
        void gc() {
            for (auto* c : m_storage)
                if (!c->has_bvar())
                    dealloc(c);
            m_storage.reset();
        }

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, conflict_core const& c) { return c.display(out); }

}
