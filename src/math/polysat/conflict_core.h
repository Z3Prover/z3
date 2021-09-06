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

    class solver;
    class inference_engine;
    class variable_elimination_engine;

    /** Conflict state, represented as core (~negation of clause). */
    class conflict_core {
        vector<signed_constraint> m_constraints;

        // If this is not null_var, the conflict was due to empty viable set for this variable.
        // Can be treated like "v = x" for any value x.
        // TODO: we could always set this to the variable we're currently focusing on.
        pvar m_conflict_var = null_var;

        /** True iff the conflict depends on the current variable assignment. (If so, additional constraints must be added to the final learned clause.) */
        bool m_needs_model = false;
        // NOTE: for now we keep this simple implementation.
        //       The drawback is that we may get weaker lemmas in some cases (but they are still correct).
        //       For example: if we have 4x+y=2 and y=0, then we have a conflict no matter the value of x, so we should drop x=? from the core.

        /** Whether we are in a bailout state. We enter a bailout state when we give up on proper conflict resolution.  */
        bool m_bailout = false;

        solver* m_solver = nullptr;
        constraint_manager& cm();
        scoped_ptr_vector<variable_elimination_engine> ve_engines;
        scoped_ptr_vector<inference_engine> inf_engines;

        // ptr_addr_map<constraint, vector<signed_constraint>> m_saturation_premises;
        map<signed_constraint, vector<signed_constraint>, obj_hash<signed_constraint>, default_eq<signed_constraint>> m_saturation_premises;
    public:
        conflict_core(solver& s);
        ~conflict_core();

        vector<signed_constraint> const& constraints() const { return m_constraints; }
        bool needs_model() const { return m_needs_model; }
        pvar conflict_var() const { return m_conflict_var; }

        bool is_bailout() const { return m_bailout; }
        void set_bailout() { m_bailout = true; }

        bool empty() const {
            return m_constraints.empty() && !m_needs_model && m_conflict_var == null_var;
        }

        void reset() {
            m_constraints.reset();
            m_needs_model = false;
            m_conflict_var = null_var;
            m_saturation_premises.reset();
            m_bailout = false;
            SASSERT(empty());
        }

        /** conflict because the constraint c is false under current variable assignment */
        void set(signed_constraint c);
        /** conflict because there is no viable value for the variable v */
        void set(pvar v);

        void insert(signed_constraint c);
        void insert(signed_constraint c, vector<signed_constraint> premises);
        void remove(signed_constraint c);

        /** Perform boolean resolution with the clause upon variable 'var'.
         * Precondition: core/clause contain complementary 'var'-literals.
         */
        void resolve(constraint_manager const& m, sat::bool_var var, clause const& cl);

        /** Convert the core into a lemma to be learned. */
        clause_ref build_lemma();

        bool try_eliminate(pvar v);
        bool try_saturate(pvar v);

        using const_iterator = decltype(m_constraints)::const_iterator;
        const_iterator begin() { return constraints().begin(); }
        const_iterator end() { return constraints().end(); }

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, conflict_core const& c) { return c.display(out); }

}
