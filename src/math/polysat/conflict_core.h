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
#include "math/polysat/clause_builder.h"
#include <optional>

namespace polysat {

    class solver;
    class explainer;
    class inference_engine;
    class variable_elimination_engine;

    /** Conflict state, represented as core (~negation of clause). */
    class conflict_core {
        vector<signed_constraint> m_constraints;  // constraints used as premises
        uint_set m_vars;                          // variable assignments used as premises

        // If this is not null_var, the conflict was due to empty viable set for this variable.
        // Can be treated like "v = x" for any value x.
        pvar m_conflict_var = null_var;

        // NOTE: for now we keep this simple implementation.
        //       The drawback is that we may get weaker lemmas in some cases (but they are still correct).
        //       For example: if we have 4x+y=2 and y=0, then we have a conflict no matter the value of x, so we should drop x=? from the core.

        unsigned_vector m_pvar2count;             // reference count of variables
        void inc_pref(pvar v);
        void dec_pref(pvar v);

        bool_vector m_bvar2mark;                  // mark of Boolean variables
        void set_bmark(sat::bool_var b);
        void unset_bmark(sat::bool_var b);

        void set_mark(constraint* c);
        void unset_mark(constraint* c);


        /** Whether we are in a bailout state. We enter a bailout state when we give up on proper conflict resolution.  */
        bool m_bailout = false;
        std::optional<clause_builder> m_bailout_lemma;

        solver* m_solver = nullptr;
        solver& s() { return *m_solver; }
        constraint_manager& cm();
        scoped_ptr_vector<explainer> ex_engines;
        scoped_ptr_vector<variable_elimination_engine> ve_engines;
        scoped_ptr_vector<inference_engine> inf_engines;

        // ptr_addr_map<constraint, vector<signed_constraint>> m_saturation_premises;
        map<signed_constraint, vector<signed_constraint>, obj_hash<signed_constraint>, default_eq<signed_constraint>> m_saturation_premises;
        void handle_saturation_premises(signed_constraint c);
    public:
        conflict_core(solver& s);
        ~conflict_core();

        vector<signed_constraint> const& constraints() const { return m_constraints; }
        pvar conflict_var() const { return m_conflict_var; }

        bool is_bailout() const { return m_bailout; }
        void set_bailout() { SASSERT(!is_bailout()); m_bailout = true; }

        bool empty() const {
            return m_constraints.empty() && m_vars.empty() && conflict_var() == null_var;
        }

        void reset() {
            for (auto c : m_constraints)
                unset_mark(c.get());
            m_constraints.reset();
            m_vars.reset();
            m_conflict_var = null_var;
            m_saturation_premises.reset();
            m_bailout = false;
            m_bailout_lemma.reset();
            SASSERT(empty());
        }

        bool is_pmarked(pvar v) const;
        bool is_bmarked(sat::bool_var b) const;

        /** conflict because the constraint c is false under current variable assignment */
        void set(signed_constraint c);
        /** conflict because there is no viable value for the variable v */
        void set(pvar v);

        void insert(signed_constraint c);
        void insert(signed_constraint c, vector<signed_constraint> premises);
        void remove(signed_constraint c);
        void replace(signed_constraint c_old, signed_constraint c_new, vector<signed_constraint> c_new_premises);

        /** remove all constraints that contain the variable v */
        void remove_var(pvar v);

        void keep(signed_constraint c);

        /** Perform boolean resolution with the clause upon variable 'var'.
         * Precondition: core/clause contain complementary 'var'-literals.
         */
        void resolve(constraint_manager const& m, sat::bool_var var, clause const& cl);

        /** Perform value resolution by applying various inference rules.
         *  Returns true if it was possible to eliminate the variable 'v'.
         */
        bool resolve_value(pvar v, vector<signed_constraint> const& cjust_v);

        /** Convert the core into a lemma to be learned. */
        clause_builder build_lemma(unsigned reverted_level);
        clause_builder build_core_lemma(unsigned model_level);
        clause_builder build_fallback_lemma(unsigned lvl);

        bool try_eliminate(pvar v);
        bool try_saturate(pvar v);

        using const_iterator = decltype(m_constraints)::const_iterator;
        const_iterator begin() { return constraints().begin(); }
        const_iterator end() { return constraints().end(); }

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, conflict_core const& c) { return c.display(out); }

}
