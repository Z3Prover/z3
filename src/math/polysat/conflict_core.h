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
    class conflict_core_iterator;

    /** Conflict state, represented as core (~negation of clause). */
    class conflict_core {
        signed_constraints m_constraints;   // new constraints used as premises
        indexed_uint_set m_literals;        // set of boolean literals in the conflict
        uint_set m_vars;                    // variable assignments used as premises

        // If this is not null_var, the conflict was due to empty viable set for this variable.
        // Can be treated like "v = x" for any value x.
        pvar m_conflict_var = null_var;

        unsigned_vector m_pvar2count;             // reference count of variables
        void inc_pref(pvar v);
        void dec_pref(pvar v);

        bool_vector m_bvar2mark;                  // mark of Boolean variables
        void set_bmark(sat::bool_var b);
        void unset_bmark(sat::bool_var b);

        void set_mark(signed_constraint c);
        void unset_mark(signed_constraint c);

        bool contains_literal(sat::literal lit) const;
        void insert_literal(sat::literal lit);
        void remove_literal(sat::literal lit);

        /** Whether we are in a bailout state. We enter a bailout state when we give up on proper conflict resolution.  */
        bool m_bailout = false;
        std::optional<clause_builder> m_bailout_lemma;

        solver* m_solver = nullptr;
        solver& s() const { return *m_solver; }
        constraint_manager& cm() const;
        scoped_ptr_vector<explainer> ex_engines;
        scoped_ptr_vector<variable_elimination_engine> ve_engines;
        scoped_ptr_vector<inference_engine> inf_engines;

        // ptr_addr_map<constraint, vector<signed_constraint>> m_saturation_premises;
        map<signed_constraint, vector<signed_constraint>, obj_hash<signed_constraint>, default_eq<signed_constraint>> m_saturation_premises;
    public:
        conflict_core(solver& s);
        ~conflict_core();

        pvar conflict_var() const { return m_conflict_var; }

        bool is_bailout() const { return m_bailout; }
        void set_bailout();

        bool empty() const {
            return m_constraints.empty() && m_vars.empty() && m_literals.empty() && m_conflict_var == null_var;
        }

        void reset();

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
        clause_builder build_lemma();
        clause_builder build_core_lemma();

        bool try_eliminate(pvar v);
        bool try_saturate(pvar v);

        using const_iterator = conflict_core_iterator;
        const_iterator begin() const;
        const_iterator end() const;

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, conflict_core const& c) { return c.display(out); }


    class conflict_core_iterator {
        friend class conflict_core;

        using it1_t = signed_constraints::const_iterator;
        using it2_t = indexed_uint_set::iterator;

        constraint_manager* m_cm;
        it1_t m_it1;
        it1_t m_end1;
        it2_t m_it2;

        conflict_core_iterator(constraint_manager& cm, it1_t it1, it1_t end1, it2_t it2):
            m_cm(&cm), m_it1(it1), m_end1(end1), m_it2(it2) {}

        static conflict_core_iterator begin(constraint_manager& cm, signed_constraints cs, indexed_uint_set lits) {
            return {cm, cs.begin(), cs.end(), lits.begin()};
        }

        static conflict_core_iterator end(constraint_manager& cm, signed_constraints cs, indexed_uint_set lits) {
            return {cm, cs.end(), cs.end(), lits.end()};
        }

    public:
        using value_type = signed_constraint;
        using difference_type = unsigned;
        using pointer = signed_constraint const*;
        using reference = signed_constraint const&;
        using iterator_category = std::input_iterator_tag;

        conflict_core_iterator& operator++() {
            if (m_it1 != m_end1)
                ++m_it1;
            else
                ++m_it2;
            return *this;
        }

        signed_constraint operator*() const {
            if (m_it1 != m_end1)
                return *m_it1;
            else
                return m_cm->lookup(sat::to_literal(*m_it2));
        }

        bool operator==(conflict_core_iterator const& other) const {
            return m_it1 == other.m_it1 && m_it2 == other.m_it2;
        }

        bool operator!=(conflict_core_iterator const& other) const { return !operator==(other); }
    };


    inline conflict_core::const_iterator conflict_core::begin() const { return conflict_core_iterator::begin(cm(), m_constraints, m_literals); }
    inline conflict_core::const_iterator conflict_core::end() const { return conflict_core_iterator::end(cm(), m_constraints, m_literals); }
}
