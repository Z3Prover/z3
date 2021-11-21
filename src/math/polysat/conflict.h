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
    class conflict_iterator;

    /** Conflict state, represented as core (~negation of clause). */
    class conflict {
        solver& s;
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

        void minimize_vars(signed_constraint c);

        /** Whether we are in a bailout state. We enter a bailout state when we give up on proper conflict resolution.  */
        bool m_bailout = false;

        constraint_manager& cm() const;
        scoped_ptr_vector<explainer> ex_engines;
        scoped_ptr_vector<variable_elimination_engine> ve_engines;
        scoped_ptr_vector<inference_engine> inf_engines;

    public:
        conflict(solver& s);
        ~conflict();

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
        /** all literals in clause are false */
        void set(clause const& cl);

        void insert(signed_constraint c);
        void insert(signed_constraint c, vector<signed_constraint> const& premises);
        void remove(signed_constraint c);
        void replace(signed_constraint c_old, signed_constraint c_new, vector<signed_constraint> const& c_new_premises);

        void keep(signed_constraint c);

        bool contains(signed_constraint c);

        /** Perform boolean resolution with the clause upon variable 'var'.
         * Precondition: core/clause contain complementary 'var'-literals.
         */
        void resolve(constraint_manager const& m, sat::literal lit, clause const& cl);

        /** Perform value resolution by applying various inference rules.
         *  Returns true if it was possible to eliminate the variable 'v'.
         */
        bool resolve_value(pvar v);

        /** Convert the core into a lemma to be learned. */
        clause_builder build_lemma();

        bool try_eliminate(pvar v);
        bool try_saturate(pvar v);

        using const_iterator = conflict_iterator;
        const_iterator begin() const;
        const_iterator end() const;

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, conflict const& c) { return c.display(out); }


    class conflict_iterator {
        friend class conflict;

        using it1_t = signed_constraints::const_iterator;
        using it2_t = indexed_uint_set::iterator;

        constraint_manager* m_cm;
        it1_t m_it1;
        it1_t m_end1;
        it2_t m_it2;

        conflict_iterator(constraint_manager& cm, it1_t it1, it1_t end1, it2_t it2):
            m_cm(&cm), m_it1(it1), m_end1(end1), m_it2(it2) {}

        static conflict_iterator begin(constraint_manager& cm, signed_constraints const& cs, indexed_uint_set const& lits) {
            return {cm, cs.begin(), cs.end(), lits.begin()};
        }

        static conflict_iterator end(constraint_manager& cm, signed_constraints const& cs, indexed_uint_set const& lits) {
            return {cm, cs.end(), cs.end(), lits.end()};
        }

    public:
        using value_type = signed_constraint;
        using difference_type = unsigned;
        using pointer = signed_constraint const*;
        using reference = signed_constraint const&;
        using iterator_category = std::input_iterator_tag;

        conflict_iterator& operator++() {
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

        bool operator==(conflict_iterator const& other) const {
            return m_it1 == other.m_it1 && m_it2 == other.m_it2;
        }

        bool operator!=(conflict_iterator const& other) const { return !operator==(other); }
    };


    inline conflict::const_iterator conflict::begin() const { return conflict_iterator::begin(cm(), m_constraints, m_literals); }
    inline conflict::const_iterator conflict::end() const { return conflict_iterator::end(cm(), m_constraints, m_literals); }
}
