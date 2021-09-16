/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat clauses

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/boolean.h"
#include "math/polysat/types.h"

namespace polysat {

    class signed_constraint;

    class clause;
    using clause_ref = ref<clause>;
    using clause_ref_vector = sref_vector<clause>;

    /// Disjunction of constraints represented by boolean literals
    // NB code review:
    // right, ref-count is unlikely the right mechanism.
    // In the SAT solver all clauses are managed in one arena (auxiliarary and redundant)
    // and deleted when they exist the arena.
    //
    class clause {
        friend class constraint_manager;

        unsigned m_ref_count = 0;  // TODO: remove refcount once we confirm it's not needed anymore
        unsigned m_level;
        pvar m_justified_var = null_var;  // The variable that was restricted by learning this lemma.
        p_dependency_ref m_dep;
        bool m_redundant = false;
        sat::literal_vector m_literals;


        /* TODO: embed literals to save an indirection?
        unsigned m_num_literals;
        constraint* m_literals[0];

        static size_t object_size(unsigned m_num_literals) {
            return sizeof(clause) + m_num_literals * sizeof(constraint*);
        }
        */

        clause(unsigned lvl, p_dependency_ref d, sat::literal_vector literals):
            m_level(lvl), m_dep(std::move(d)), m_literals(std::move(literals)) {
            SASSERT(std::count(m_literals.begin(), m_literals.end(), sat::null_literal) == 0);
        }

    public:
        void inc_ref() { m_ref_count++; }
        void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (!m_ref_count) dealloc(this); }

        static clause_ref from_unit(unsigned lvl, signed_constraint c, p_dependency_ref d);
        static clause_ref from_literals(unsigned lvl, p_dependency_ref d, sat::literal_vector literals);

        p_dependency* dep() const { return m_dep; }
        unsigned level() const { return m_level; }

        pvar justified_var() const { return m_justified_var; }
        void set_justified_var(pvar v) { SASSERT(m_justified_var == null_var); m_justified_var = v; }

        bool empty() const { return m_literals.empty(); }
        unsigned size() const { return m_literals.size(); }
        sat::literal operator[](unsigned idx) const { return m_literals[idx]; }
        sat::literal& operator[](unsigned idx) { return m_literals[idx]; }

        using const_iterator = typename sat::literal_vector::const_iterator;
        const_iterator begin() const { return m_literals.begin(); }
        const_iterator end() const { return m_literals.end(); }

        bool is_always_false(solver& s) const;
        bool is_currently_false(solver& s) const;

        std::ostream& display(std::ostream& out) const;

        void set_redundant(bool r) { m_redundant = r; }
        bool is_redundant() const { return m_redundant; }
    };

    inline std::ostream& operator<<(std::ostream& out, clause const& c) { return c.display(out); }
}
