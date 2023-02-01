/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat clauses

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once
#include "math/polysat/boolean.h"
#include "math/polysat/types.h"

namespace polysat {

    class signed_constraint;
    class simplify_clause;

    /// Disjunction of constraints represented by boolean literals
    // NB code review:
    // right, ref-count is unlikely the right mechanism.
    // In the SAT solver all clauses are managed in one arena (auxiliarary and redundant)
    // and deleted when they exist the arena.
    //
    class clause {
    public:
        static inline const bool redundant_default = true;
    private:
        friend class constraint_manager;
        friend class simplify_clause;

        unsigned m_ref_count = 0;  // TODO: remove refcount once we confirm it's not needed anymore
        bool m_redundant = redundant_default;
        bool m_active = false;  // clause is active iff it has been added to the solver and boolean watchlists
        sat::literal_vector m_literals;
        char const* m_name = "";


        /* TODO: embed literals to save an indirection?
        unsigned m_num_literals;
        constraint* m_literals[0];

        static size_t object_size(unsigned m_num_literals) {
            return sizeof(clause) + m_num_literals * sizeof(constraint*);
        }
        */

        clause(sat::literal_vector literals):
            m_literals(std::move(literals)) {
            SASSERT(count(m_literals, sat::null_literal) == 0);
        }

        void set_active() { m_active = true; }

    public:
        void inc_ref() { m_ref_count++; }
        void dec_ref() { SASSERT(m_ref_count > 0); m_ref_count--; if (!m_ref_count) dealloc(this); }

        static clause_ref from_unit(signed_constraint c);
        static clause_ref from_literals(sat::literal_vector literals);

        bool empty() const { return m_literals.empty(); }
        unsigned size() const { return m_literals.size(); }
        sat::literal operator[](unsigned idx) const { return m_literals[idx]; }
        sat::literal& operator[](unsigned idx) { return m_literals[idx]; }

        sat::literal_vector& literals() { return m_literals; }
        sat::literal_vector const& literals() const { return m_literals; }

        using const_iterator = typename sat::literal_vector::const_iterator;
        const_iterator begin() const { return m_literals.begin(); }
        const_iterator end() const { return m_literals.end(); }

        std::ostream& display(std::ostream& out) const;

        void set_redundant(bool r) { m_redundant = r; }
        bool is_redundant() const { return m_redundant; }

        bool is_active() const { return m_active; }

        void set_name(char const* name) { m_name = name; }
        char const* name() const { return m_name; }
    };

    inline std::ostream& operator<<(std::ostream& out, clause const& c) { return c.display(out); }
}
