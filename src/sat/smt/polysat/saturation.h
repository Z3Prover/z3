/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat core saturation

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once

#include "sat/smt/polysat/constraints.h"
#include "sat/smt/polysat/inequality.h"

namespace polysat {

    class umul_ovfl;

    /**
     * Introduce lemmas that derive new (simpler) constraints from the current conflict and partial model.
     */
    class saturation {

        using clause = std::initializer_list<constraint_or_dependency>;
        core& c;
        constraints& C;

        void propagate(signed_constraint const& sc, std::initializer_list<constraint_id> const& premises);
        void add_clause(char const* name, clause const& cs, bool is_redundant);

        struct constraint_filter {
            core& c;
            std::function<bool(signed_constraint const& sc)> const& m_filter;
            unsigned m_index;
            unsigned m_end;
            void fwd() {
                for (; m_index < m_end && !m_filter(c.get_constraint(c.assigned_constraints()[m_index])); ++m_index);
                if (c.inconsistent())
                    m_index = m_end;
            }
            constraint_filter(core& c, std::function<bool(signed_constraint const& sc)> const& filter, unsigned i) :
                c(c), m_filter(filter), m_index(i), m_end(c.assigned_constraints().size()) {
                fwd();
            }

            bool operator!=(constraint_filter const& other) const { return m_index != other.m_index; }
            constraint_filter& operator++() { ++m_index; fwd(); return *this; }
            constraint_id operator*() const { return c.assigned_constraints()[m_index]; }
        };
        struct constraint_iterator {
            core& c;
            std::function<bool(signed_constraint const& sc)> const& m_filter;
            constraint_iterator(core& c, std::function<bool(signed_constraint const& sc)> const& filter) :
                c(c), m_filter(filter) {}
            constraint_filter begin() const { return constraint_filter(c, m_filter, 0); }
            constraint_filter end() const { return constraint_filter(c, m_filter, c.assigned_constraints().size()); }
        };
        
        bool match_constraints(std::function<bool(signed_constraint const& sc)> const& p, constraint_id& id);

        void propagate_infer_equality(pvar x, inequality const& a_l_b);
        void try_ugt_x(pvar v, inequality const& i);
        void try_ugt_y(pvar v, inequality const& i);
        void try_ugt_z(pvar z, inequality const& i);
        void try_umul_ovfl(pvar v, umul_ovfl const& sc);

        signed_constraint ineq(bool is_strict, pdd const& x, pdd const& y);       

        void resolve(pvar v, inequality const& i);

    public:
        saturation(core& c);
        bool resolve(pvar v, constraint_id cid);
    };
}
