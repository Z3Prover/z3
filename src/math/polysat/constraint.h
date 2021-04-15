/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints

Abstract:

    Polynomial constriants

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/
#pragma once
#include "math/polysat/types.h"


namespace polysat {

    enum ckind_t { eq_t, ule_t, sle_t };

    class eq_constraint;
    class ule_constraint;

    class constraint {
        unsigned         m_level;
        ckind_t          m_kind;
        p_dependency_ref m_dep;
        unsigned_vector  m_vars;
        constraint(unsigned lvl, p_dependency_ref& dep, ckind_t k): 
            m_level(lvl), m_kind(k), m_dep(dep) {}
    public:
        static constraint* eq(unsigned lvl, pdd const& p, p_dependency_ref& d);
        bool is_eq() const { return m_kind == ckind_t::eq_t; }
        bool is_ule() const { return m_kind == ckind_t::ule_t; }
        bool is_sle() const { return m_kind == ckind_t::sle_t; }
        ckind_t kind() const { return m_kind; }
        virtual std::ostream& display(std::ostream& out) const = 0;
        eq_constraint& to_eq() { return *dynamic_cast<eq_constraint*>(this); }
        eq_constraint const& to_eq() { return *dynamic_cast<eq_constraint const*>(this); }
        p_dependency* dep() const { return m_dep; }
        unsigned_vector& vars() { return m_vars; }
        unsigned level() const { return m_level; }
    };

    class eq_constraint : public constraint {
        pdd m_poly;
    public:
        eq_constraint(unsigned lvl, pdd const& p, pdd const& q, p_dependency_ref& dep,):
            constraint(lvl, dep, ckind_t::eq_t), m_poly(p) {
            m_vars.append(p.free_vars());
        }
        pdd const & p() const { return m_poly; }
        std::ostream& display(std::ostream& out) const override;
    };

    inline std::ostream& operator<<(std::ostream& out, constraint const& c) { return c.display(out); }
        

}
