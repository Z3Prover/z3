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

    class constraint {
        unsigned         m_level;
        ckind_t          m_kind;
        pdd              m_poly;
        pdd              m_other;
        p_dependency_ref m_dep;
        unsigned_vector  m_vars;
        constraint(unsigned lvl, pdd const& p, pdd const& q, p_dependency_ref& dep, ckind_t k): 
            m_level(lvl), m_kind(k), m_poly(p), m_other(q), m_dep(dep) {
            m_vars.append(p.free_vars());
            if (q != p) 
                for (auto v : q.free_vars())
                    m_vars.insert(v);            
            }
    public:
        static constraint* eq(unsigned lvl, pdd const& p, p_dependency_ref& d) { 
            return alloc(constraint, lvl, p, p, d, ckind_t::eq_t); 
        }
        static constraint* ule(unsigned lvl, pdd const& p, pdd const& q, p_dependency_ref& d) { 
            return alloc(constraint, lvl, p, q, d, ckind_t::ule_t); 
        }
        bool is_eq() const { return m_kind == ckind_t::eq_t; }
        bool is_ule() const { return m_kind == ckind_t::ule_t; }
        bool is_sle() const { return m_kind == ckind_t::sle_t; }
        ckind_t kind() const { return m_kind; }
        pdd const &  p() const { return m_poly; }
        pdd const &  lhs() const { return m_poly; }
        pdd const &  rhs() const { return m_other; }
        std::ostream& display(std::ostream& out) const;
        p_dependency* dep() const { return m_dep; }
        unsigned_vector& vars() { return m_vars; }
        unsigned level() const { return m_level; }
    };

    inline std::ostream& operator<<(std::ostream& out, constraint const& c) { return c.display(out); }

}
