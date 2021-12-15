/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat shift right constraint.

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/

#include "math/polysat/shr_constraint.h"
#include "math/polysat/solver.h"

namespace polysat {

    shr_constraint::shr_constraint(constraint_manager& m, pdd const& p, pdd const& q, pdd const& r):
        constraint(m, ckind_t::shr_t), m_p(p), m_q(q), m_r(r) {
        m_vars.append(p.free_vars());
        for (auto v : q.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);
        for (auto v : r.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);
    }    

    lbool shr_constraint::eval(pdd const& p, pdd const& q, pdd const& r) const {
        if (p.is_val() && r.is_val()) {
            if (p.val() >= p.manager().power_of_2())
                return r.is_zero() ? l_true : l_false;            
            if (r.is_val()) {
                // todo
            }
            // other cases when we know lower 
            // bound of q, e.g, q = 2^k*q1 + q2, where q2 is a constant.
        }
        return l_undef;
    }
    
    bool shr_constraint::is_always_false(bool is_positive, pdd const& p, pdd const& q, pdd const& r) const {
        switch (eval(p, q, r)) {
        case l_true: return !is_positive;
        case l_false: return is_positive;
        default: return false;
        }
    }

    bool shr_constraint::is_always_true(bool is_positive, pdd const& p, pdd const& q, pdd const& r) const {
        switch (eval(p, q, r)) {
        case l_true: return is_positive;
        case l_false: return !is_positive;
        default: return false;
        }
    }
    
    std::ostream& shr_constraint::display(std::ostream& out, lbool status) const {
        switch (status) {
        case l_true: return display(out);
        case l_false: return display(out << "~");
        default: return display(out << "?");
        }
    }

    std::ostream& shr_constraint::display(std::ostream& out) const {
        return out << r() << " == " << p() << " << " << q();
    }

    bool shr_constraint::is_always_false(bool is_positive) const {
        return is_always_false(is_positive, p(), q(), r());
    }

    bool shr_constraint::is_currently_false(assignment_t const& a, bool is_positive) const {
        return is_always_false(is_positive, p().subst_val(a), q().subst_val(a), r().subst_val(a));
    }

    bool shr_constraint::is_currently_true(assignment_t const& a, bool is_positive) const {
        return is_always_true(is_positive, p().subst_val(a), q().subst_val(a), r().subst_val(a));
    }

    /**
    * Enforce basic axioms, such as:
    * 
    * r = p >> q & q >= k -> r[i] = 0 for i > K - k
    * r = p >> q & q >= K -> r = 0
    * r = p >> q & q = k -> r[i] = p[i+k] for k + i < K
    * r = p >> q & q >= k -> r <= 2^{K-k-1}
    * r = p >> q => r <= p
    * r = p >> q & q != 0 => r < p
    * r = p >> q & q = 0 => r = p
    * 
    * when q is a constant, several axioms can be enforced at activation time.
    * 
    * Enforce also inferences and bounds
    * 
    * We can assume that shr_constraint is only asserted positive.
    */
    void shr_constraint::narrow(solver& s, bool is_positive) {
        SASSERT(is_positive);
        NOT_IMPLEMENTED_YET();
    }

    unsigned shr_constraint::hash() const {
        return mk_mix(p().hash(), q().hash(), r().hash());
    }

    bool shr_constraint::operator==(constraint const& other) const {
        if (other.kind() != ckind_t::shr_t)
            return false;
        auto const& o = other.to_shr();
        return p() == o.p() && q() == o.q() && r() == o.r();
    }

}
