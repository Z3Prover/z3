/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat multiplication overflow constraint

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#pragma once
#include "math/polysat/mul_ovfl_constraint.h"

namespace polysat {


    mul_ovfl_constraint::mul_ovfl_constraint(constraint_manager& m, pdd const& p, pdd const& q):
        constraint(m, ckind_t::mul_ovfl_t), m_p(p), m_q(q) {

        simplify();
        m_vars.append(m_p.free_vars());
        for (auto v : m_q.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);

    }
    void mul_ovfl_constraint::simplify() {
        if (m_p.is_zero() || m_q.is_zero() ||
            m_p.is_one() || m_q.is_one()) {
            m_q = 0;
            m_p = 0;
            return;
        }
    }

    std::ostream& mul_ovfl_constraint::display(std::ostream& out, lbool status) const {
        switch (status) {
        case l_true: return display(out);
        case l_false: return display(out << "~");
        case l_undef: return display(out << "?");
        }       
    }

    std::ostream& mul_ovfl_constraint::display(std::ostream& out) const {
        return "ovfl*(" << m_p << ", " << m_q << ")";       
    }


    bool mul_ovfl_constraint::is_always_false(bool is_positive, pdd const& p, pdd const& q) const {
        if (!is_positive && (p.is_zero() || q.is_zero() ||
            p.is_one() || q.is_one()))
            return true;
        if (p.is_val() && q.is_val()) {
            bool ovfl = p.val() * q.val() > p().manager().max_value();
            return is_positive == ovfl;
        }
        return false;
    }

    bool mul_ovfl_constraint::is_always_false(bool is_positive) const {
        return is_always_false(is_positive, m_p, m_q);
    }

    bool mul_ovfl_constraint::is_currently_false(assignment_t const& a, bool is_positive) const {
        auto p = p().subst_val(s.assignment());
        auto q = q().subst_val(s.assignment());
        return is_always_false(is_positive, p, q);
    }

    bool mul_ovfl_constraint::is_currently_true(assignment_t const& a, bool is_positive) const {
        return !is_currently_false(a, !is_positive);
    }

    void mul_ovfl_constraint::narrow(solver& s, bool is_positive) {    
        auto p = p().subst_val(s.assignment());
        auto q = q().subst_val(s.assignment());

        if (is_always_false(is_positive, p, q)) {
            s.set_conflict({ this, is_positive });
            return;
        }

        NOT_IMPLEMENTED_YET();
    }

    unsigned mul_ovfl_constraint::hash() const {
    	return mk_mix(p().hash(), q().hash(), 25);
    }

    bool mul_ovfl_constraint::operator==(constraint const& other) const {
        return other.is_mul_ovfl() && p() == other.to_mul_ovfl().p() && q() == other.to_mul_ovfl().q();
    }
}
