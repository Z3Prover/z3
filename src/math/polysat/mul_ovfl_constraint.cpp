/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat multiplication overflow constraint

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#pragma once
#include "math/polysat/mul_ovfl_constraint.h"
#include "math/polysat/solver.h"

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
        return out;
    }

    std::ostream& mul_ovfl_constraint::display(std::ostream& out) const {
        return out << "ovfl*(" << m_p << ", " << m_q << ")";       
    }

    bool mul_ovfl_constraint::is_always_false(bool is_positive, pdd const& p, pdd const& q) const {
        if (!is_positive && (p.is_zero() || q.is_zero() ||
            p.is_one() || q.is_one()))
            return true;
        if (p.is_val() && q.is_val()) {
            bool ovfl = p.val() * q.val() > p.manager().max_value();
            return is_positive == ovfl;
        }
        return false;
    }

    bool mul_ovfl_constraint::is_always_true(bool is_positive, pdd const& p, pdd const& q) const {
        if (is_positive && (p.is_zero() || q.is_zero() ||
            p.is_one() || q.is_one()))
            return true;
        if (p.is_val() && q.is_val()) {
            bool noovfl = p.val() * q.val() <= p.manager().max_value();
            return is_positive == noovfl;
        }
        return false;
    }

    bool mul_ovfl_constraint::is_always_false(bool is_positive) const {
        return is_always_false(is_positive, m_p, m_q);
    }

    bool mul_ovfl_constraint::is_currently_false(assignment_t const& a, bool is_positive) const {
        return is_always_false(is_positive, p().subst_val(a), q().subst_val(a));
    }

    bool mul_ovfl_constraint::is_currently_true(assignment_t const& a, bool is_positive) const {
        return is_always_true(is_positive, p().subst_val(a), q().subst_val(a));
    }

    void mul_ovfl_constraint::narrow(solver& s, bool is_positive) {    
        auto p1 = p().subst_val(s.assignment());
        auto q1 = q().subst_val(s.assignment());

        if (is_always_false(is_positive, p1, q1)) {
            s.set_conflict({ this, is_positive });
            return;
        }
        if (is_always_true(is_positive, p1, q1))
            return;
        if (narrow_bound(s, is_positive, p1, q1))
            return;
        if (narrow_bound(s, is_positive, q1, p1))
            return;
    }

    /**
    * if p constant, q, propagate inequality
    * 
    * TODO optimizations:
    * if p is constant, q variable, update viable for q
    * 
    * Use bounds on variables in p instead of current assignment as premise.
    * This is a more general lemma
    */
    bool mul_ovfl_constraint::narrow_bound(solver& s, bool is_positive, pdd const& p, pdd const& q) {

        if (!p.is_val())
            return false;

        SASSERT(!p.is_zero() && !p.is_one());
        auto const& max = p.manager().max_value();
        // p * q >= max + 1 <=> q >= (max + 1)/p <=> q >= ceil((max+1)/p)
        auto bound = ceil((max + 1) / p.val());

        // the clause that explains bound <= q or bound > q 
        // is justified by the partial assignment to m_vars

        signed_constraint sc(this, is_positive);       
        signed_constraint conseq = is_positive ? s.ule(bound, q) : s.ult(q, bound);

        clause_builder cb(s);
        cb.push_new(~sc);
        cb.push_new(conseq);
        for (auto v : m_vars)
            if (s.is_assigned(v))
                cb.push_new(~s.eq(s.var(v), s.get_value(v)));
        clause_ref just = cb.build();
        s.assign_propagate(conseq.blit(), *just);
        return true;
    }

    unsigned mul_ovfl_constraint::hash() const {
    	return mk_mix(p().hash(), q().hash(), 325);
    }

    bool mul_ovfl_constraint::operator==(constraint const& other) const {
        return other.is_mul_ovfl() && p() == other.to_mul_ovfl().p() && q() == other.to_mul_ovfl().q();
    }
}
