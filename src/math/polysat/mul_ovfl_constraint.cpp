/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat multiplication overflow constraint

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
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
        if (m_p.index() > m_q.index())
            std::swap(m_p, m_q);
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

    lbool mul_ovfl_constraint::eval(pdd const& p, pdd const& q) const {
        if (p.is_zero() || q.is_zero() || p.is_one() || q.is_one())
            return l_false;

        if (p.is_val() && q.is_val()) {
            if (p.val() * q.val() > p.manager().max_value())
                return l_true;
            else
                return l_false;
        }
        return l_undef;
    }

    bool mul_ovfl_constraint::is_always_false(bool is_positive, pdd const& p, pdd const& q) const {
        switch (eval(p, q)) {
        case l_true: return !is_positive;
        case l_false: return is_positive;
        default: return false;
        }
    }

    bool mul_ovfl_constraint::is_always_true(bool is_positive, pdd const& p, pdd const& q) const {
        switch (eval(p, q)) {
        case l_true: return is_positive;
        case l_false: return !is_positive;
        default: return false;
        }
    }

    bool mul_ovfl_constraint::is_always_false(bool is_positive) const {
        return is_always_false(is_positive, m_p, m_q);
    }


    bool mul_ovfl_constraint::is_currently_false(solver& s, bool is_positive) const {
        return is_always_false(is_positive, s.subst(p()), s.subst(q()));
    }

    bool mul_ovfl_constraint::is_currently_true(solver& s, bool is_positive) const {
        return is_always_true(is_positive, s.subst(p()), s.subst(q()));
    }

    void mul_ovfl_constraint::narrow(solver& s, bool is_positive, bool first) {    
        auto p1 = s.subst(p());
        auto q1 = s.subst(q());
        
        if (is_always_false(is_positive, p1, q1)) {
            s.set_conflict({ this, is_positive });
            return;
        }
        if (is_always_true(is_positive, p1, q1))
            return;

        if (try_viable(s, is_positive, p(), q(), p1, q1))
            return;
        
        if (narrow_bound(s, is_positive, p(), q(), p1, q1))
            return;
        if (narrow_bound(s, is_positive, q(), p(), q1, p1))
            return;

        
    }

    /**
    * if p constant, q, propagate inequality   
    */
    bool mul_ovfl_constraint::narrow_bound(solver& s, bool is_positive, 
        pdd const& p0, pdd const& q0, pdd const& p, pdd const& q) {

        if (!p.is_val())
            return false;

        SASSERT(!p.is_zero() && !p.is_one());
        auto const& max = p.manager().max_value();
        // p * q >= max + 1 <=> q >= (max + 1)/p <=> q >= ceil((max+1)/p)
        auto bound = ceil((max + 1) / p.val());

        //
        // the clause that explains bound <= q or bound > q 
        // 
        // Ovfl(p, q)  & p <= p.val() => q >= bound
        // ~Ovfl(p, q) & p >= p.val() => q < bound 
        //

        signed_constraint sc(this, is_positive);       
        signed_constraint premise = is_positive ? s.ule(p0, p.val()) : s.ule(p.val(), p0);
        signed_constraint conseq = is_positive ? s.ule(bound, q0) : s.ult(q0, bound);

        SASSERT(premise.is_currently_true(s));
        SASSERT(bound * p.val() > max);
        SASSERT((bound - 1) * p.val() <= max);
        clause_builder cb(s);
        cb.push_new(~sc);
        cb.push_new(~premise);
        cb.push_new(conseq);
        clause_ref just = cb.build();
        SASSERT(just);
        s.add_clause(*just);
        SASSERT(s.m_bvars.is_true(conseq.blit()));
        return true;
    }

    bool mul_ovfl_constraint::try_viable(
        solver& s, bool is_positive,
        pdd const& p0, pdd const& q0, pdd const& p, pdd const& q) {
        signed_constraint sc(this, is_positive);
        return s.m_viable.intersect(p0, q0, sc);
    }


    unsigned mul_ovfl_constraint::hash() const {
    	return mk_mix(p().hash(), q().hash(), kind());
    }

    bool mul_ovfl_constraint::operator==(constraint const& other) const {
        return other.is_mul_ovfl() && p() == other.to_mul_ovfl().p() && q() == other.to_mul_ovfl().q();
    }
}
