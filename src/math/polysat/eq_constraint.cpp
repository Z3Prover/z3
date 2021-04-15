/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat eq_constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/

#include "math/polysat/constraint.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"

namespace polysat {

    std::ostream& eq_constraint::display(std::ostream& out) const {
        return out << p() << " == 0";
    }

    bool eq_constraint::propagate(solver& s, pvar v) {
        LOG_H3("Propagate " << s.m_vars[v] << " in " << *this);
        SASSERT(!vars().empty());
        auto var = s.m_vars[v].var();
        unsigned idx = 0;
        if (vars()[idx] != v)
            idx = 1;
        SASSERT(v == vars()[idx]);
        // find other watch variable.
        for (unsigned i = vars().size(); i-- > 2; ) {
            if (!s.is_assigned(vars()[i])) {
                std::swap(vars()[idx], vars()[i]);
                return true;
            }
        }        
        

        LOG("Assignments: " << s.m_search);
        auto q = p().subst_val(s.m_search);
        LOG("Substituted: " << p() << " := " << q);
        TRACE("polysat", tout << p() << " := " << q << "\n";);
        if (q.is_zero()) 
            return false;
        if (q.is_never_zero()) {
            LOG("Conflict (never zero under current assignment)");
            // we could tag constraint to allow early substitution before 
            // swapping watch variable in case we can detect conflict earlier.
            s.set_conflict(*this);
            return false;
        }

        // at most one variable remains unassigned.
        auto other_var = vars()[1 - idx];

        // Detect and apply unit propagation.
            
        if (!q.is_linear())
            return false;

        // a*x + b == 0
        rational a = q.hi().val();
        rational b = q.lo().val();
        rational inv_a;
        if (a.is_odd()) {
            // v1 = -b * inverse(a)
            unsigned sz = q.power_of_2();
            VERIFY(a.mult_inverse(sz, inv_a)); 
            rational val = mod(inv_a * -b, rational::power_of_two(sz));
            s.m_cjust[other_var].push_back(this);
            s.propagate(other_var, val, *this);
            return false;
        }

        SASSERT(!b.is_odd());  // otherwise p.is_never_zero() would have been true above

        // TBD
        // constrain viable using condition on x
        // 2*x + 2 == 0 mod 4 => x is odd
        //
        // We have:
        // 2^j*a'*x + 2^j*b' == 0 mod m, where a' is odd (but not necessarily b')
        // <=> 2^j*(a'*x + b') == 0 mod m
        // <=> a'*x + b' == 0 mod (m-j)
        // <=> x == -b' * inverse_{m-j}(a') mod (m-j)
        // ( <=> 2^j*x == 2^j * -b' * inverse_{m-j}(a') mod m )
        //
        // x == c mod (m-j)
        // Which x in 2^m satisfy this?
        // => x \in { c + k * 2^(m-j) | k = 0, ..., 2^j - 1 }
        unsigned rank_a = a.trailing_zeros();  // j
        SASSERT(b == 0 || rank_a <= b.trailing_zeros());
        rational aa = a / rational::power_of_two(rank_a);  // a'
        rational bb = b / rational::power_of_two(rank_a);  // b'
        rational inv_aa;
        unsigned small_sz = q.power_of_2() - rank_a;  // m - j
        VERIFY(aa.mult_inverse(small_sz, inv_aa));
        rational cc = mod(inv_aa * -bb, rational::power_of_two(small_sz));
        LOG(m_vars[other_var] << " = " << cc << " + k * 2^" << small_sz);
        // TODO: better way to update the BDD, e.g. construct new one (only if rank_a is small?)
        vector<rational> viable;
        for (rational k = rational::zero(); k < rational::power_of_two(rank_a); k += 1) {
            rational val = cc + k * rational::power_of_two(small_sz);
            viable.push_back(val);
        }
        LOG_V("still viable: " << viable);
        unsigned i = 0;
        for (rational r = rational::zero(); r < rational::power_of_two(q.power_of_2()); r += 1) {
            while (i < viable.size() && viable[i] < r)
                ++i;
            if (i < viable.size() && viable[i] == r)
                continue;
            if (s.is_viable(other_var, r)) {
                s.add_non_viable(other_var, r);
            }
        }

        LOG("TODO");
        
        return false;
    }

    constraint* eq_constraint::resolve(solver& s, pvar v) {
        if (s.m_conflict.size() != 1)
            return nullptr;
        constraint* c = s.m_conflict[0];
        if (c->is_eq()) {
            pdd a = c->to_eq().p();
            pdd b = p();
            pdd r = a;
            if (!a.resolve(v, b, r)) 
                return nullptr;
            p_dependency_ref d(s.m_dm.mk_join(c->dep(), dep()), s.m_dm);
            // d = ;
            unsigned lvl = std::max(c->level(), level());
            return constraint::eq(lvl, r, d);             
        }
        return nullptr;
    }

    bool eq_constraint::is_always_false() {
        return p().is_never_zero();
    }

    bool eq_constraint::is_currently_false(solver& s) {
        pdd r = p().subst_val(s.m_search);
        return r.is_never_zero();
    }

}
