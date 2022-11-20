/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat variable elimination

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#include "math/polysat/variable_elimination.h"
#include "math/polysat/conflict.h"
#include "math/polysat/clause_builder.h"
#include "math/polysat/solver.h"
#include <algorithm>

namespace polysat {
    
    pdd free_variable_elimination::get_odd(pdd p) {
        SASSERT(p.is_val() || p.is_var()); // For now
        
        if (p.is_val()) {
            const rational& v = p.val();
            unsigned d = v.trailing_zeros(); 
            if (!d)
                return s.sz2pdd(p.power_of_2()).mk_val(v);
            return s.sz2pdd(p.power_of_2()).mk_val(div(v, rational::power_of_two(d))); // TODO: Is there no shift?
        }
        pvar v = p.var();
        if (m_rest_constants.size() > v && m_rest_constants[v] != -1)
            return s.var(m_rest_constants[v]);
        
        get_dyadic_valuation(p);
        
        pvar rest = s.add_var(p.power_of_2());
        m_rest_constants.setx(v, rest, -1);
        s.add_clause(s.eq(s.var(m_pv_power_constants[v]) * s.var(rest), p), false);
        return s.var(rest);
    }
    
    optional<pdd> free_variable_elimination::get_inverse(pdd p) {
        SASSERT(p.is_val() || p.is_var()); // For now
        
        if (p.is_val()) {
            pdd i = s.sz2pdd(p.power_of_2()).zero();
            if (!inv(p, i))
                return {};
            return optional<pdd>(i);
        }
        pvar v = p.var();
        if (m_inverse_constants.size() > v && m_inverse_constants[v] != -1)
            return optional<pdd>(s.var(m_inverse_constants[v]));
        
        pvar inv = s.add_var(s.var(v).power_of_2());
        m_inverse_constants.setx(v, inv, -1);
        s.add_clause(s.eq(s.var(inv) * s.var(v), s.sz2pdd(s.var(v).power_of_2()).one()), false);
        return optional<pdd>(s.var(inv));
    }
    
    // symbolic version of "max_pow2_divisor" for checking if it is exactly "k"
    void free_variable_elimination::add_dyadic_valuation(pvar v, unsigned k) {
        pvar pv;
        pvar pv2;
        if (m_pv_constants.size() <= v || m_pv_constants[v] == -1) {
            pv = s.add_var(s.var(v).power_of_2()); // TODO: What's a good value? Unfortunately we cannot use a integer
            pv2 = s.add_var(s.var(v).power_of_2());
            m_pv_constants.setx(v, pv, -1);
            m_pv_power_constants.setx(v, pv2, -1);
        }
        else {
            pv = m_pv_constants[v];
            pv2 = m_pv_power_constants[v];
        }
        
        // (pv = k && pv2 = 2^k) <==> ((v & (2^(k + 1) - 1)) = 2^k) 
        
        rational mask = rational::power_of_two(k + 1) - 1;
        pdd masked = s.band(s.var(v), s.sz2pdd(s.var(v).power_of_2()).mk_val(mask));
        std::pair<pdd, pdd> odd_part = s.quot_rem(s.var(v), s.var(pv2));
        
        signed_constraint c1 = s.eq(s.var(pv), k);
        signed_constraint c2 = s.eq(s.var(pv2), rational::power_of_two(k));
        signed_constraint c3 = s.eq(masked, rational::power_of_two(k));
        bool e = get_log_enabled();
        set_log_enabled(false);
        s.add_clause(c1, ~c3, false);
        s.add_clause(c2, ~c3, false);
        s.add_clause(~c1, ~c2, c3, false);
        
        s.add_clause(s.eq(odd_part.second, 0), false); // The division has to be exact
        set_log_enabled(e);
    }
    
    std::pair<pdd, pdd> free_variable_elimination::get_dyadic_valuation(pdd p, unsigned short lower, unsigned short upper) {
        SASSERT(p.is_val() || p.is_var()); // For now
        
        if (p.is_val()) {
            rational pv(p.val().trailing_zeros());
            rational pv2 = rational::power_of_two(p.val().trailing_zeros());
            return { s.sz2pdd(p.power_of_2()).mk_val(pv), s.sz2pdd(p.power_of_2()).mk_val(pv2) };
        }
        
        pvar v = p.var();
        unsigned short prev_lower = 0, prev_upper = 0;
        if (m_has_validation_of_range.size() > v) {
            unsigned range = m_has_validation_of_range[v];
            prev_lower = range & 0xFFFF;
            prev_upper = range >> 16;
            if (lower >= prev_lower && upper <= prev_upper)
                return { s.var(m_pv_constants[v]), s.var(m_pv_power_constants[v]) }; // exists already in the required range
        }
        LOG("Adding valuation function for variable " << v  << " in [" << lower << "; " << upper << ")");
        m_has_validation_of_range.setx(v, lower | (unsigned)upper << 16, 0);
        for (unsigned i = lower; i < prev_lower; i++) {
            add_dyadic_valuation(v, i);
        }
        for (unsigned i = prev_upper; i < upper; i++) {
            add_dyadic_valuation(v, i);
        }
        return { s.var(m_pv_constants[v]), s.var(m_pv_power_constants[v]) };
    }
    
    std::pair<pdd, pdd> free_variable_elimination::get_dyadic_valuation(pdd p) {
        return get_dyadic_valuation(p, 0, p.power_of_2()); 
    }

    void free_variable_elimination::find_lemma(conflict& core) {
        LOG_H1("Free Variable Elimination");
        LOG("core: " << core);
        LOG("Free variables: " << s.m_free_pvars);
        for (pvar v : core.vars_occurring_in_constraints())
            if (!s.is_assigned(v))  // TODO: too restrictive. should also consider variables that will be unassigned only after backjumping (can update this after assignment handling in search state is refactored.)
                find_lemma(v, core);
    }

    void free_variable_elimination::find_lemma(pvar v, conflict& core) {
        LOG_H2("Free Variable Elimination for v" << v);
        // find constraint that allows computing v from other variables
        // (currently, consider only equations that contain v with degree 1)
        for (signed_constraint c : core) {
            if (!c.is_eq())
                continue;
            if (c.eq().degree(v) != 1)
                continue;
            find_lemma(v, c, core);
        }
    }

    void free_variable_elimination::find_lemma(pvar v, signed_constraint c, conflict& core) {
        vector<signed_constraint> to_check;
        // Find another constraint where we want to substitute v
        for (signed_constraint c_target : core) {
            if (c == c_target)
                continue;
            if (c_target.vars().size() <= 1)
                continue;
            if (!c_target.contains_var(v))
                continue;
            // TODO: helper method constraint::subst(pvar v, pdd const& p)
            //       (or rather, add it on constraint_manager since we need to allocate/dedup the new constraint)
            //  For now, just restrict to ule_constraint.
            if (!c_target->is_ule()) // TODO: Remove?
                continue;
            // TODO: Eliminate without inversion? 2x = y && 2x <= z
            
            to_check.push_back(c_target);
        }
        if (to_check.empty())
            return;
        
        LOG_H3("Free Variable Elimination for v" << v << " using equation " << c);
        pdd const& p = c.eq();
        SASSERT_EQ(p.degree(v), 1);
        auto& m = p.manager();
        pdd lc = m.zero();
        pdd rest = m.zero();
        p.factor(v, 1, lc, rest);
        if (rest.is_val())
            return;
        // lc * v + rest == p == 0
        // v == -1 * rest * lc^-1

        SASSERT(!lc.free_vars().contains(v));
        SASSERT(!rest.free_vars().contains(v));

        LOG("lc: " << lc);
        LOG("rest: " << rest);

        //pdd rs = rest;
        
        if (!lc.is_val() && lc.is_var())
            // TODO: We could introduce a new variable "new_var = lc" and add the valuation for this new variable
            return;
        
        pdd coeff_odd = get_odd(lc); // a'
        optional<pdd> lci = get_inverse(coeff_odd); // a'^-1
        if (!lci)
            return; // For sure not invertible
        
        LOG("lci: " << lci);
        
        /*assignment_t a;
        pdd const lcs = eval(lc, core, a);
        LOG("lcs: " << lcs);
        pdd lci = m.zero();
        if (!inv(lcs, lci))
            return;
            
        pdd lci = m.zero();

        pdd const rs = s.subst(a, rest);
        */
        
        /*pdd const vs = -rs * lci;  // this is the polynomial that computes v
        LOG("vs: " << vs);
        SASSERT(!vs.free_vars().contains(v));*/

        // Find another constraint where we want to substitute v
        for (signed_constraint c_target : to_check) {
            
            // Move the variable to eliminate to one side
            pdd fac = m.zero(); 
            pdd fac2 = m.zero(); 
            pdd rest2 = m.zero(); 
            pdd rest3 = m.zero(); 
            c_target->to_ule().lhs().factor(v, 1, fac, rest2);
            c_target->to_ule().rhs().factor(v, 1, fac2, rest3);
            
            rest2 = rest3 - rest2;
            fac = fac - fac2;
            
            LOG("c_target: " << lit_pp(s, c_target));
            LOG("fac: " << fac);
            LOG("rest2: " << rest2);
            
            if (!fac.is_val() && !fac.is_var())
                return; // TODO: Again, we might bind this to a variable
            
            pdd pv2 = get_dyadic_valuation(fac).first;
            pdd pv1 = get_dyadic_valuation(lc).first;  
            pdd odd_fac = get_odd(fac);
            pdd power_diff = s.shl(m.one(), pv2 - pv1);
            
            LOG("pv2: " << pv2);
            LOG("pv1: " << pv1);
            LOG("odd_fac: " << odd_fac);
            LOG("power_diff: " << power_diff);
            
            signed_constraint c_new = s.ule(-rest * lci * power_diff * odd_fac, rest2);
            if (c_target.is_negative())
                c_new.negate();
            LOG("c_new:    " << lit_pp(s, c_new));

            // New constraint is already true (maybe we already derived it previously?)
            // TODO: It might make sense to keep different derivations of the same constraint.
            //       E.g., if the new clause could derive c_new at a lower decision level.
            if (c_new.bvalue(s) == l_true)
                continue;

            clause_builder cb(s);
            /*for (auto [w, wv] : a)
                cb.push(~s.eq(s.var(w), wv));*/
            cb.insert(~c);
            cb.insert(~c_target);
            cb.insert(~s.ule(get_dyadic_valuation(lc).first, get_dyadic_valuation(fac).first));
            cb.insert(c_new);
            ref<clause> c = cb.build();
            if (c) // Can we get tautologies this way?
                core.add_lemma(c);
        }
    }

    // Evaluate p under assignments in the core.
    pdd free_variable_elimination::eval(pdd const& p, conflict& core, assignment_t& out_assignment) {
        // TODO: this should probably be a helper method on conflict.
        // TODO: recognize constraints of the form "v1 == 27" to be used in the assignment?
        //       (but maybe useful evaluations are always part of core.vars() anyway?)

        assignment_t& a = out_assignment;
        SASSERT(a.empty());

        for (auto v : p.free_vars())
            if (core.contains_pvar(v))
                a.push_back({v, s.get_value(v)});

        pdd q = s.subst(a, p);

        // TODO: like in the old conflict::minimize_vars, we can now try to remove unnecessary variables from a.

        return q;
    }

    // Compute the multiplicative inverse of p.
    bool free_variable_elimination::inv(pdd const& p, pdd& out_p_inv) {
        // TODO: in the non-val case, we could introduce an additional variable to represent the inverse
        //       (and a constraint p * p_inv == 1)
        if (!p.is_val())
            return false;
        rational iv;
        if (!p.val().mult_inverse(p.power_of_2(), iv))
            return false;
        out_p_inv = p.manager().mk_val(iv);
        return true;
    }

}
