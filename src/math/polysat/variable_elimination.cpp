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
    
    pdd free_variable_elimination::get_hamming_distance(pdd p) {
        SASSERT(p.power_of_2() >= 8); // TODO: Implement special cases for smaller bit-width
        // The trick works only for multiples of 8 (because of the final multiplication).
        // Maybe it can be changed to work for all sizes
        SASSERT(p.power_of_2() % 8 == 0); 
        
        // Proven for 8, 16, 24, 32 by bit-blasting in Z3
        
        // https://en.wikipedia.org/wiki/Hamming_weight
        const unsigned char pattern_55 = 0x55; // 01010101
        const unsigned char pattern_33 = 0x33; // 00110011
        const unsigned char pattern_0f = 0x0f; // 00001111
        const unsigned char pattern_01 = 0x01; // 00000001
        
        unsigned to_alloc = (p.power_of_2() + sizeof(unsigned) - 1) / sizeof(unsigned);
        unsigned to_alloc_bits = to_alloc * sizeof(unsigned);
        
        // Cache this?
        auto* scaled_55 = (unsigned*)alloca(to_alloc_bits);
        auto* scaled_33 = (unsigned*)alloca(to_alloc_bits);
        auto* scaled_0f = (unsigned*)alloca(to_alloc_bits);
        auto* scaled_01 = (unsigned*)alloca(to_alloc_bits);
        
        memset(scaled_55, pattern_55, to_alloc_bits);
        memset(scaled_33, pattern_33, to_alloc_bits);
        memset(scaled_0f, pattern_0f, to_alloc_bits);
        memset(scaled_01, pattern_01, to_alloc_bits);
        
        rational rational_scaled_55(scaled_55, to_alloc);
        rational rational_scaled_33(scaled_33, to_alloc);
        rational rational_scaled_0f(scaled_0f, to_alloc);
        rational rational_scaled_01(scaled_01, to_alloc);
        
        auto& m = p.manager();
        
        pdd w = p - s.band(s.lshr(p, m.one()), m.mk_val(rational_scaled_55));
        w = s.band(w, m.mk_val(rational_scaled_33)) + s.band(s.lshr(w, m.mk_val(2)), m.mk_val(rational_scaled_33));
        w = s.band(w + s.lshr(w, m.mk_val(4)), m.mk_val(rational_scaled_0f));
        //unsigned final_shift = p.power_of_2() - 8;
        //final_shift = (final_shift + 7) / 8 * 8 - 1; // ceil final_shift to the next multiple of 8
        return s.lshr(w * m.mk_val(rational_scaled_01), m.mk_val(p.power_of_2() - 8));
    }
    
    pdd free_variable_elimination::get_odd(pdd p) {
        SASSERT(p.is_val() || p.is_var()); // For now
        
        if (p.is_val()) {
            const rational& v = p.val();
            unsigned d = v.trailing_zeros(); 
            if (!d)
                return p.manager().mk_val(v);
            return p.manager().mk_val(div(v, rational::power_of_two(d))); // TODO: Is there no shift?
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
            pdd i = p.manager().zero();
            if (!inv(p, i))
                return {};
            return optional<pdd>(i);
        }
        pvar v = p.var();
        if (m_inverse_constants.size() > v && m_inverse_constants[v] != -1)
            return optional<pdd>(s.var(m_inverse_constants[v]));
        
        pvar inv = s.add_var(s.var(v).power_of_2());
        m_inverse_constants.setx(v, inv, -1);
        s.add_clause(s.eq(s.var(inv) * s.var(v), p.manager().one()), false);
        return optional<pdd>(s.var(inv));
    }
    
#define PV_MOD 2
    
    // symbolic version of "max_pow2_divisor" for checking if it is exactly "k"
    void free_variable_elimination::add_dyadic_valuation(pvar v, unsigned k) {
        // TODO: works for all values except 0; how to deal with this case?
        pvar pv;
        pvar pv2;
        bool new_var = false;
        if (m_pv_constants.size() <= v || m_pv_constants[v] == -1) {
            pv = s.add_var(s.var(v).power_of_2()); // TODO: What's a good value? Unfortunately we cannot use a integer
            pv2 = s.add_var(s.var(v).power_of_2());
            m_pv_constants.setx(v, pv, -1);
            m_pv_power_constants.setx(v, pv2, -1);
            new_var = true;
        }
        else {
            pv = m_pv_constants[v];
            pv2 = m_pv_power_constants[v];
        }
        
        pdd p = s.var(v);
        auto& m = p.manager();
        
        bool e = get_log_enabled();
        set_log_enabled(false);

        // For testing some different implementations
#if PV_MOD == 1
        // brute-force bit extraction and <=
        signed_constraint c1 = s.eq(rational::power_of_two(p.power_of_2() - k - 1) * p, m.zero());
        signed_constraint c2 = s.ule(m.mk_val(k), s.var(pv));
        s.add_clause(~c1, c2, false);
        s.add_clause(c1, ~c2, false);
        
        if (new_var) {
            s.add_clause(s.eq(s.var(pv2), s.shl(m.one(), s.var(pv))), false);
        }
#elif PV_MOD == 2
        // symbolic "maximal divisible"
        signed_constraint c1 = s.eq(s.shl(s.lshr(p, s.var(pv)), s.var(pv)), p);
        signed_constraint c2 = ~s.eq(s.shl(s.lshr(p, s.var(pv + 1)), s.var(pv + 1)), p);
        
        signed_constraint z = ~s.eq(p, p.manager().zero());
        
        // v != 0 ==> [(v >> pv) << pv == v && (v >> pv + 1) << pv + 1 != v]
        s.add_clause(~z, c1, false);
        s.add_clause(~z, c2, false);
        
        if (new_var) {
            s.add_clause(s.eq(s.var(pv2), s.shl(m.one(), s.var(pv))), false);
        }
#elif PV_MOD == 3
        // computing the complete function by hamming-distance
        // proven equivalent with case 2 via bit-blasting for small sizes
        s.add_clause(s.eq(s.var(pv), get_hamming_distance(s.bxor(p, p - 1)) - 1), false);
        
        // in case v == 0 ==> pv == k - 1 (we don't care)
        
        if (new_var) {
            s.add_clause(s.eq(s.var(pv2), s.shl(m.one(), s.var(pv))), false);
        }
#elif PV_MOD == 4
        // brute-force bit-and
        // (pv = k && pv2 = 2^k) <==> ((v & (2^(k + 1) - 1)) = 2^k) 
        
        rational mask = rational::power_of_two(k + 1) - 1;
        pdd masked = s.band(s.var(v), s.var(v).manager().mk_val(mask));
        std::pair<pdd, pdd> odd_part = s.quot_rem(s.var(v), s.var(pv2));
        
        signed_constraint c1 = s.eq(s.var(pv), k);
        signed_constraint c2 = s.eq(s.var(pv2), rational::power_of_two(k));
        signed_constraint c3 = s.eq(masked, rational::power_of_two(k));
        
        s.add_clause(c1, ~c3, false);
        s.add_clause(c2, ~c3, false);
        s.add_clause(~c1, ~c2, c3, false);
        
        s.add_clause(s.eq(odd_part.second, 0), false); // The division has to be exact
#endif
        
        set_log_enabled(e);
    }
    
    std::pair<pdd, pdd> free_variable_elimination::get_dyadic_valuation(pdd p, unsigned short lower, unsigned short upper) {
        SASSERT(p.is_val() || p.is_var()); // For now
        SASSERT(lower == 0);
        SASSERT(upper == p.power_of_2()); // Maybe we don't need all. However, for simplicity have this now
        
        if (p.is_val()) {
            rational pv(p.val().trailing_zeros());
            rational pv2 = rational::power_of_two(p.val().trailing_zeros());
            return { p.manager().mk_val(pv), p.manager().mk_val(pv2) };
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
#if PV_MOD == 2 || PV_MOD == 3
        LOG("Adding valuation function for variable " << v);
        add_dyadic_valuation(v, 0);
        m_has_validation_of_range.setx(v, (unsigned)UCHAR_MAX << 16, 0);
#else
        LOG("Adding valuation function for variable " << v  << " in [" << lower << "; " << upper << ")");
        m_has_validation_of_range.setx(v, lower | (unsigned)upper << 16, 0);
        for (unsigned i = lower; i < prev_lower; i++) {
            add_dyadic_valuation(v, i);
        }
        for (unsigned i = prev_upper; i < upper; i++) {
            add_dyadic_valuation(v, i);
        }
#endif
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
            if (c_target->to_ule().lhs().degree(v) > 1 || // TODO: Invert non-linear parts?
                c_target->to_ule().rhs().degree(v) > 1)
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
        
        if (!lc.is_val() && !lc.is_var())
            // TODO: We could introduce a new variable "new_var = lc" and add the valuation for this new variable
            return;
        
        pdd coeff_odd = get_odd(lc); // a'
        
        LOG("coeff_odd: " << coeff_odd);
        
        optional<pdd> coeff_odd_inv = get_inverse(coeff_odd); // a'^-1
        if (!coeff_odd_inv)
            return; // For sure not invertible
        
        LOG("coeff_odd_inv: " << *coeff_odd_inv);
        
        // Find another constraint where we want to substitute v
        for (signed_constraint c_target : to_check) {
            
            // Move the variable to eliminate to one side
            pdd fac_lhs = m.zero(); 
            pdd fac_rhs = m.zero(); 
            pdd rest_lhs = m.zero(); 
            pdd rest_rhs = m.zero(); 
            c_target->to_ule().lhs().factor(v, 1, fac_lhs, rest_lhs);
            c_target->to_ule().rhs().factor(v, 1, fac_rhs, rest_rhs);
            
            LOG("c_target: " << lit_pp(s, c_target));
            LOG("c_target (lhs): " << c_target->to_ule().lhs());
            LOG("c_target (rhs): " << c_target->to_ule().rhs());
            LOG("fac_lhs: " << fac_lhs);
            LOG("rest_lhs: " << rest_lhs);
            LOG("fac_rhs: " << fac_rhs);
            LOG("rest_rhs: " << rest_rhs);
            
            if (!fac_lhs.is_val() && !fac_lhs.is_var())
                return; // TODO: Again, we might bind this to a variable
            if (!fac_rhs.is_val() && !fac_rhs.is_var())
                return;
            // TODO: Maybe only replace one side if the other is not invertible...
            
            pdd pv_equality = get_dyadic_valuation(lc).first;
            pdd pv_lhs = get_dyadic_valuation(fac_lhs).first;
            pdd pv_rhs = get_dyadic_valuation(fac_rhs).first;
            
            pdd odd_fac_lhs = get_odd(fac_lhs);
            pdd odd_fac_rhs = get_odd(fac_rhs);
            pdd power_diff_lhs = s.shl(m.one(), pv_lhs - pv_equality);
            pdd power_diff_rhs = s.shl(m.one(), pv_rhs - pv_equality);
            
            LOG("pv_equality " << pv_equality);
            LOG("pv_lhs: " << pv_lhs);
            LOG("odd_fac_lhs: " << odd_fac_lhs);
            LOG("power_diff_lhs: " << power_diff_lhs);
            LOG("pv_rhs: " << pv_rhs);
            LOG("odd_fac_rhs: " << odd_fac_rhs);
            LOG("power_diff_rhs: " << power_diff_rhs);
            
            signed_constraint c_new = s.ule(
                    -rest * *coeff_odd_inv * power_diff_lhs * odd_fac_lhs + rest_lhs,
                    -rest * *coeff_odd_inv * power_diff_rhs * odd_fac_rhs + rest_rhs);
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
            cb.insert(~s.ule(get_dyadic_valuation(lc).first, get_dyadic_valuation(fac_lhs).first));
            cb.insert(~s.ule(get_dyadic_valuation(lc).first, get_dyadic_valuation(fac_rhs).first));
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
