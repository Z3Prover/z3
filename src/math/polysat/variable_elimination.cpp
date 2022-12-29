/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat variable elimination

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#include "math/polysat/conflict.h"
#include "math/polysat/clause_builder.h"
#include "math/polysat/saturation.h"
#include "math/polysat/solver.h"
#include "math/polysat/variable_elimination.h"
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
        
        pdd power = get_dyadic_valuation(p).second;
        
        pvar rest = s.add_var(p.power_of_2());
        pdd rest_pdd = p.manager().mk_var(rest);
        m_rest_constants.setx(v, rest, -1);
        s.add_clause(s.eq(power * rest_pdd, p), false);
        return rest_pdd;
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
        
        pvar inv = s.add_var(p.power_of_2());
        pdd inv_pdd = p.manager().mk_var(inv);
        m_inverse_constants.setx(v, inv, -1);
        s.add_clause(s.eq(inv_pdd * p, p.manager().one()), false);
        return optional<pdd>(inv_pdd);
    }
    
#define PV_MOD 2
    
    // symbolic version of "max_pow2_divisor" for checking if it is exactly "k"
    void free_variable_elimination::add_dyadic_valuation(pvar v, unsigned k) {
        // TODO: works for all values except 0; how to deal with this case?
        pdd p = s.var(v);
        auto& m = p.manager();
        
        pvar pv;
        pvar pv2;
        bool new_var = false;
        if (m_pv_constants.size() <= v || m_pv_constants[v] == -1) {
            pv = s.add_var(m.power_of_2()); // TODO: What's a good value? Unfortunately we cannot use a integer
            pv2 = s.add_var(m.power_of_2());
            m_pv_constants.setx(v, pv, -1);
            m_pv_power_constants.setx(v, pv2, -1);
            m.mk_var(pv);
            m.mk_var(pv2);
            new_var = true;
        }
        else {
            pv = m_pv_constants[v];
            pv2 = m_pv_power_constants[v];
        }
        
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
            //if (!s.is_assigned(v))  // TODO: too restrictive. should also consider variables that will be unassigned only after backjumping (can update this after assignment handling in search state is refactored.)
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
        LOG_H3("Free Variable Elimination for v" << v << " using equation " << c);
        pdd const& p = c.eq();
        SASSERT_EQ(p.degree(v), 1);
        auto& m = p.manager();
        pdd fac = m.zero();
        pdd rest = m.zero();
        p.factor(v, 1, fac, rest);
        //if (rest.is_val()) // TODO: Why do we need this?
        //    return;
        
        SASSERT(!fac.free_vars().contains(v));
        SASSERT(!rest.free_vars().contains(v));

        LOG("fac: " << fac);
        LOG("rest: " << rest);
        
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
            if (c_target->to_ule().lhs().degree(v) > 1 || // TODO: Invert non-linear variable?
                c_target->to_ule().rhs().degree(v) > 1)
                continue;
            
            signed_constraint p1 = s.ule(m.zero(), m.zero()); 
            signed_constraint p2 = s.ule(m.zero(), m.zero());
            
            pdd new_lhs = p.manager().zero();
            pdd new_rhs = p.manager().zero();
            
            pdd fac_lhs = m.zero(); 
            pdd fac_rhs = m.zero(); 
            pdd rest_lhs = m.zero(); 
            pdd rest_rhs = m.zero(); 
            c_target->to_ule().lhs().factor(v, 1, fac_lhs, rest_lhs);
            c_target->to_ule().rhs().factor(v, 1, fac_rhs, rest_rhs);
            
            LOG_H3("With constraint " << lit_pp(s, c_target) << ":");
            LOG("c_target: " << lit_pp(s, c_target));
            LOG("fac_lhs: " << fac_lhs);
            LOG("rest_lhs: " << rest_lhs);
            LOG("fac_rhs: " << fac_rhs);
            LOG("rest_rhs: " << rest_rhs);
            
            pdd pv_equality = p.manager().zero();
            pdd lhs_multiple = p.manager().zero(); 
            pdd rhs_multiple = p.manager().zero(); 
            pdd coeff_odd = p.manager().zero();
            optional<pdd> fac_odd_inv;
            
            get_multiple_result multiple1 = get_multiple(fac_lhs, fac, new_lhs);
            get_multiple_result multiple2 = get_multiple(fac_rhs, fac, new_rhs);

            if (multiple1 == cannot_multiple || multiple2 == cannot_multiple)
                continue;

            bool evaluated = false;
            substitution sub(m);

            if (multiple1 == can_multiple || multiple2 == can_multiple) {
                if (
                        (!fac.is_val() && !fac.is_var()) ||
                        (!fac_lhs.is_val() && !fac_lhs.is_var()) ||
                        (!fac_rhs.is_val() && !fac_rhs.is_var())) {

                    // TODO: We could introduce a new variable "new_var = lc" and add the valuation for this new variable
                    if (s.is_assigned(v))
                        continue; // We could not eliminate it symbolically and evaluating makes no sense as we already have a value for it

                    pdd const fac_eval = eval(fac, core, sub);
                    LOG("fac_eval: " << fac_eval);
                    pdd fac_eval_inv = m.zero();

                    // TODO: We can now again use multiples instead of failing if it is not invertible
                    // e.g., x * y + x * z = z (with y = 0 eval)
                    // and,  3 * x * z <= 0
                    // We don't do anything, although we could
                    // x * z = z
                    // and multiplying with 3 results in a feasible replacement
                    if (!inv(fac_eval, fac_eval_inv))
                        continue;

                    LOG("fac_eval_inv: " << fac_eval_inv);

                    pdd const rest_eval = sub.apply_to(rest);
                    LOG("rest_eval: " << rest_eval);
                    pdd const vs = -rest_eval * fac_eval_inv;  // this is the polynomial that computes v
                    LOG("vs: " << vs);
                    SASSERT(!vs.free_vars().contains(v));

                    // TODO: Why was the assignment (sub) not applied to the result in previous commits?
                    new_lhs = sub.apply_to(c_target->to_ule().lhs().subst_pdd(v, vs));
                    new_rhs = sub.apply_to(c_target->to_ule().rhs().subst_pdd(v, vs));
                    evaluated = true;
                }
                else {
                    pv_equality = get_dyadic_valuation(fac).first;
                    LOG("pv_equality " << pv_equality);
                    coeff_odd = get_odd(fac); // a'
                    LOG("coeff_odd: " << coeff_odd);
                    fac_odd_inv = get_inverse(coeff_odd); // a'^-1
                    if (!fac_odd_inv)
                        continue; // factor is for sure not invertible
                    LOG("coeff_odd_inv: " << *fac_odd_inv);
                }
            }

            if (!evaluated) {
                if (multiple1 == can_multiple) {
                    pdd pv_lhs = get_dyadic_valuation(fac_lhs).first;
                    pdd odd_fac_lhs = get_odd(fac_lhs);
                    pdd power_diff_lhs = s.shl(m.one(), pv_lhs - pv_equality);

                    LOG("pv_lhs: " << pv_lhs);
                    LOG("odd_fac_lhs: " << odd_fac_lhs);
                    LOG("power_diff_lhs: " << power_diff_lhs);
                    new_lhs = -rest * *fac_odd_inv * power_diff_lhs * odd_fac_lhs + rest_lhs;
                    p1 = s.ule(get_dyadic_valuation(fac).first, get_dyadic_valuation(fac_lhs).first);
                }
                else {
                    SASSERT(multiple1 == is_multiple);
                    new_lhs = -rest * new_lhs + rest_lhs;
                }

                if (multiple2 == can_multiple) {
                    pdd pv_rhs = get_dyadic_valuation(fac_rhs).first;
                    pdd odd_fac_rhs = get_odd(fac_rhs);
                    pdd power_diff_rhs = s.shl(m.one(), pv_rhs - pv_equality);

                    LOG("pv_rhs: " << pv_rhs);
                    LOG("odd_fac_rhs: " << odd_fac_rhs);
                    LOG("power_diff_rhs: " << power_diff_rhs);
                    new_rhs = -rest * *fac_odd_inv * power_diff_rhs * odd_fac_rhs + rest_rhs;
                    p2 = s.ule(get_dyadic_valuation(fac).first, get_dyadic_valuation(fac_rhs).first);
                }
                else {
                    SASSERT(multiple2 == is_multiple);
                    new_rhs = -rest * new_rhs + rest_rhs;
                }
            }
            
            signed_constraint c_new = s.ule(new_lhs, new_rhs);
            
            if (c_target.is_negative())
                c_new.negate();
            LOG("c_new:    " << lit_pp(s, c_new));

            // New constraint is already true (maybe we already derived it previously?)
            // TODO: It might make sense to keep different derivations of the same constraint.
            //       E.g., if the new clause could derive c_new at a lower decision level.
            if (c_new.bvalue(s) == l_true)
                continue;
            
            LOG("p1:    " << p1);
            LOG("p2:    " << p2);
                        
            clause_builder cb(s);

            if (evaluated) {
                for (auto [w, wv] : sub)
                    cb.insert(~s.eq(s.var(w), wv));
            }
            cb.insert(~c);
            cb.insert(~c_target);
            cb.insert(~p1);
            cb.insert(~p2);
            cb.insert(c_new);
            ref<clause> c = cb.build();
            if (c) // Can we get tautologies this way?
                core.add_lemma("variable elimination", c);
        }
    }

    // Evaluate p under assignments in the core.
    pdd free_variable_elimination::eval(pdd const& p, conflict& core, substitution& out_sub) {
        // TODO: this should probably be a helper method on conflict.
        // TODO: recognize constraints of the form "v1 == 27" to be used in the assignment?
        //       (but maybe useful evaluations are always part of core.vars() anyway?)

        SASSERT(out_sub.empty());

        for (auto v : p.free_vars())
            if (core.contains_pvar(v))
                out_sub = out_sub.add(v, s.get_value(v));

        pdd q = out_sub.apply_to(p);
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
    
    
    free_variable_elimination::get_multiple_result free_variable_elimination::get_multiple(const pdd& p1, const pdd& p2, pdd& out) {
        LOG("Check if there is an easy way to unify " << p2 << " and " << p1);
        if (p1.is_zero()) {
            out = p1.manager().zero();
            return is_multiple;
        }
        if (p2.is_one()) {
            out = p1;
            return is_multiple;
        }
        if (!p1.is_monomial() || !p2.is_monomial())
            // TODO: Actually, this could work as well. (4a*d + 6b*c*d) is a multiple of (2a + 3b*c) although none of them is a monomial
            return can_multiple;
        dd::pdd_monomial p1m = *p1.begin();
        dd::pdd_monomial p2m = *p2.begin();
        
        unsigned tz1 = p1m.coeff.trailing_zeros();
        unsigned tz2 = p2m.coeff.trailing_zeros();
        
        if (tz2 > tz1)
            return cannot_multiple; // The constant coefficient is not invertible
        
        rational odd = div(p2m.coeff, rational::power_of_two(tz2));
        rational inv;
        bool succ = odd.mult_inverse(p1.power_of_2() - tz2, inv);
        SASSERT(succ); // we divided by the even part so it has to be odd/invertible
        inv *= div(p1m.coeff, rational::power_of_two(tz2));
        
        m_occ_cnt.reserve(s.m_vars.size(), (unsigned)0); // TODO: Are there duplicates in the list (e.g., v1 * v1)?)
        
        for (const auto& v1 : p1m.vars) {
            if (m_occ_cnt[v1] == 0)
                m_occ.push_back(v1);
            m_occ_cnt[v1]++;
        }
        for (const auto& v2 : p2m.vars) {
            if (m_occ_cnt[v2] == 0) {
                for (const auto& occ : m_occ)
                    m_occ_cnt[occ] = 0;
                m_occ.clear();
                return can_multiple; // p2 contains more v2 than p1; we need more information
            }
            m_occ_cnt[v2]--;
        }
        
        out = p1.manager().mk_val(inv);
        for (const auto& occ : m_occ) {
            for (unsigned i = 0; i < m_occ_cnt[occ]; i++)
                out *= s.var(occ);
            m_occ_cnt[occ] = 0;
        }
        m_occ.clear();
        LOG("Found multiple: " << out);
        return is_multiple;
    }
    
    unsigned parity_tracker::get_id(const pdd& p) {
        // SASSERT(p.is_var()); // For now
        // pvar v = p.var();
        unsigned id = m_pdd_to_id.get(optional(p), -1);
        if (id == -1) {
            id = m_pdd_to_id.size();
            m_pdd_to_id.insert(optional(p), id);
        }
        return id;
    }
    
    pdd parity_tracker::get_inverse(const pdd &p) {
        LOG("Getting inverse of " << p);
        if (p.is_val()) {
            SASSERT(p.val().is_odd());
            rational iv;
            VERIFY(p.val().mult_inverse(p.power_of_2(), iv));
            return p.manager().mk_val(iv);
        }
        unsigned v = get_id(p);
        if (m_inverse.size() > v && m_inverse[v] != -1)
            return s.var(m_inverse[v]);
        
        pvar inv = s.add_var(p.power_of_2());
        pdd inv_pdd = p.manager().mk_var(inv);
        m_inverse.setx(v, inv, -1);
        s.add_clause(s.eq(inv_pdd * p, p.manager().one()), false);
        return inv_pdd;
    }
    
    pdd parity_tracker::get_odd(const pdd& p, unsigned parity, svector<signed_constraint>& path) {
        LOG("Getting odd part of " << p);
        if (p.is_val()) {
            SASSERT(!p.val().is_zero());
            rational odd = machine_div(p.val(), rational::power_of_two(p.val().trailing_zeros()));
            SASSERT(odd.is_odd());
            return p.manager().mk_val(odd);
        }
        unsigned v = get_id(p);
        pvar odd_v;
        bool needs_propagate = true;
        
        if (m_odd.size() > v && m_odd[v].initialized()) {
            auto& tuple = *(m_odd[v]);
            SASSERT(tuple.second.size() == p.power_of_2());
            odd_v = tuple.first;
            needs_propagate = !tuple.second[parity];
        }
        else {
            odd_v = s.add_var(p.power_of_2());
            m_odd.setx(v, optional<std::pair<pvar, bool_vector>>({ odd_v, bool_vector(p.power_of_2(), false) }), optional<std::pair<pvar, bool_vector>>::undef());
        }
        
        m_builder.reset();
        m_builder.set_redundant(true);
        
        unsigned lower = 0, upper = p.power_of_2();
        // binary search for the parity (binary search instead of at_least_parity(p, parity) && at_most_parity(p, parity) for propagation if used with another parity
        while (lower + 1 < upper) {
            unsigned middle = (upper + lower) / 2;
            signed_constraint c = s.parity_at_least(p, middle); // constraints are anyway cached and reused
            LOG("Splitting on " << middle << " with " << parity);
            if (parity >= middle) {
                lower = middle;
                path.push_back(~c);
                if (needs_propagate)
                    m_builder.insert(~c);
            }
            else {
                upper = middle;
                path.push_back(c);
                if (needs_propagate)
                    m_builder.insert(c);
            }
            LOG("Its in [" << lower << "; " << upper << ")");
        }
        if (!needs_propagate)
            return s.var(odd_v);
        
        (*m_odd[v]).second[parity] = true;
        m_builder.insert(s.eq(rational::power_of_two(parity) * s.var(odd_v), p));
        clause_ref c = m_builder.build();
        s.add_clause(*c);
        return s.var(odd_v);
    }
    
    // a * x + b = 0 (x not in a or b; i.e., the equation is linear in x)
    // C[p, ...] resp., C[..., p]
    std::tuple<pdd, bool, svector<signed_constraint>> parity_tracker::eliminate_variable(saturation& saturation, pvar x, const pdd& a, const pdd& b, const pdd& p) {
        
        unsigned p_degree = p.degree(x);
        if (p_degree == 0)
            return { p, false, {} };
        if (a.is_val() && a.val().is_odd()) { // just invert and plug it in
            rational a_inv;
            VERIFY(a.val().mult_inverse(a.power_of_2(), a_inv));
            // this works as well if the degree of "p" is not 1: 3 x = a (mod 4) && x^2 <= b => (3a)^2 <= b
            return { p.subst_pdd(x, -b * a_inv), true, {} };
        }
        // from now on we require linear factors
        if (p_degree != 1)
            return { p, false, {} }; // TODO: Maybe fallback to brute-force
        
        pdd a1 = a.manager().zero(), b1 = a1, mul_fac = a1;
        
        p.factor(x, 1, a1, b1);
        lbool is_multiple = saturation.get_multiple(a1, a, mul_fac);
        if (is_multiple == l_false)
            return { p, false, {} }; // there is no chance to invert
        if (is_multiple == l_true) // we multiply with a factor to make them equal
            return { b1 - b * mul_fac, true, {} };
        
        #if 1
        return { p, false, {} };
        #else
        if (!a1.is_var() && !a1.is_val()) {
            //return { p, false, {} };
            LOG("Warning: Inverting " << a1 << " although it is not a single variable - might not be a good idea"); // TODO: Compromise: Maybe only monomials...?
        }
        if (!a.is_var() && !a.is_val()) {
            //return { p, false, {} };
            LOG("Warning: Inverting " << a << " although it is not a single variable - might not be a good idea");
        }
        
        if (!a.is_monomial() || !a1.is_monomial())
            return { p , false, {} };
        
        // We don't know whether it will work. Use the parity of the assignment
        
        unsigned a_parity;
        unsigned a1_parity;
        
        if ((a_parity = saturation.min_parity(a)) != saturation.max_parity(a) || (a1_parity = saturation.min_parity(a1)) != saturation.max_parity(a1))
            return { p, false, {} }; // We need the parity, but we failed to get it precisely
            
        if (a_parity > a1_parity) {
            SASSERT(false); // get_multiple should have excluded this case already
            return { p, false, {} };
        }
        
        svector<signed_constraint> precondition;
        
        auto odd_a = get_odd(a, a_parity, precondition);
        auto odd_a1 = get_odd(a1, a1_parity, precondition);
        pdd inv_odd_a = get_inverse(odd_a);
        
        LOG("Forced elimination: " << odd_a1 * inv_odd_a * rational::power_of_two(a1_parity - a_parity) * b + b1);
        verbose_stream() << "Forced elimination: " << odd_a1 * inv_odd_a * rational::power_of_two(a1_parity - a_parity) * b + b1 << "\n";
        verbose_stream() << "From: " << "eliminated v" << x << " with a = " << a << "; b = " << b << "; p = " << p << "\n";
        return { odd_a1 * inv_odd_a * rational::power_of_two(a1_parity - a_parity) * b + b1, true, {std::move(precondition)} };
#endif
    }
}
