/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    fixed_bits

Abstract:

    Associates every pdd with the set of already fixed bits and justifications for this

--*/

#include "math/polysat/fixed_bits.h"
#include "math/polysat/solver.h"

namespace polysat {
    
    bit_justication* bit_justication::get_other_justification(const fixed_bits& fixed, const pdd& p, unsigned idx) {
        return fixed.m_tbv_to_justification[{ p, idx }];
    }
    
    const tbv_ref& bit_justication::get_tbv(fixed_bits& fixed, const pdd& p) {
        return fixed.get_tbv(p);
    }
    
    bool bit_justication::fix_value(fixed_bits& fixed, const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication* j) {
        return fixed.fix_value(p, tbv, idx, val, j);
    }
    
    void bit_justication_constraint::get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) {
        for (const auto& dep : this->m_dependencies)
            to_process.push_back(dep);
    }
    
    bit_justication_constraint* bit_justication_constraint::mk_justify_at_least(constraint *c, const pdd& v, const tbv_ref& tbv, const rational& least) {
        return mk_justify_between(c, v, tbv, least, rational::power_of_two(tbv.num_tbits()) - 1); 
    }
    
    bit_justication_constraint* bit_justication_constraint::mk_justify_at_most(constraint *c, const pdd& v, const tbv_ref& tbv, const rational& most) { 
        return mk_justify_between(c, v, tbv, rational::zero(), most); 
    }
    
    bit_justication_constraint* bit_justication_constraint::mk_justify_between(constraint *c, const pdd& v, const tbv_ref& tbv, rational least, rational most) {
        SASSERT(least.is_nonneg());
        SASSERT(most.is_nonneg());
        
        most = power(rational(2), tbv.num_tbits()) - most;
        bit_dependencies dep;
        for (unsigned i = tbv.num_tbits(); i > 0; i--) {
            tbit b = tbv[i];
            if (b == BIT_0 || b == BIT_1) {
                (b == BIT_0 ? most : least) -= power(rational(2), i - 1);
                dep.push_back({ v, i });
            }
            if (most.is_nonpos() && least.is_nonpos())
                return alloc(bit_justication_constraint, c, std::move(dep));
        }
        
        SASSERT(most.is_pos() || least.is_pos());
        VERIFY(false); // we assume that the possible values are indeed in [least; most]
        return nullptr;
    }
    
    // multiplication: (1*p0 + 2*p1 + 4*p2 + 8*p3 + ...) * (1*q0 + 2*q1 + 4*q2 + 8*q3 + ...) =
    // = 1 * (p0 q0) + 2 * (p0 q1 + p1 q0) + 4 * (p0 q2 + p1 q1 + p2 q0) + 8 * (p0 q3 + p1 q2 + p2 q1 + p3 q0) + ...
    // that means
    // r0 = (p0 q0) 
    // r1 = (p0 q1 + p1 q0) + (p0 q0) / 2 = (p0 q1 + p1 q0)
    // r2 = (p0 q2 + p1 q1 + p2 q0) + (p0 q1 + p1 q0) / 2 + (p0 q0) / 4 = (p0 q2 + p1 q1 + p2 q0) + (p0 q1 + p1 q0) / 2 
    // r3 = (p0 q3 + p1 q2 + p2 q1 + p3 q0) + (p0 q2 + p1 q1 + p2 q0) / 2 + (p0 q1 + p1 q0) / 4 + (p0 q0) / 8 = (p0 q3 + p1 q2 + p2 q1 + p3 q0) + (p0 q2 + p1 q1 + p2 q0) / 2 
    tbv_ref& bit_justication_mul::mul(fixed_bits& fixed, const pdd& p, const tbv_ref& in1, const tbv_ref& in2) {
        auto m = in1.manager();
        tbv_ref& out = fixed.get_tbv(p);
        
        unsigned min_bit_value = 0; // The value of the current bit assuming all unknown bits are 0
        unsigned max_bit_value = 0; // The value of the current bit assuming all unknown bits are 1
    
        // TODO: Check: Is the performance too worse? It is O(k^2)
        for (unsigned i = 0; i < m.num_tbits(); i++) {
            for (unsigned x = 0, y = i; x <= i; x++, y--) {
                tbit bit1 = in1[x];
                tbit bit2 = in2[y];
    
                if (bit1 == BIT_1 && bit2 == BIT_1) {
                    min_bit_value++; // we get two 1
                    max_bit_value++;
                }
                else if (bit1 != BIT_0 && bit2 != BIT_0) {
                    max_bit_value++; // we could get two 1
                }
            }
            if (min_bit_value == max_bit_value) {
                // We know the value of this bit
                if (!fix_value(fixed, p, out, i, min_bit_value & 1 ? BIT_1 : BIT_0, alloc(bit_justication_mul)))
                    return out;
            }
            // Subtract one; shift this to the next higher bit as "carry value"
            min_bit_value >>= 1;
            max_bit_value >>= 1;
        }

        return out;
    }    
    
    // collect all bits that effect the given bit. These might be quite a lot
    // We need to know how many previous bits are relevant
    // r0 = (p0 q0) ... 0 overflow candidates
    // r1 = (p0 q1 + p1 q0) + (p0 q0) / 2 = (p0 q1 + p1 q0) ... 0 overflow candidates
    // r2 = (p0 q2 + p1 q1 + p2 q0) + (p0 q1 + p1 q0) / 2 + (p0 q0) / 4 = (p0 q2 + p1 q1 + p2 q0) + (p0 q1 + p1 q0) / 2 ... 1 overflow candidates
    // ...
    // r5 = ([6]) + ([5]) / 2 + ([4]) / 4 + ([3]) / 8 + ([2]) / 16 + ([1]) / 32 = ([6]) + ([5]) / 2 + ([4]) / 4 ... 2 overflow candidates
    // ...
    // r12 = ([11]) + ([10]) / 2 + ([9]) / 4 + ([8]) / 8 ... 3 overflow candidates
    // ...
    // r21 = ([20]) + ([19]) / 2 + ([18]) / 4 + ([17]) / 8 + ([16]) / 16 ... 4 overflow candidates
    // ...
    // r38 = ([37]) + ([36]) / 2 + ([35]) / 4 + ([34]) / 8 + ([33]) / 16 + ([32]) / 32 ... 5 overflow candidates
    // ...
    // r71 =  ... 6 overflow candidates
    // ...
    // the overflow increases on { 2, 5, 12, 21, 21, 38, 71, ... } that is 2^k + idx + 1 = 2^idx
    // Hence we can calculate it by "ilog2(idx - ilog2(idx) - 1)" if idx >= 7 or otherwise use the lookup table [0, 0, 1, 1, 1, 1, 1] (as the intermediate result is negative)
    void bit_justication_mul::get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) {
        unsigned relevant_range; // the number of previous places that might overflow to this bit 
        if (m_idx < 7)
            relevant_range = m_idx >= 2;
        else
            relevant_range = log2(m_idx - (log2(m_idx) + 1));
        
        const tbv_ref& tbv1 = get_tbv(fixed, *m_c1);
        const tbv_ref& tbv2 = get_tbv(fixed, *m_c2);
                        
        for (unsigned i = m_idx - relevant_range; i <= m_idx; i++) {
            for (unsigned x = 0, y = i; x <= i; x++, y--) {
                tbit bit1 = tbv1[x];
                tbit bit2 = tbv2[y];
                
                if (bit1 == BIT_1 && bit2 == BIT_1) {
                    get_other_justification(fixed, *m_c1, x)->get_dependencies(fixed, to_process);
                    get_other_justification(fixed, *m_c2, x)->get_dependencies(fixed, to_process);
                }
                else if (bit1 == BIT_0) // TODO: Take the better one if both are zero
                    get_other_justification(fixed, *m_c1, x)->get_dependencies(fixed, to_process);
                else if (bit2 == BIT_0)
                    get_other_justification(fixed, *m_c2, x)->get_dependencies(fixed, to_process);
                else {
                    // The bit is apparently not set because we cannot derive a truth-value.
                    // Why do we ask for an explanation
                    VERIFY(false);
                }
            }
        }
    }
    
    // similar to multiplying but far simpler/faster (only the direct predecessor might overflow)
    tbv_ref& bit_justication_add::add(fixed_bits& fixed, const pdd& p, const tbv_ref& in1, const tbv_ref& in2) {
        auto m = in1.manager();
        tbv_ref& out = fixed.get_tbv(p);

        unsigned min_bit_value = 0;
        unsigned max_bit_value = 0;

        for (unsigned i = 0; i < m.num_tbits(); i++) {
            tbit bit1 = in1[i];
            tbit bit2 = in2[i];
            if (bit1 == BIT_1 && bit2 == BIT_1) {
                min_bit_value++;
                max_bit_value++;
            }
            else if (bit1 != BIT_0 && bit2 != BIT_0) {
                max_bit_value++;
            }

            if (min_bit_value == max_bit_value)
                if (!fix_value(fixed, p, out, i, min_bit_value & 1 ? BIT_1 : BIT_0, alloc(bit_justication_add)))
                    return out;

            min_bit_value >>= 1;
            max_bit_value >>= 1;
        }
        
        if (min_bit_value == max_bit_value) // Overflow to the first bit
            fix_value(fixed, p, out, 0, min_bit_value & 1 ? BIT_1 : BIT_0, alloc(bit_justication_add));
        
        return out;
    }
    
    void bit_justication_add::get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) {
        if (m_c1->power_of_2() > 1) {
            if (m_idx == 0) {
                get_other_justification(fixed, *m_c1, m_c1->power_of_2() - 1)->get_dependencies(fixed, to_process);
                get_other_justification(fixed, *m_c2, m_c1->power_of_2() - 1)->get_dependencies(fixed, to_process);
                DEBUG_CODE(
                    const tbv_ref& tbv1 = get_tbv(fixed, *m_c1);
                    const tbv_ref& tbv2 = get_tbv(fixed, *m_c2);
                    SASSERT(tbv1[m_c1->power_of_2() - 1] != BIT_z && tbv2[m_c1->power_of_2() - 1] != BIT_z);
                );
            }
            else {
                get_other_justification(fixed, *m_c1, m_idx - 1)->get_dependencies(fixed, to_process);
                get_other_justification(fixed, *m_c2, m_idx - 1)->get_dependencies(fixed, to_process);
                DEBUG_CODE(
                    const tbv_ref& tbv1 = get_tbv(fixed, *m_c1);
                    const tbv_ref& tbv2 = get_tbv(fixed, *m_c2);
                    SASSERT(tbv1[m_idx - 1] != BIT_z && tbv2[m_idx - 1] != BIT_z);
                );
            }
        }
        get_other_justification(fixed, *m_c1, m_idx)->get_dependencies(fixed, to_process);
        get_other_justification(fixed, *m_c2, m_idx)->get_dependencies(fixed, to_process);
        DEBUG_CODE(
            const tbv_ref& tbv1 = get_tbv(fixed, *m_c1);
            const tbv_ref& tbv2 = get_tbv(fixed, *m_c2);
            SASSERT(tbv1[m_idx] != BIT_z && tbv2[m_idx] != BIT_z);
        );
    }

    tbv_manager& fixed_bits::get_manager(unsigned sz){
          m_tbv_managers.reserve(sz + 1);
          if (!m_tbv_managers[sz])
              m_tbv_managers.set(sz, alloc(tbv_manager, sz));
          return *m_tbv_managers[sz];
    }

    tbv_manager& fixed_bits::get_manager(const pdd& v) {
          return get_manager(v.power_of_2());
    }

    tbv_ref& fixed_bits::get_tbv(const pdd& v) {
        auto found = m_var_to_tbv.find_iterator(optional(v));
        if (found == m_var_to_tbv.end()) {
            auto& manager = get_manager(v.power_of_2());
            if (v.is_val()) 
                m_var_to_tbv[optional(v)] = optional(tbv_ref(manager, manager.allocate(v.val())));
            else 
                m_var_to_tbv[optional(v)] = optional(tbv_ref(manager, manager.allocate()));
            return *m_var_to_tbv[optional(v)];
        }
        /*if (m_var_to_tbv.size() <= v) {
            m_var_to_tbv.reserve(v + 1);
            auto& manager = get_manager(sz);
            m_var_to_tbv[v] = tbv_ref(manager, manager.allocate());
            return *m_var_to_tbv[v];
        }*/
        return *m_var_to_tbv[optional(v)];
        /*auto& old_manager = m_var_to_tbv[optional(v)]->manager();
        if (old_manager.num_tbits() >= v.power_of_2())
            return *(m_var_to_tbv[optional(v)]);
        tbv* old_tbv = m_var_to_tbv[optional(v)]->detach();
        auto& new_manager = get_manager(v.power_of_2());
        tbv* new_tbv = new_manager.allocate();
        old_manager.copy(*new_tbv, *old_tbv); // Copy the lower bits to the new (larger) tbv
        old_manager.deallocate(old_tbv);
        m_var_to_tbv[optional(v)] = optional(tbv_ref(new_manager, new_tbv));
        return *m_var_to_tbv[optional(v)];*/
    }
    
    clause_ref fixed_bits::get_explanation(solver& s, bit_justication* j1, bit_justication* j2) {
        bit_dependencies to_process;
        // TODO: Check that we do not process the same tuple multiples times (efficiency)
        j1->get_dependencies(*this, to_process);
        j2->get_dependencies(*this, to_process);
        
        clause_builder conflict(s);
        conflict.set_redundant(true);
        
        auto insert_constraint = [&conflict, &s](bit_justication* j) {
            constraint* constr;
            if (j->has_constraint(constr))
                return;
            SASSERT(constr);
            if (constr->has_bvar()) {
                SASSERT(s.m_bvars.is_assigned(constr->bvar()));
                // add negated
                conflict.insert(signed_constraint(constr, s.m_bvars.value(constr->bvar()) != l_true));
            }
        };
        
        insert_constraint(j1);
        insert_constraint(j2);
        
        // In principle, the dependencies should be acyclic so this should terminate. If there are cycles it is for sure a bug
        while (!to_process.empty()) {
            bit_dependency& curr = to_process.back();
            to_process.pop_back();
            SASSERT(m_tbv_to_justification.contains(curr));
            bit_justication* j = m_tbv_to_justification[curr];
            insert_constraint(j);
            j->get_dependencies(*this, to_process);
        }
        
        return conflict.build();
    }
    
    tbit fixed_bits::get_value(const pdd& p, unsigned idx) {
        SASSERT(p.is_var());
        return get_tbv(p)[idx];
    }

    bool fixed_bits::fix_value(const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication* j) {
        SASSERT(val != BIT_x); // We don't use don't-cares
        SASSERT(p.is_var());
        if (val == BIT_z)
            return true;
        tbit curr_val = tbv[idx];

        if (val == curr_val)
            return true; // TODO: Take the new justification if it has a lower decision level

        auto& m = tbv.manager();

        if (curr_val == BIT_z) {
            m.set(*tbv, idx, val);
            delete m_tbv_to_justification[{ p, idx }];
            m_tbv_to_justification[{ p, idx }] = j;
            return true;
        }
        SASSERT((curr_val == BIT_1 && val == BIT_0) || (curr_val == BIT_0 && val == BIT_1));
        SASSERT(m_tbv_to_justification.contains({ p, idx }));
        return m_consistent = false;
    }
    
    bool fixed_bits::fix_value(solver& s, const pdd& p, unsigned idx, tbit val, bit_justication* j) {
        tbv_ref& tbv = get_tbv(p);
        if (fix_value(p, tbv, idx, val, j))
            return true;
        clause_ref explanation = get_explanation(s, j, m_tbv_to_justification[{ p, idx }]);
        s.set_conflict(*explanation);
        return false;
    }

    void fixed_bits::clear_value(const pdd& p, unsigned idx) {
        SASSERT(p.is_var());
        tbv_ref& tbv = get_tbv(p);
        auto& m = tbv.manager();
        m.set(*tbv, idx, BIT_z);

        SASSERT(m_tbv_to_justification.contains({ p, idx }));
        delete m_tbv_to_justification[{ p, idx }];
        m_tbv_to_justification[{ p, idx }] = nullptr;
    }

#define COUNT(DOWN, TO_COUNT) \
    do { \
    unsigned sz = ref.num_tbits(); \
    unsigned least = 0; \
    for (; least < sz; least++) { \
        if (ref[((DOWN) ? sz - least - 1 : least)] != (TO_COUNT)) \
            break; \
    } \
    if (least == sz) \
        return { sz, sz }; /* For sure TO_COUNT */ \
    unsigned most = least; \
    for (; most < sz; most++) { \
        if (ref[((DOWN) ? sz - most - 1 : most)] == ((TO_COUNT) == BIT_0 ? BIT_1 : BIT_0)) \
            break; \
    } \
    return { least, most }; /* There are between "least" and "most" leading/trailing TO_COUNT */ \
    } while(false)

    std::pair<unsigned, unsigned> fixed_bits::leading_zeros(const tbv_ref& ref) { COUNT(false, BIT_0); }
    std::pair<unsigned, unsigned> fixed_bits::trailing_zeros(const tbv_ref& ref) { COUNT(true, BIT_0); }
    std::pair<unsigned, unsigned> fixed_bits::leading_ones(const tbv_ref& ref) { COUNT(false, BIT_1); }
    std::pair<unsigned, unsigned> fixed_bits::trailing_ones(const tbv_ref& ref) { COUNT(true, BIT_1); }

    std::pair<rational, rational> fixed_bits::min_max(const tbv_ref& ref) {
        unsigned sz = ref.num_tbits();
        rational least(0);
        rational most(0);

        for (unsigned i = 0; i < sz; i++) {
            tbit v = ref[i];
            least *= 2;
            most *= 2;
            if (v == BIT_1) {
                least++;
                most++;
            }
            else if (v == BIT_z)
                most++;
        }

        return { least, most };
    }

    tbv_ref& fixed_bits::eval(solver& s, const pdd& p) {
        pdd zero = p.manager().zero();
        pdd one = p.manager().one();
        
        pdd sum = zero;
        tbv_ref* prev_sum_tbv = &get_tbv(sum);
        
        for (const dd::pdd_monomial& n : p) {
            SASSERT(!n.coeff.is_zero());
            pdd prod = p.manager().mk_val(n.coeff);
            tbv_ref* prev_mul_tbv = &get_tbv(prod);
            
            for (pvar fac : n.vars) {
                pdd fac_pdd = s.var(fac);
                prod *= fac_pdd;
                prev_mul_tbv = &bit_justication_mul::mul(*this, prod, *prev_mul_tbv, get_tbv(fac_pdd));
                if (!m_consistent)
                    return *prev_sum_tbv;
            }
            sum += prod;
            prev_sum_tbv = &bit_justication_add::add(*this, sum, *prev_sum_tbv, *prev_mul_tbv);
            if (!m_consistent)
                return *prev_sum_tbv;
        }
        return *prev_sum_tbv;
    }
}
