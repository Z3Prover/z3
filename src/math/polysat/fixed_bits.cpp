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
        return fixed.m_bvpos_to_justification[{ p, idx }].m_justification;
    }
    
    const tbv_ref* bit_justication::get_tbv(fixed_bits& fixed, const pdd& p) {
        return fixed.get_tbv(p);
    }
    
    // returns: Is it consistent
    bool bit_justication::fix_bit(solver& s, fixed_bits& fixed, const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication** j) {
        SASSERT(j && *j);
        if (!fixed.fix_bit(s, p, tbv, idx, val, *j) && (*j)->can_dealloc()) {
            // TODO: Potential double deallocation; Check!
            dealloc(*j);
            *j = nullptr;
        }
        return fixed.m_consistent;
    }
    
    bool bit_justication::fix_bit(solver& s, fixed_bits& fixed, const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication* j) {
        return fix_bit(s, fixed, p, tbv, idx, val, &j);
    }
    
    void bit_justication_constraint::get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) {
        for (const auto& dep : this->m_dependencies) {
            LOG("Dependency: pdd: " << dep.m_pdd << " idx: " << dep.m_bit_idx);
            to_process.push_back(dep);
        }
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
    void bit_justication_mul::propagate(solver& s, fixed_bits& fixed, const pdd& r, const pdd &p, const pdd &q) {
        LOG_H2("Bit-Propagating: " << r << " = (" << p << ") * (" << q << ")");
        tbv_ref& p_tbv = *fixed.get_tbv(p);
        tbv_ref& q_tbv = *fixed.get_tbv(q);
        tbv_ref& r_tbv = *fixed.get_tbv(r);
        LOG("p: " << p << " = " << p_tbv);
        LOG("q: " << q << " = " << q_tbv);
        LOG("r: " << r << " = " << r_tbv);
        
        auto& m = r_tbv.manager();
        // TODO: maybe propagate the bits only until the first "don't know" and as well for the leading "0"s [The bits in-between are rare and hard to compute]
        unsigned min_val = 0; // The value of the current bit assuming all unknown bits are 0
        unsigned max_val = 0; // The value of the current bit assuming all unknown bits are 1
        unsigned highest_overflow_idx = -1; // The index which could result in the highest overflow (Used for backward propagation. Which previous bit-index could have the highest overflow to the current bit?)
        unsigned highest_overflow_val = 0; // The respective value
        bool highest_overflow_precise = false; // True if the highest overflow is still precise after all divisions by 2  (We can only use those for backward propagation. If it is not a power of 2 we don't know which values to set.)
        
        // Forward propagation
        // Example 1: 
        // r4 = (0 q3 + 1 1 + 0 q1 + 0 q0) + (1 1 + 0 q1 + 1 1) / 2
        // min_val = 2 = 2 / 2 + 1; max_val = 2 = 2 / 2 + 1 and  (0 q3 + 1 1 + 0 q1 + 0 q0) + (1 1 + 0 q1 + 1 1) / 2 = 2 we conclude r3 = 0 (and min_val = max_val := min_val / 2 + 2 / 2)
        //
        // Example 2: 
        // r4 = (0 q3 + 1 1 + 0 q1 + 0 q0) + (1 1 + 0 q1 + 1 q0) / 2
        // min_val = 1 = 1 + 1 / 2; max_val = 2 = 1 + 2 / 2. We cannot propagate to r4 as we don't know the value of the overflow
        //
        // Example 3:
        // r4 = (0 q3 + p1 1 + 0 q1 + 0 q0) + (1 1 + 0 q1 + 1 1) / 2
        // min_val = 1 = 0 + 2 / 2; v = 2 = 1 + 2 / 2. We cannot propagate to r4 as we don't know the precise value
        
        // Backward propagation
        // Example 1:
        // 0 = r3 = (1 1 + 0 q2 + 1 q1 + p3 0) + (0 q2 + 1 1 + 1 1) / 2
        // highest_overflow_idx = 3 [meaning r3]; min_val = 2 = 1 + 2 / 2; max_val = 3 = 2 + 2 / 2. We can propagate q1 = 0 as min_val == max_val - 1
        //
        // Example 2:
        // 0 = r3 = (1 1 + 0 q2 + 0 q1 + p3 0) + (0 q2 + p1 1 + p2 1) / 2
        // highest_overflow_idx = 2; highest_overflow_precise = true; min_val = 1; max_val = 2. We can propagate p2 = p1 = 1 in r2 as min_val == max_val - 1 and we know that we can make all [highest_overflow_precise == true] undetermined products in r2 true
        //
        // Example 3:
        // 0 = r3 = (1 1 + 0 q2 + 0 q1 + p3 0) + (1 q2 + 1 1 + p2 1) / 2
        // highest_overflow_idx = 2; highest_overflow_precise = false; min_val = 1; max_val = 2. We can not propagate p2 = 1 or q2 = 1 in r2 as we don't know which [highest_overflow_precise == false i.e., 3 is not divisible by 2]
        //
        // Example 4:
        // 0 = r3 = (1 1 + 0 q2 + 0 q1 + p3 0) + (p0 q2 + p1 1 + 0 1) / 2
        // highest_overflow_idx = 2; highest_overflow_precise = true; min_val = 1; max_val = 2. We can propagate p1 = 1 but not p0 = 1 or q2 = 1 as we don't know which
        //
        // In all cases cases min_val == max_val after backward propagation [max_val = min_val if assigned to 0; min_val = max_val if assigned to 1]
        
        // TODO: Check: Is the performance too worse? It is O(k^3) in the worst case...
        for (unsigned i = 0; i < m.num_tbits(); i++) {
            unsigned current_min_val = 0, current_max_val = 0;
            for (unsigned x = 0, y = i; x <= i; x++, y--) {
                tbit bit1 = p_tbv[x];
                tbit bit2 = q_tbv[y];
                
                if (bit1 == BIT_1 && bit2 == BIT_1) {
                    current_min_val++; // we get two 1
                    current_max_val++;
                }
                else if (bit1 != BIT_0 && bit2 != BIT_0)
                    current_max_val++; // we could get two 1
            }
            
            if (max_val >= highest_overflow_val) {
                highest_overflow_val = max_val;
                highest_overflow_idx = i;
                highest_overflow_precise = true;
            }
            min_val += current_min_val;
            max_val += current_max_val;
            
            if (min_val == max_val) {
                // We know the value of this bit
                // forward propagation
                // this might add a conflict if the value is already set to another value
                if (!fix_bit(s, fixed, r, r_tbv, i, min_val & 1 ? BIT_1 : BIT_0, alloc(bit_justication_mul, i, p, q)))
                    return;
            }
            else if (r_tbv[i] != BIT_z && min_val == max_val - 1) {
                // backward propagation
                // this cannot add a conflict. However, conflicts are already captured in the forward propagation case
                tbit set;
                if ((min_val & 1) == (r_tbv[i] == BIT_0 ? 0 : 1)) {
                    set = BIT_0;
                    max_val = min_val;
                }
                else {
                    set = BIT_1;
                    min_val = max_val;
                }
                SASSERT(set == BIT_0 || set == BIT_1);
                SASSERT(highest_overflow_idx <= i);
                if (highest_overflow_precise) { // Otherwise, we cannot set the elements in the previous ri but we at least know max_val == min_val (resp., vice-versa)
                    bit_justication_shared* j = nullptr;
                    unsigned_vector set_bits;
#define SHARED_JUSTIFICATION (j ? (j->inc_ref(), (bit_justication**)&j) : (j = alloc(bit_justication_shared, alloc(bit_justication_mul, i, p, q, r)), (bit_justication**)&j))
                    
                    for (unsigned x = 0, y = i; x <= highest_overflow_idx; x++, y--) {
                        tbit bit1 = p_tbv[x];
                        tbit bit2 = q_tbv[y];
                        if (set == BIT_0 && bit1 != bit2) {
                            // Sets: (1, z), (z, 1), (0, 1), (1, 0) [the cases with two constants are used for minimizing decision levels]
                            // Does not set: (1, 1), (0, 0), (0, z), (z, 0)
                            // Also does not set: (z, z) [because we don't know which one. We only know that it has to be 0 => we can still set max_val = min_val]
                            if (bit1 == BIT_1) {
                                if (!fix_bit(s, fixed, q, q_tbv, y, BIT_0, SHARED_JUSTIFICATION)) {
                                    VERIFY(false);
                                }
                                set_bits.push_back(y << 1 | 1);
                            }
                            else if (bit2 == BIT_1) {
                                if (!fix_bit(s, fixed, p, p_tbv, x, BIT_0, SHARED_JUSTIFICATION)) {
                                    VERIFY(false);
                                }
                                set_bits.push_back(x << 1 | 0);
                            }
                        }
                        else if (set == BIT_1 && bit1 != BIT_0 && bit2 != BIT_0) {
                            // Sets: (1, z), (z, 1), (1, 1), (z, z)
                            // Does not set: (0, 0), (0, z), (z, 0), (0, 1), (1, 0)
                            if (bit1 == BIT_1) {
                                if (!fix_bit(s, fixed, q, q_tbv, y, BIT_1, SHARED_JUSTIFICATION)) {
                                    VERIFY(false);
                                }
                                set_bits.push_back(y << 1 | 1);
                            }
                            if (bit2 == BIT_1) {
                                if (!fix_bit(s, fixed, p, p_tbv, x, BIT_1, SHARED_JUSTIFICATION)) {
                                    VERIFY(false);
                                }
                                set_bits.push_back(x << 1 | 0);
                            }
                            if (bit1 == BIT_z && bit2 == BIT_z) {
                                if (!fix_bit(s, fixed, p, p_tbv, i, BIT_1, SHARED_JUSTIFICATION) ||
                                    !fix_bit(s, fixed, q, q_tbv, i, BIT_1, SHARED_JUSTIFICATION)) {
                                    VERIFY(false);
                                }
                                set_bits.push_back(y << 1 | 1);
                                set_bits.push_back(x << 1 | 0);
                            }
                        }
                    }
                    
                    if (j) {
                        // the reference count might be higher than the number of elements in the vector
                        // some elements might not be relevant for the justification (e.g., because of decision-level)
                        ((bit_justication_mul*)j->get_justification())->m_bit_indexes = set_bits;
                    }
                }
            }
            
            // Subtract one; shift this to the next higher bit as "carry values"
            min_val >>= 1;
            max_val >>= 1;
            highest_overflow_precise &= (highest_overflow_val & 1) == 0; 
            highest_overflow_val >>= 1;
        }
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
                
        const tbv_ref& p_tbv = *get_tbv(fixed, *m_p);
        const tbv_ref& q_tbv = *get_tbv(fixed, *m_q);
        
        if (m_r)
            get_dependencies_forward(fixed, to_process, p_tbv, q_tbv, relevant_range);
        else 
            get_dependencies_backward(fixed, to_process, p_tbv, q_tbv, relevant_range);
    }
    
    void bit_justication_mul::get_dependencies_forward(fixed_bits &fixed, bit_dependencies &to_process, const tbv_ref& p_tbv, const tbv_ref& q_tbv, unsigned relevant_range) {
        for (unsigned i = m_idx - relevant_range; i <= m_idx; i++) {
            for (unsigned x = 0, y = i; x <= i; x++, y--) {
                tbit bit1 = p_tbv[x];
                tbit bit2 = q_tbv[y];
                
                if (bit1 == BIT_1 && bit2 == BIT_1) {
                    get_other_justification(fixed, *m_p, x)->get_dependencies(fixed, to_process);
                    get_other_justification(fixed, *m_q, y)->get_dependencies(fixed, to_process);
                }
                else if (bit1 == BIT_0) // TODO: Take the better one if both are zero
                    get_other_justification(fixed, *m_p, x)->get_dependencies(fixed, to_process);
                else if (bit2 == BIT_0)
                    get_other_justification(fixed, *m_q, y)->get_dependencies(fixed, to_process);
                else {
                    // The bit is apparently not set because we cannot derive a truth-value.
                    // Why do we ask for an explanation?
                    VERIFY(false);
                }
            }
        }
    }
    
    void bit_justication_mul::get_dependencies_backward(fixed_bits& fixed, bit_dependencies& to_process, const tbv_ref& p_tbv, const tbv_ref& q_tbv, unsigned relevant_range) {
        SASSERT(!m_bit_indexes.empty()); // Who asked us for an explanation if there is nothing in the set?
        unsigned set_idx = 0;
        for (unsigned i = m_idx - relevant_range; i <= m_idx; i++) {
            for (unsigned x = 0, y = i; x <= i; x++, y--) {
                
                unsigned i_p = x << 1 | 0;
                unsigned i_q = y << 1 | 1;
                
                // the list is ordered in the same way we iterate now through it so we just look at the first elements
                unsigned next1 = set_idx >= m_bit_indexes.size() ? -1 : m_bit_indexes[set_idx];
                unsigned next2 = set_idx + 1 >= m_bit_indexes.size() ? -1 : m_bit_indexes[set_idx + 1];
                
                bool p_in_set = false, q_in_set =false;
                
                if (i_p == next1 || i_p == next2) {
                    set_idx++;
                    p_in_set = true;
                }
                else if (i_q == next1 || i_q == next2) {
                    set_idx++;
                    q_in_set = true;
                }
                                
                tbit bit1 = p_tbv[x];
                tbit bit2 = q_tbv[y];
                
                // TODO: Check once more
                
                if (bit1 == BIT_1 && bit2 == BIT_1) {
                    if (!p_in_set)
                        get_other_justification(fixed, *m_p, x)->get_dependencies(fixed, to_process);
                    if (!q_in_set)
                        get_other_justification(fixed, *m_q, y)->get_dependencies(fixed, to_process);
                }
                else if (bit1 == BIT_0) {
                    if (!p_in_set)
                        get_other_justification(fixed, *m_p, x)->get_dependencies(fixed, to_process);
                    else if (!q_in_set)
                        get_other_justification(fixed, *m_q, y)->get_dependencies(fixed, to_process);
                }
                else if (bit2 == BIT_0 && !q_in_set) {
                    if (!q_in_set)
                        get_other_justification(fixed, *m_q, y)->get_dependencies(fixed, to_process);
                    else if (!p_in_set)
                        get_other_justification(fixed, *m_p, x)->get_dependencies(fixed, to_process);
                }
                else {
                    // unlike in the forward case this can happen
                }
            }
        }
    }
    
    // similar to multiplying but far simpler/faster (only the direct predecessor might overflow)
    void bit_justication_add::propagate(solver& s, fixed_bits& fixed, const pdd& r, const pdd& p, const pdd& q) {
        LOG_H2("Bit-Propagating: " << r << " = (" << p << ") + (" << q << ")");
        // TODO: Add backward propagation
        tbv_ref& p_tbv = *fixed.get_tbv(p);
        tbv_ref& q_tbv = *fixed.get_tbv(q);
        tbv_ref& r_tbv = *fixed.get_tbv(r);
        LOG("p: " << p << " = " << p_tbv);
        LOG("q: " << q << " = " << q_tbv);
        LOG("r: " << r << " = " << r_tbv);
        
        auto& m = r_tbv.manager();

        unsigned min_bit_value = 0;
        unsigned max_bit_value = 0;

        for (unsigned i = 0; i < m.num_tbits(); i++) {
            tbit bit1 = p_tbv[i];
            tbit bit2 = q_tbv[i];
            if (bit1 == BIT_1) {
                min_bit_value++;
                max_bit_value++;
            }
            else if (bit1 == BIT_z)
                max_bit_value++;
            
            if (bit2 == BIT_1) {
                min_bit_value++;
                max_bit_value++;
            }
            else if (bit2 == BIT_z)
                max_bit_value++;

            if (min_bit_value == max_bit_value)
                if (!fix_bit(s, fixed, r, r_tbv, i, min_bit_value & 1 ? BIT_1 : BIT_0, alloc(bit_justication_add)))
                    return;

            min_bit_value >>= 1;
            max_bit_value >>= 1;
        }
    }
    
    void bit_justication_add::get_dependencies(fixed_bits& fixed, bit_dependencies& to_process) {
        if (m_c1->power_of_2() > 1 && m_idx > 0) {
            get_other_justification(fixed, *m_c1, m_idx - 1)->get_dependencies(fixed, to_process);
            get_other_justification(fixed, *m_c2, m_idx - 1)->get_dependencies(fixed, to_process);
            DEBUG_CODE(
                const tbv_ref& tbv1 = *get_tbv(fixed, *m_c1);
                const tbv_ref& tbv2 = *get_tbv(fixed, *m_c2);
                SASSERT(tbv1[m_idx - 1] != BIT_z && tbv2[m_idx - 1] != BIT_z);
            );
        }
        get_other_justification(fixed, *m_c1, m_idx)->get_dependencies(fixed, to_process);
        get_other_justification(fixed, *m_c2, m_idx)->get_dependencies(fixed, to_process);
        DEBUG_CODE(
            const tbv_ref& tbv1 = *get_tbv(fixed, *m_c1);
            const tbv_ref& tbv2 = *get_tbv(fixed, *m_c2);
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

    tbv_ref* fixed_bits::get_tbv(const pdd& v) {
        LOG("Looking for tbv for " << v);
        auto found = m_var_to_tbv.find_iterator(optional(v));
        if (found == m_var_to_tbv.end()) {
            auto& manager = get_manager(v.power_of_2());
            if (v.is_val()) 
                m_var_to_tbv.insert(optional(v), alloc(tbv_ref, manager, manager.allocate(v.val())));
            else 
                m_var_to_tbv.insert(optional(v), alloc(tbv_ref, manager, manager.allocate()));
            return m_var_to_tbv[optional(v)];
        }
        /*if (m_var_to_tbv.size() <= v) {
            m_var_to_tbv.reserve(v + 1);
            auto& manager = get_manager(sz);
            m_var_to_tbv[v] = tbv_ref(manager, manager.allocate());
            return *m_var_to_tbv[v];
        }*/
        return found->m_value;
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
        
#define GET_DEPENDENCY(X) do { (X)->get_dependencies(*this, to_process); if ((X)->can_dealloc()) { dealloc(X); } } while (false)
        
        clause_builder conflict(s);
        conflict.set_redundant(true);
        
        auto insert_constraint = [&conflict, &s](bit_justication* j) {
            constraint* constr;
            if (!j->has_constraint(constr))
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
        
        GET_DEPENDENCY(j1);
        GET_DEPENDENCY(j2);
        
        // In principle, the dependencies should be acyclic so this should terminate. If there are cycles it is for sure a bug
        while (!to_process.empty()) {
            bvpos& curr = to_process.back();
            if (curr.m_pdd->is_val()) {
                to_process.pop_back();
                continue; // We don't need an explanation for bits of constants
            }
            SASSERT(m_bvpos_to_justification.contains(curr));
                
            bit_justication* j = m_bvpos_to_justification[curr].m_justification;
            to_process.pop_back();
            insert_constraint(j);
            GET_DEPENDENCY(j);
        }
        
        return conflict.build();
    }
    
    tbit fixed_bits::get_value(const pdd& p, unsigned idx) {
        SASSERT(p.is_var());
        return (*get_tbv(p))[idx];
    }

    // True iff the justification was stored (must not be deallocated!)
    bool fixed_bits::fix_value_core(const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication* j) {
        LOG("Fixing bit " << idx << " in " << p << " (" << tbv << ")");
        constraint* c;
        if (j->has_constraint(c)) {
            LOG("justification constraint: " << *c);
        }

        SASSERT(val != BIT_x); // We don't use don't-cares
        if (val == BIT_z) // just ignore this case
            return false;
        tbit curr_val = tbv[idx];
        bvpos pos(p, idx);

        if (val == curr_val) { // we already have the "correct" value there
            if (p.is_val())
                return false; // no justification because it is trivial
            SASSERT(m_bvpos_to_justification.contains(pos));
            justified_bvpos& old_j = m_bvpos_to_justification[pos];
            if (old_j.m_justification->m_decision_level > j->m_decision_level)
                return false;
            replace_justification(old_j, j); // the new justification is better. Let's take it
            return true;
        }

        auto& m = tbv.manager();

        if (curr_val == BIT_z) {
            m.set(*tbv, idx, val);
            justified_bvpos jpos(pos, j, m_trail.size());
            
            auto jstfc = m_bvpos_to_justification.get(pos, {});
            if (jstfc.m_justification && jstfc.m_justification->can_dealloc())
                dealloc(jstfc.m_justification);
            
            m_bvpos_to_justification.insert(pos, jpos);
            m_trail.push_back(jpos);
            return true;
        }
        SASSERT((curr_val == BIT_1 && val == BIT_0) || (curr_val == BIT_0 && val == BIT_1));
        SASSERT(p.is_val() || m_bvpos_to_justification.contains(pos));
        m_consistent = false;
        return false;
    }
    
    bool fixed_bits::fix_bit(solver& s, const pdd& p, tbv_ref& tbv, unsigned idx, tbit val, bit_justication* j) {
        SASSERT(m_trail.size() == s.m_level);
        
        bool changed = fix_value_core(p, tbv, idx, val, j);
        if (changed)
            return true;
        
        if (!m_consistent) {
            bvpos pos(p, idx);
            clause_ref explanation = get_explanation(s, j, m_bvpos_to_justification[pos].m_justification);
            s.set_conflict(*explanation);
        }
        return false;
    }
    
    // return: consistent?
    bool fixed_bits::fix_value(solver& s, const pdd& p, unsigned idx, tbit val, bit_justication* j) {
        tbv_ref& tbv = *get_tbv(p);
        bool changed = fix_value_core(p, tbv, idx, val, j);
        if (changed) { // this implies consistency
            propagate_to_subterm(s, p);
            return true;
        }
        // TODO: Propagate equality if everything is set
        if (!m_consistent) {
            LOG("Adding conflict on bit " << idx << " on pdd " << p);
            clause_ref explanation = get_explanation(s, j, m_bvpos_to_justification[{ p, idx }].m_justification);
            s.set_conflict(*explanation);
            return false; // get_explanation will dealloc the justification
        }
        if (j->can_dealloc())
            dealloc(j);
        return m_consistent;
    }

    void fixed_bits::clear_value(const pdd& p, unsigned idx) {
        tbv_ref& tbv = *get_tbv(p);
        auto& m = tbv.manager();
        m.set(*tbv, idx, BIT_z);
        bvpos pos(p, idx);
        SASSERT(m_bvpos_to_justification.contains(pos));
        const auto& jstfc = m_bvpos_to_justification[pos];
        if (jstfc.m_justification->can_dealloc())
            dealloc(jstfc.m_justification);
        m_bvpos_to_justification.remove(pos);
    }
    
    void fixed_bits::replace_justification(const justified_bvpos& old_j, bit_justication* new_j) {
        SASSERT(old_j.m_justification->m_decision_level > new_j->m_decision_level);
        SASSERT(m_trail[old_j.m_trail_pos] == old_j);
        
        if (old_j.m_justification->can_dealloc())
            dealloc(old_j.m_justification);
        m_trail[old_j.m_trail_pos].m_justification = new_j; // We only overwrite with smaller decision-levels. This way we preserve some kind of "order"
    }
    
    void fixed_bits::push() {
#if 0
        m_trail_size.push_back(m_trail.size());
#endif
    }
    
    void fixed_bits::pop(unsigned pop_cnt) {
#if 0
        SASSERT(!m_consistent); // Why do we backtrack if this is true? We might remove this for (random) restarts
        SASSERT(pop_cnt > 0);
        
        unsigned old_lvl = m_trail_size.size();
        unsigned new_lvl = old_lvl - pop_cnt;
        SASSERT(pop_cnt <= old_lvl);
        
        unsigned prev_cnt = m_trail_size[new_lvl];
        m_trail_size.resize(new_lvl);
        
        unsigned last_to_keep = -1;
        
        for (unsigned i = m_trail.size(); i > prev_cnt; i--) {
            // all elements m_trail[j] with (j > i) have higher decision levels than new_lvl 
            justified_bvpos& curr = m_trail[i - 1];
            SASSERT(curr.m_justification->m_decision_level <= old_lvl);
            
            if (curr.m_justification->m_decision_level > new_lvl) {
                clear_value(curr.get_pdd(), curr.get_idx());
                if (last_to_keep != -1)
                    std::swap(curr, m_trail[--last_to_keep]);
            }
            else {
                if (last_to_keep == -1)
                    last_to_keep = i;
            }
        }
        if (last_to_keep == -1)
            m_trail.resize(prev_cnt);
        else 
            m_trail.resize(last_to_keep);
#endif
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

    tbv_ref* fixed_bits::eval(solver& s, const pdd& p) {
        
        if (p.is_val() || p.is_var())
            return get_tbv(p);
        
        pdd zero = p.manager().zero();
        pdd one = p.manager().one();
        
        pdd sum = zero;
        
        for (const dd::pdd_monomial& n : p) {
            SASSERT(!n.coeff.is_zero());
            pdd prod = p.manager().mk_val(n.coeff);
            
            for (pvar fac : n.vars) {
                pdd fac_pdd = s.var(fac);
                pdd pre_prod = prod;
                prod *= fac_pdd;
                
                if (!pre_prod.is_val() || !pre_prod.val().is_one()) {
                    bit_justication_mul::propagate(s, *this, prod, pre_prod, fac_pdd);
                    if (!m_consistent)
                        return nullptr;
                }
            }
            pdd pre_sum = sum;
            sum += prod;
            
            if (!pre_sum.is_val() || !pre_sum.val().is_zero()) {
                bit_justication_add::propagate(s, *this, sum, pre_sum, prod);
                if (!m_consistent)
                    return nullptr;
            }
        }
        return get_tbv(sum);
    }
    
    //propagate to subterms of the polynomial/pdd
    void fixed_bits::propagate_to_subterm(solver& s, const pdd& p) {
        // we assume the tbv of p was already assigned and there was no conflict
        if (p.is_var() || p.is_val())
            return;
        
        vector<pdd> sum_subterms;
        vector<vector<pdd>> prod_subterms;
        pdd zero = p.manager().zero();
        pdd one = p.manager().one();
        
        pdd sum = zero;
        
        for (const dd::pdd_monomial& n : p) {
            SASSERT(!n.coeff.is_zero());
            pdd prod = p.manager().mk_val(n.coeff);
            prod_subterms.push_back(vector<pdd>());
            
            // TODO: Maybe process the coefficient first as we have the most information there 
            //  (however, we cannot really revert the order as we used the coefficient first for forward propagation)
            if (n.coeff != 1) 
                prod_subterms.back().push_back(prod);
            
            for (pvar fac : n.vars) {
                pdd fac_pdd = s.var(fac);
                prod *= fac_pdd;
                prod_subterms.back().push_back(prod);
                prod_subterms.back().push_back(fac_pdd);
            }
            sum += prod;
            sum_subterms.push_back(sum);
            sum_subterms.push_back(prod);
        }
        
        SASSERT(sum_subterms[0] == sum_subterms[1] && sum_subterms.size() % 2 == 1);
        SASSERT(2 * prod_subterms.size() == sum_subterms.size());
        
        pdd current = p;
        
        for (unsigned i = sum_subterms.size() - 1; i > 1; i -= 2) {
            pdd rhs = sum_subterms[i]; // a monomial for sure
            pdd lhs = sum_subterms[i - 1];
            SASSERT(rhs.is_monomial());
            bit_justication_add::propagate(s, *this, current, lhs, rhs);
            current = rhs;
            auto& prod = prod_subterms[i / 2];
            for (unsigned j = prod.size() - 1; j > 1; j -= 2) {
                bit_justication_mul::propagate(s, *this, current, prod[j], prod[j - 1]);
                current = prod[j - 1];
            }
            current = lhs;
        }
    }
}
