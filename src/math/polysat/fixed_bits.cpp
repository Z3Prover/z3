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

    tbv_manager& fixed_bits::get_manager(unsigned sz){
          m_tbv_managers.reserve(sz + 1);
          if (!m_tbv_managers[sz])
              m_tbv_managers.set(sz, alloc(tbv_manager, sz));
          return *m_tbv_managers[sz];
    }

    tbv_manager& fixed_bits::get_manager(const pdd& v) {
          return get_manager(v.power_of_2());
    }

    tbv_ref& fixed_bits::get_tbv(pvar v, unsigned sz) {
        if (m_var_to_tbv.size() <= v) {
            m_var_to_tbv.reserve(v + 1);
            auto& manager = get_manager(sz);
            m_var_to_tbv[v] = tbv_ref(manager, manager.allocate());
            return *m_var_to_tbv[v];
        }
        auto& old_manager = m_var_to_tbv[v]->manager();
        if (old_manager.num_tbits() >= sz)
            return *(m_var_to_tbv[v]);
        tbv* old_tbv = m_var_to_tbv[v]->detach();
        auto& new_manager = get_manager(sz);
        tbv* new_tbv = new_manager.allocate();
        old_manager.copy(*new_tbv, *old_tbv); // Copy the lower bits to the new (larger) tbv
        old_manager.deallocate(old_tbv);
        m_var_to_tbv[v] = tbv_ref(new_manager, new_tbv);
        return *m_var_to_tbv[v];
    }

    tbv_ref& fixed_bits::get_tbv(const pdd& p) {
        SASSERT(p.is_var());
        return get_tbv(p.var(), p.power_of_2());
    }

    tbit fixed_bits::get_value(const pdd& p, unsigned idx) {
        SASSERT(p.is_var());
        return get_tbv(p)[idx];
    }

    bool fixed_bits::fix_value(solver& s, const pdd& p, unsigned idx, tbit val, constraint* c, bit_dependency& dep) {
        SASSERT(val != BIT_x); // We don't use don't-cares
        SASSERT(p.is_var());
        if (val == BIT_z)
            return true;
        tbv_ref& tbv = get_tbv(p);
        tbit curr_val = tbv[idx];

        if (val == curr_val)
            return true;

        auto& m = tbv.manager();

        if (curr_val == BIT_z) {
            m.set(*tbv, idx, val);
            m_tbv_to_justification[std::pair(tbv.get(), idx)] = bit_justication(c, (bit_dependency&&)std::move(dep));
            return true;
        }
        SASSERT((curr_val == BIT_1 && val == BIT_0) || (curr_val == BIT_0 && val == BIT_1));

        return false;

    }

    void fixed_bits::clear_value(const pdd& p, unsigned idx) {
        SASSERT(p.is_var());
        tbv_ref& tbv = get_tbv(p);
        auto& m = tbv.manager();
        m.set(*tbv, idx, BIT_z);

        SASSERT(m_tbv_to_justification.contains(std::pair(tbv.get(), idx)));
        m_tbv_to_justification[std::pair(tbv.get(), idx)] = bit_justication();
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

    // multiplication: (1*p0 + 2*p1 + 4*p2 + 8*p3 + ...) * (1*q0 + 2*q1 + 4*q2 + 8*q3 + ...) =
    // = 1 * (p0 q0) + 2 * (p0 q1 + p1 q0) + 4 * (p0 q2 + p1 q1 + p2 q0) + 8 * (p0 q3 + p1 q2 + p2 q1 + p3 q0) + ...
    // maintains
    void fixed_bits::multiply(tbv_ref& in_out, const tbv_ref& in2) {
        auto m= in_out.manager();
        m_aux_values.reserve(m.num_tbits());

        unsigned min_bit_value = 0; // The value of the current bit assuming all unknown bits are 0
        unsigned max_bit_value = 0; // The value of the current bit assuming all unknown bits are 1

        // TODO: Check: Is the performance too worse? It is O(k^2)
        for (unsigned i = 0; i < m.num_tbits(); i++) {
            for (unsigned x = 0, y = i; x <= i; x++, y--) {
                tbit bit1 = in_out[x];
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
                // As we might access in_out in some later iteration again we first write to aux-list
                m_aux_values[i] = min_bit_value & 1 ? BIT_1 : BIT_0;
            }
            else {
                m_aux_values[i] = BIT_z;
            }
            // Subtract one; shift this to the next higher bit as "carry value"
            min_bit_value >>= 1;
            max_bit_value >>= 1;
        }

        // Copy aux to result tbv
        for (unsigned i = 0; i < m.num_tbits(); i++) {
            m.set(*in_out, i, (tbit)m_aux_values[i]);
        }
    }

    // similar to multiplying
    void fixed_bits::add(tbv_ref& in_out, const tbv_ref& in2) {
        auto m= in_out.manager();

        unsigned min_bit_value = 0;
        unsigned max_bit_value = 0;

        for (unsigned i = 0; i < m.num_tbits(); i++) {
            tbit bit1 = in_out[i];
            tbit bit2 = in2[i];
            if (bit1 == BIT_1 && bit2 == BIT_1) {
                min_bit_value++;
                max_bit_value++;
            }
            else if (bit1 != BIT_0 && bit2 != BIT_0) {
                max_bit_value++;
            }

            if (min_bit_value == max_bit_value)
                // for addition we don't need previous values so we can directly write to the output variable
                m.set(*in_out, i, min_bit_value & 1 ? BIT_1 : BIT_0);
            else
                m.set(*in_out, i, BIT_z);

            min_bit_value >>= 1;
            max_bit_value >>= 1;
        }
    }

    tbv_ref fixed_bits::eval(const pdd& p) {
        tbv_manager m = get_manager(p);
        unsigned sz = m.num_tbits();
        tbv_ref ret = tbv_ref(m, m.allocate(0ull));
        for (const dd::pdd_monomial& s : p) {
            SASSERT(!s.coeff.is_zero());
            tbv_ref sum = tbv_ref(m, m.allocate(s.coeff));
            for (pvar fac : s.vars) {
                multiply(sum, get_tbv(fac, sz));
            }
            add(ret, sum);
        }
        return ret;
    }
}
