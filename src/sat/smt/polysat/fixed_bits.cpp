/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Extract fixed bits from constraints

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner), Clemens Eisenhofer 2022-08-22

--*/

#include "sat/smt/polysat/fixed_bits.h"
#include "sat/smt/polysat/ule_constraint.h"
#include "sat/smt/polysat/core.h"

namespace polysat {

    void fixed_bits::reset() {
        m_fixed_slices.reset();
        m_var = null_var;
    }

    // reset with fixed bits information for variable v
    void fixed_bits::init(pvar v) {
        m_fixed_slices.reset();
        m_var = v;
        c.get_fixed_bits(v, m_fixed_slices);
    }

    // if x[hi:lo] = value, then 
    // 2^(w-hi+1)* x >= 
    bool fixed_bits::check(rational const& val, fi_record& fi) {
        unsigned sz = c.size(m_var);
        rational bw = rational::power_of_two(sz);
        for (auto const& s : m_fixed_slices) {
            rational sbw = rational::power_of_two(s.length);
            // slice is properly contained in bit-vector variable
            if (s.length <= sz && s.value != mod(machine_div2k(val, s.offset), sbw)) {
                SASSERT(s.offset + s.length <= sz);
                rational hi_val = s.value;
                rational lo_val = mod(s.value + 1, sbw);                
                pdd lo = c.value(rational::power_of_two(sz - s.length) * lo_val, sz);
                pdd hi = c.value(rational::power_of_two(sz - s.length) * hi_val, sz);
                fi.reset();
                fi.interval = eval_interval::proper(lo, lo_val, hi, hi_val);
                fi.deps.push_back(dependency({ m_var, s }));
                
                fi.bit_width = s.length;
                fi.coeff = 1;
                return false;
            }
            // slice, properly contains variable.
            // s.offset refers to offset in containing value.
            if (s.length > sz && mod(machine_div2k(s.value, s.offset), bw) != val) {
                
                rational hi_val = mod(machine_div2k(s.value, s.offset), bw);
                rational lo_val = mod(hi_val + 1, bw);
                pdd lo = c.value(lo_val, sz);
                pdd hi = c.value(hi_val, sz);
                fi.reset();
                fi.interval = eval_interval::proper(lo, lo_val, hi, hi_val);
                fi.deps.push_back(dependency({ m_var, s }));               
                fi.bit_width = sz;
                fi.coeff = 1;
                return false;
            }
        }
        return true;
    }

    std::ostream& fixed_bits::display(std::ostream& out) const {
        for (auto const& s : m_fixed_slices)
            out << s.value << "[" << s.length << "]@" << s.offset << "\n";  
        return out;
    }   

}  // namespace polysat
