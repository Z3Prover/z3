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

    //
    // Assume x[hi:lo] = value.
    // Then 2^lo value <= x[hi:0] < 2^lo (value + 1),
    // and further 2^(lo + k) value <= 2^k x < 2^(lo + k) (value + 1)
    // where k = w - hi - 1, lo = s.offset, hi = s.offset + s.length - 1.
    //
    // k = w - s.offset - s.length
    // lo + k = w - s.length
    // entry bit-width = w - k = s.offset + s.length
    //
    bool fixed_bits::check(rational const& val, fi_record& fi) {
        unsigned sz = c.size(m_var);
        for (auto const& s : m_fixed_slices) {
            rational sbw = rational::power_of_two(s.length);
            // slice is properly contained in bit-vector variable
            if (s.length <= sz && s.value != mod(machine_div2k(val, s.offset), sbw)) {
                SASSERT(s.offset + s.length <= sz);
                unsigned bw = s.length + s.offset;
                rational p2lok = rational::power_of_two(sz - s.length);
                rational p2lo = rational::power_of_two(s.offset);
                pdd lo = c.value(p2lok * (s.value + 1), sz);
                pdd hi = c.value(p2lok * s.value, sz);
                rational lo_val = mod(p2lo * (s.value + 1), rational::power_of_two(bw));
                rational hi_val = p2lo * s.value;
                // verbose_stream() << "sz " << sz << "\n";
                // verbose_stream() << "slice len " << s.length << " off " << s.offset << " value " << s.value << "\n";
                // verbose_stream() << "lo " << lo.val() << " hi " << hi.val() << "\n";
                // verbose_stream() << "lo_val " << lo_val << " hi_val " << hi_val << "\n";

                fi.reset();
                fi.interval = eval_interval::proper(lo, lo_val, hi, hi_val);
                fi.deps.push_back(dependency({ m_var, s }));                
                fi.bit_width = bw;
                fi.coeff = 1;
                // verbose_stream() << "fixed bits sub: v" << m_var << " " << sz << " value " << val << " "  << fi << "\n";
                return false;
            }
#if 0
            // slice, properly contains variable.
            // s.offset refers to offset in containing value.
            rational bw = rational::power_of_two(sz);
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
                verbose_stream() << "fixed bits sup: v" << m_var << " " << fi << "\n";
                return false;
            }
#endif
        }
        return true;
    }

    std::ostream& fixed_bits::display(std::ostream& out) const {
        for (auto const& s : m_fixed_slices)
            out << s.value << "[" << s.length << "]@" << s.offset << "\n";  
        return out;
    }   

}  // namespace polysat
