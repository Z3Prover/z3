/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_valuation.cpp

Abstract:

    A Stochastic Local Search (SLS) engine
    Uses invertibility conditions, 
    interval annotations
    don't care annotations

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/

#include "ast/sls/sls_valuation.h"

namespace bv {

    sls_valuation::sls_valuation(unsigned bw): bw(bw) {
        nw = (bw + sizeof(digit_t) * 8 - 1) / (8 * sizeof(digit_t));
        unsigned num_bytes = nw * sizeof(digit_t);
        lo.reserve(nw + 1);
        hi.reserve(nw + 1);
        bits.reserve(nw + 1);
        fixed.reserve(nw + 1);
        // have lo, hi bits, fixed point to memory allocated within this of size num_bytes each allocated        
        for (unsigned i = 0; i < nw; ++i)
            lo[i] = 0, hi[i] = 0, bits[i] = 0, fixed[i] = 0;
        for (unsigned i = bw; i < 8 * sizeof(digit_t) * nw; ++i)
            set(fixed, i, false);
    }

    sls_valuation::~sls_valuation() {
    }

    bool sls_valuation::in_range(svector<digit_t> const& bits) const {
        mpn_manager m;    
        auto c = m.compare(lo.data(), nw, hi.data(), nw);
        // full range
        if (c == 0)
            return true;
        // lo < hi: then lo <= bits & bits < hi
        if (c < 0)
            return
            m.compare(lo.data(), nw, bits.data(), nw) <= 0 &&
            m.compare(bits.data(), nw, hi.data(), nw) < 0;
        // hi < lo: bits < hi or lo <= bits
        return
            m.compare(lo.data(), nw, bits.data(), nw) <= 0 ||
            m.compare(bits.data(), nw, hi.data(), nw) < 0;
    }

    bool sls_valuation::eq(svector<digit_t> const& other) const {
        auto c = 0 == memcmp(bits.data(), other.data(), bw / 8);
        if (bw % 8 == 0 || !c)
            return c;
        for (unsigned i = 8 * (bw / 8); i < bw; ++i)
            if (get(bits, i) != get(other, i))
                return false;
        return true;
    }

    bool sls_valuation::gt(svector<digit_t> const& a, svector<digit_t> const& b) const {
        mpn_manager m;
        return m.compare(a.data(), nw, b.data(), nw) > 0;
    }

    void sls_valuation::clear_overflow_bits(svector<digit_t>& bits) const { 
        for (unsigned i = bw; i < nw * sizeof(digit_t) * 8; ++i)
            set(bits, i, false);
    }

    bool sls_valuation::get_below(svector<digit_t> const& src, svector<digit_t>& dst) {
        for (unsigned i = 0; i < nw; ++i)
            dst[i] = (src[i] & ~fixed[i]) | (fixed[i] & bits[i]);
        for (unsigned i = 0; i < nw; ++i)
            dst[i] = fixed[i] & bits[i];
        if (gt(dst, src))
            return false;
        if (!in_range(dst)) {
            // lo < hi:
            // set dst to lo, except for fixed bits
            // 
            if (gt(hi, lo)) {

            }
        }         
        return true;
    }

    void sls_valuation::set_value(svector<digit_t>& bits, rational const& n) {       
        for (unsigned i = 0; i < bw; ++i) 
            set(bits, i, n.get_bit(i)); 
        clear_overflow_bits(bits);
    }

    void sls_valuation::get_value(svector<digit_t> const& bits, rational& r) const {
        rational p(1);
        for (unsigned i = 0; i < nw; ++i) {
            r += p * rational(bits[i]);
            p *= rational::power_of_two(bw);
        }
    }

    void sls_valuation::get(svector<digit_t>& dst) const {
        for (unsigned i = 0; i < nw; ++i)
            dst[i] = bits[i];
    }

    void sls_valuation::set1(svector<digit_t>& bits) {
        for (unsigned i = 0; i < bw; ++i)
            set(bits, i, true);
    }
    
    //
    // new_bits != bits => ~fixed
    // 0 = (new_bits ^ bits) & fixed
    // also check that new_bits are in range
    //
    bool sls_valuation::can_set(svector<digit_t> const& new_bits) const {        
        for (unsigned i = 0; i < nw; ++i)
            if (0 != ((new_bits[i] ^ bits[i]) & fixed[i]))
                return false;        
        return in_range(new_bits);
    }

    unsigned sls_valuation::to_nat(svector<digit_t> const& d, unsigned max_n) {
        SASSERT(max_n < UINT_MAX / 2);
        unsigned p = 1;
        unsigned value = 0;
        for (unsigned i = 0; i < bw; ++i) {
            if (p >= max_n) {
                for (unsigned j = i; j < bw; ++j)
                    if (get(d, j))
                        return max_n;
                return value;
            }
            if (get(d, i)) 
                value += p;            
            p <<= 1;
        }
        return value;
    }

    void sls_valuation::add_range(rational l, rational h) {
        l = mod(l, rational::power_of_two(bw));
        h = mod(h, rational::power_of_two(bw));
        if (h == l)
            return;
        if (eq(lo, hi)) {
            set_value(lo, l);
            set_value(hi, h);
            return;
        }
        
        // TODO: intersect with previous range, if any
        set_value(lo, l);
        set_value(hi, h);       
    }

}
