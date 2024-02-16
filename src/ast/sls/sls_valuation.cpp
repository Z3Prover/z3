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
            set(fixed, i, true);
    }

    sls_valuation::~sls_valuation() {
    }

    bool sls_valuation::is_feasible() const {
        return true;
        mpn_manager m;
        unsigned nb = (bw + 7) / 8;
        auto c = m.compare(lo.data(), nb, hi.data(), nb);
        if (c == 0)
            return true;
        if (c < 0)
            return 
                m.compare(lo.data(), nb, bits.data(), nb) <= 0 && 
                m.compare(bits.data(), nb, hi.data(), nb) < 0;
        return 
            m.compare(lo.data(), nb, bits.data(), nb) <= 0 || 
            m.compare(bits.data(), nb, hi.data(), nb) < 0;
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

    void sls_valuation::clear_overflow_bits(svector<digit_t>& bits) const { 
        for (unsigned i = bw; i < nw * sizeof(digit_t) * 8; ++i)
            set(bits, i, false);
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
    
    bool sls_valuation::can_set(svector<digit_t> const& new_bits) const {
        for (unsigned i = 0; i < nw; ++i)
            if (bits[i] != ((new_bits[i] & ~fixed[i]) | (bits[i] & fixed[i])))
                return true;
        return false;
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
        set_value(this->lo, l);
        set_value(this->hi, h);
        // TODO: intersect with previous range, if any

    }

}
