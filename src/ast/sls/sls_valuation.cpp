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

    bool sls_valuation::in_range(svector<digit_t> const& bits) const {
        mpn_manager m;    
        auto c = m.compare(lo.data(), nw, hi.data(), nw);
        SASSERT(!has_overflow(bits));
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

    bool sls_valuation::eq(svector<digit_t> const& a, svector<digit_t> const& b) const {
        SASSERT(!has_overflow(a));
        SASSERT(!has_overflow(b));
        return 0 == memcmp(a.data(), b.data(), num_bytes());
    }

    bool sls_valuation::gt(svector<digit_t> const& a, svector<digit_t> const& b) const {
        SASSERT(!has_overflow(a));
        SASSERT(!has_overflow(b));
        mpn_manager m;
        return m.compare(a.data(), nw, b.data(), nw) > 0;
    }

    bool sls_valuation::lt(svector<digit_t> const& a, svector<digit_t> const& b) const {
        SASSERT(!has_overflow(a));
        SASSERT(!has_overflow(b));
        mpn_manager m;
        return m.compare(a.data(), nw, b.data(), nw) < 0;
    }

    bool sls_valuation::le(svector<digit_t> const& a, svector<digit_t> const& b) const {
        SASSERT(!has_overflow(a));
        SASSERT(!has_overflow(b));
        mpn_manager m;
        return m.compare(a.data(), nw, b.data(), nw) <= 0;
    }

    void sls_valuation::clear_overflow_bits(svector<digit_t>& bits) const { 
        for (unsigned i = bw; i < nw * sizeof(digit_t) * 8; ++i)
            set(bits, i, false);
        SASSERT(!has_overflow(bits));
    }

    //
    // largest dst <= src and dst is feasible
    // set dst := src & (~fixed | bits)
    // 
    // increment dst if dst < src by setting bits below msb(src & ~dst) to 1
    // 
    // if dst < lo < hi:
    //    return false
    // if lo < hi <= dst:
    //    set dst := hi - 1
    // if hi <= dst < lo
    //    set dst := hi - 1
    // 

    bool sls_valuation::get_at_most(svector<digit_t> const& src, svector<digit_t>& dst) const {
        SASSERT(!has_overflow(src));
        for (unsigned i = 0; i < nw; ++i)
            dst[i] = src[i] & (~fixed[i] | bits[i]);

        //
        // If dst < src, then find the most significant 
        // bit where src[idx] = 1, dst[idx] = 0
        // set dst[j] = bits_j | ~fixed_j for j < idx
        //
        for (unsigned i = nw; i-- > 0; ) {
            if (0 != (~dst[i] & src[i])) {
                auto idx = log2(~dst[i] & src[i]);
                auto mask = (1 << idx) - 1;
                dst[i] = (~fixed[i] & mask) | dst[i];
                for (unsigned j = i; j-- > 0; )
                    dst[j] = (~fixed[j] | bits[j]);
                break;
            }
        }
        SASSERT(!has_overflow(dst));
        return round_down(dst);
    }

    //
    // smallest dst >= src and dst is feasible with respect to this.
    // set dst := (src & ~fixed) | (fixed & bits)
    // 
    // decrement dst if dst > src by setting bits below msb to 0 unless fixed
    // 
    // if lo < hi <= dst
    //    return false
    // if dst < lo < hi:
    //    set dst := lo
    // if hi <= dst < lo
    //    set dst := lo
    // 
    bool sls_valuation::get_at_least(svector<digit_t> const& src, svector<digit_t>& dst) const {
        SASSERT(!has_overflow(src));
        for (unsigned i = 0; i < nw; ++i)
            dst[i] = (~fixed[i] & src[i]) | (fixed[i] & bits[i]);

        //
        // If dst > src, then find the most significant 
        // bit where src[idx] = 0, dst[idx] = 1
        // set dst[j] = dst[j] & fixed_j for j < idx
        //
        for (unsigned i = nw; i-- > 0; ) {
            if (0 != (dst[i] & ~src[i])) {
                auto idx = log2(dst[i] & ~src[i]);
                auto mask = (1 << idx);
                dst[i] = dst[i] & (fixed[i] | mask);
                for (unsigned j = i; j-- > 0; )
                    dst[j] = dst[j] & fixed[j];
                break;
            }
        }
        SASSERT(!has_overflow(dst));
        return round_up(dst);
    }

    bool sls_valuation::round_up(svector<digit_t>& dst) const {
        if (lt(lo, hi)) {
            if (le(hi, dst))
                return false;
            if (lt(dst, lo))
                set(dst, lo);
        }
        else if (le(hi, dst) && lt(dst, lo))
            set(dst, lo);
        SASSERT(!has_overflow(dst));
        return true;
    }

    bool sls_valuation::round_down(svector<digit_t>& dst) const {
        if (lt(lo, hi)) {
            if (lt(lo, hi))
                return false;
            if (le(hi, dst)) {
                set(dst, hi);
                sub1(dst);
            }
        }
        else if (le(hi, dst) && lt(dst, lo)) {
            set(dst, hi);
            sub1(dst);
        }
        SASSERT(!has_overflow(dst));
        return true;
    }

    void sls_valuation::set_repair(bool try_down, svector<digit_t>& dst) {
        for (unsigned i = 0; i < nw; ++i)
            dst[i] = (~fixed[i] & dst[i]) | (fixed[i] & bits[i]);
        bool ok = try_down ? round_down(dst) : round_up(dst);
        if (!ok)
            VERIFY(try_down ? round_up(dst) : round_down(dst));
        set(bits, dst);
        SASSERT(!has_overflow(dst));
    }

    void sls_valuation::min_feasible(svector<digit_t>& out) const {
        if (gt(hi, lo)) {
            for (unsigned i = 0; i < nw; ++i)
                out[i] = lo[i];
        }
        else {
            for (unsigned i = 0; i < nw; ++i)
                out[i] = fixed[i] & bits[i];
        }
        SASSERT(!has_overflow(out));
    }

    void sls_valuation::max_feasible(svector<digit_t>& out) const {
        if (gt(hi, lo)) {        
            for (unsigned i = 0; i < nw; ++i)
                out[i] = hi[i];
            sub1(out);
        }
        else {
            for (unsigned i = 0; i < nw; ++i)
                out[i] = ~fixed[i] | bits[i];
        }
        SASSERT(!has_overflow(out));
    }

    unsigned sls_valuation::msb(svector<digit_t> const& src) const {
        SASSERT(!has_overflow(src));
        for (unsigned i = nw; i-- > 0; ) 
            if (src[i] != 0)
                return i * 8 * sizeof(digit_t) + log2(src[i]);        
        return bw;
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
        SASSERT(!has_overflow(new_bits));
        for (unsigned i = 0; i < nw; ++i)
            if (0 != ((new_bits[i] ^ bits[i]) & fixed[i]))
                return false;        
        return in_range(new_bits);
    }

    unsigned sls_valuation::to_nat(svector<digit_t> const& d, unsigned max_n) {
        SASSERT(!has_overflow(d));
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
        }
        else {
            rational old_lo, old_hi;
            get_value(lo, old_lo);
            get_value(hi, old_hi);
            if (old_lo < old_hi) {
                if (old_lo < l && l < old_hi)
                    set_value(lo, l),
                    old_lo = l;
                if (old_hi < h && h < old_hi)
                    set_value(hi, h);
            }
            else {
                SASSERT(old_hi < old_lo);
                if (old_lo < l || l < old_hi)
                    set_value(lo, l),
                    old_lo = l;
                if (old_lo < h && h < old_hi)
                    set_value(hi, h);
                else if (old_hi < old_lo && (h < old_hi || old_lo < h))
                    set_value(hi, h);
            }
        }    
        SASSERT(!has_overflow(lo));
        SASSERT(!has_overflow(hi));
    }

    void sls_valuation::init_fixed() {
        if (eq(lo, hi))
            return;
        bool lo_ok = true;
        for (unsigned i = 0; i < nw; ++i)
            lo_ok &= (0 == (fixed[i] & (bits[i] ^ lo[i])));
        if (!lo_ok) {
            svector<digit_t> tmp(nw + 1);
            if (get_at_least(lo, tmp)) {
                if (lt(lo, hi) && lt(tmp, hi))
                    set(lo, tmp);                
                else if (gt(lo, hi))
                    set(lo, tmp);
            }
            else if (gt(lo, hi)) {
                svector<digit_t> zero(nw + 1, (unsigned) 0);
                if (get_at_least(zero, tmp) && lt(tmp, hi))
                    set(lo, tmp);
            }
        }
        bool hi_ok = true;
        svector<digit_t> hi1(nw + 1, (unsigned)0);
        svector<digit_t> one(nw + 1, (unsigned)0);
        one[0] = 1;
        digit_t c;
        mpn_manager().sub(hi.data(), nw, one.data(), nw, hi1.data(), &c);
        for (unsigned i = 0; i < nw; ++i)
            hi_ok &= (0 == (fixed[i] & (bits[i] ^ hi1[i])));
        if (!hi_ok) {
            svector<digit_t> tmp(nw + 1);
            if (get_at_most(hi1, tmp)) {
                if (lt(tmp, hi) && (le(lo, tmp) || lt(hi, lo))) {
                    mpn_manager().add(tmp.data(), nw, one.data(), nw, hi1.data(), nw + 1, &c);
                    clear_overflow_bits(hi1);
                    set(hi, hi1);
                }
            }
            // TODO other cases
        }

        // set most significant bits
        if (lt(lo, hi)) {
            unsigned i = bw;
            for (; i-- > 0; ) {
                if (get(hi, i))
                    break;
                if (!get(fixed, i)) {
                    set(fixed, i, true);
                    set(bits, i, false);
                }
            }
            bool is_power_of2 = true;
            for (unsigned j = 0; is_power_of2 && j < i; ++j)
                is_power_of2 = !get(hi, j);            
            if (is_power_of2) {
                if (!get(fixed, i)) {
                    set(fixed, i, true);
                    set(bits, i, false);
                }
            }
        }
        svector<digit_t> tmp(nw + 1, (unsigned)0);
        mpn_manager().add(lo.data(), nw, one.data(), nw, tmp.data(), nw + 1, &c);
        clear_overflow_bits(tmp);
        if (eq(tmp, hi)) {
            for (unsigned i = 0; i < bw; ++i) {
                if (!get(fixed, i)) {
                    set(fixed, i, true);
                    set(bits, i, get(lo, i));
                }
            }
        }
        SASSERT(!has_overflow(bits));
    }

    void sls_valuation::set_sub(svector<digit_t>& out, svector<digit_t> const& a, svector<digit_t> const& b) const {
        digit_t c;
        mpn_manager().sub(a.data(), nw, b.data(), nw, out.data(), &c);
        clear_overflow_bits(out);
    }

    bool sls_valuation::set_add(svector<digit_t>& out, svector<digit_t> const& a, svector<digit_t> const& b) const {
        digit_t c;
        mpn_manager().add(a.data(), nw, b.data(), nw, out.data(), nw + 1, &c);
        bool ovfl = out[nw] != 0 || has_overflow(out);
        clear_overflow_bits(out);
        return ovfl;
    }

    bool sls_valuation::set_mul(svector<digit_t>& out, svector<digit_t> const& a, svector<digit_t> const& b) const {
        mpn_manager().mul(a.data(), nw, b.data(), nw, out.data());
        bool ovfl = has_overflow(out);
        for (unsigned i = nw; i < 2 * nw; ++i)
            ovfl |= out[i] != 0;
        clear_overflow_bits(out);
        return ovfl;
    }

}
