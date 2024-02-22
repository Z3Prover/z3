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
            if (lt(dst, lo))
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

    bool sls_valuation::set_repair(bool try_down, svector<digit_t>& dst) {
        for (unsigned i = 0; i < nw; ++i)
            dst[i] = (~fixed[i] & dst[i]) | (fixed[i] & bits[i]);
        bool ok = try_down ? round_down(dst) : round_up(dst);
        if (!ok)
            VERIFY(try_down ? round_up(dst) : round_down(dst));
        if (eq(bits, dst))
            return false;
        set(bits, dst);
        SASSERT(!has_overflow(dst));
        return true;
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
        r = 0;
        for (unsigned i = 0; i < nw; ++i) {
            r += p * rational(bits[i]);
            p *= rational::power_of_two(8*sizeof(digit_t));
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

    void sls_valuation::shift_right(svector<digit_t>& out, unsigned shift) const {
        SASSERT(shift < bw);
        for (unsigned i = 0; i < bw; ++i)
            set(out, i, i + shift < bw ? get(bits, i + shift) : false);
        SASSERT(!has_overflow(out));
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
        init_fixed();
    }

    //
    // tighten lo/hi based on fixed bits.
    //   lo[bit_i] != fixedbit[bit_i] 
    //     let bit_i be most significant bit position of disagreement.
    //     if fixedbit = 1, lo = 0, increment lo
    //     if fixedbit = 0, lo = 1, lo := fixed & bits
    //   (hi-1)[bit_i] != fixedbit[bit_i]
    //     if fixedbit = 0, hi-1 = 1, set hi-1 := 0, maximize below bit_i
    //     if fixedbit = 1, hi-1 = 0, hi := fixed & bits
    // tighten fixed bits based on lo/hi
    //  lo + 1 = hi -> set bits = lo
    //  lo < hi, set most significant bits based on hi
    //
    void sls_valuation::init_fixed() {
        if (eq(lo, hi))
            return;
        for (unsigned i = bw; i-- > 0; ) {
            if (!get(fixed, i))
                continue;
            if (get(bits, i) == get(lo, i))
                continue;
            if (get(bits, i)) {
                set(lo, i, true);
                for (unsigned j = i; j-- > 0; )
                    set(lo, j, get(fixed, j) && get(bits, j));
            }
            else {
                for (unsigned j = bw; j-- > 0; )
                    set(lo, j, get(fixed, j) && get(bits, j));
            }
            break;
        }
        svector<digit_t> hi1(nw + 1, (unsigned)0);
        svector<digit_t> one(nw + 1, (unsigned)0);
        one[0] = 1;
        digit_t c;
        mpn_manager().sub(hi.data(), nw, one.data(), nw, hi1.data(), &c);
        clear_overflow_bits(hi1);
        for (unsigned i = bw; i-- > 0; ) {
            if (!get(fixed, i))
                continue;
            if (get(bits, i) == get(hi1, i))
                continue;
            if (get(hi1, i)) {
                set(hi1, i, false);
                for (unsigned j = i; j-- > 0; )
                    set(hi1, j, !get(fixed, j) || get(bits, j));
            }
            else {
                for (unsigned j = bw; j-- > 0; )
                    set(hi1, j, get(fixed, j) && get(bits, j));
            }
            mpn_manager().add(hi1.data(), nw, one.data(), nw, hi.data(), nw + 1, &c);
            clear_overflow_bits(hi);
            break;
        }

        // set fixed bits based on bounds
        auto set_fixed_bit = [&](unsigned i, bool b) {
            if (!get(fixed, i)) {
                set(fixed, i, true);
                set(bits, i, b);
            }
        };

        // set most significant bits
        if (lt(lo, hi)) {
            unsigned i = bw;
            for (; i-- > 0 && !get(hi, i); ) 
                set_fixed_bit(i, false);
            
            if (is_power_of2(hi))
                set_fixed_bit(i, false);
        }

        // lo + 1 = hi: then bits = lo
        mpn_manager().add(lo.data(), nw, one.data(), nw, hi1.data(), nw + 1, &c);
        clear_overflow_bits(hi1);
        if (eq(hi1, hi)) {
            for (unsigned i = 0; i < bw; ++i)
                set_fixed_bit(i, get(lo, i));            
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

    bool sls_valuation::set_mul(svector<digit_t>& out, svector<digit_t> const& a, svector<digit_t> const& b, bool check_overflow) const {
        mpn_manager().mul(a.data(), nw, b.data(), nw, out.data());

        bool ovfl = false;
        if (check_overflow) {
            ovfl = has_overflow(out);
            for (unsigned i = nw; i < 2 * nw; ++i)
                ovfl |= out[i] != 0;
        }
        clear_overflow_bits(out);
        return ovfl;
    }

    bool sls_valuation::is_power_of2(svector<digit_t> const& src) const {
        unsigned c = 0;
        for (unsigned i = 0; i < nw; ++i)
            c += get_num_1bits(src[i]);
        return c == 1;
    }

}
