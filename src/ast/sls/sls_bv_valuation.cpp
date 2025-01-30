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

#include "ast/sls/sls_bv_valuation.h"

namespace sls {

    void bvect::set_bw(unsigned bw) {
        this->bw = bw;
        nw = (bw + sizeof(digit_t) * 8 - 1) / (8 * sizeof(digit_t));
        mask = (1 << (bw % (8 * sizeof(digit_t)))) - 1;
        if (mask == 0)
            mask = ~(digit_t)0;
        reserve(nw + 1);     
    }

    bool operator==(bvect const& a, bvect const& b) {
        if (a.nw == 1)
            return a[0] == b[0];
        SASSERT(a.nw > 0);
        return 0 == memcmp(a.data(), b.data(), a.nw * sizeof(digit_t));
    }

    bool operator<(bvect const& a, bvect const& b) {
        SASSERT(a.nw > 0);       
        return mpn_manager().compare(a.data(), a.nw, b.data(), a.nw) < 0;
    }

    bool operator>(bvect const& a, bvect const& b) {
        SASSERT(a.nw > 0);
        return mpn_manager().compare(a.data(), a.nw, b.data(), a.nw) > 0;
    }

    bool operator<=(bvect const& a, bvect const& b) {
        SASSERT(a.nw > 0);
        return mpn_manager().compare(a.data(), a.nw, b.data(), a.nw) <= 0;
    }

    bool operator>=(bvect const& a, bvect const& b) {
        SASSERT(a.nw > 0);
        return mpn_manager().compare(a.data(), a.nw, b.data(), a.nw) >= 0;
    }

    bool operator<=(digit_t a, bvect const& b) {
        for (unsigned i = 1; i < b.nw; ++i)
            if (0 != b[i])
                return true;
        return mpn_manager().compare(&a, 1, b.data(), 1) <= 0;
    }

    bool operator<=(bvect const& a, digit_t b) {
        for (unsigned i = 1; i < a.nw; ++i)
            if (0 != a[i])
                return false;
        return mpn_manager().compare(a.data(), 1, &b, 1) <= 0;
    }

    std::ostream& operator<<(std::ostream& out, bvect const& v) {
        out << std::hex;
        bool nz = false;
        for (unsigned i = v.nw; i-- > 0;) {
            auto w = v[i];
            if (i + 1 == v.nw)
                w &= v.mask;
            if (nz)
                out << std::setw(8) << std::setfill('0') << w;
            else if (w != 0)
                out << w, nz = true;
        }
        if (!nz)
            out << "0";
        out << std::dec;
        return out;
    }

    rational bvect::get_value(unsigned nw) const {
        rational p(1), r(0);
        for (unsigned i = 0; i < nw; ++i) {
            r += p * rational((*this)[i]);
            if (i + 1 < nw)
                p *= rational::power_of_two(8 * sizeof(digit_t));
        }
        return r;
    }


    unsigned bvect::to_nat(unsigned max_n) const {
        SASSERT(max_n < UINT_MAX / 2);
        unsigned p = 1;
        unsigned value = 0;
        for (unsigned i = 0; i < bw; ++i) {
            if (p >= max_n) {
                for (unsigned j = i; j < bw; ++j)
                    if (get(j))
                        return max_n;
                return value;
            }
            if (get(i))
                value += p;
            p <<= 1;
        }
        return value;
    }

    bvect& bvect::set_shift_right(bvect const& a, bvect const& b) {
        SASSERT(a.bw == b.bw);
        unsigned shift = b.to_nat(b.bw);
        return set_shift_right(a, shift);
    }

    bvect& bvect::set_shift_right(bvect const& a, unsigned shift) {
        set_bw(a.bw);
        if (shift == 0)
            a.copy_to(a.nw, *this);
        else if (shift >= a.bw)
            set_zero();
        else
            for (unsigned i = 0; i < bw; ++i)
                set(i, i + shift < bw ? a.get(i + shift) : false);
        return *this;
    }

    bvect& bvect::set_shift_left(bvect const& a, bvect const& b) {
        set_bw(a.bw);
        SASSERT(a.bw == b.bw);
        unsigned shift = b.to_nat(b.bw);

        if (shift == 0)
            a.copy_to(a.nw, *this);
        else if (shift >= a.bw)
            set_zero();
        else
            for (unsigned i = bw; i-- > 0; )
                set(i, i >= shift ? a.get(i - shift) : false);
        return *this;
    }

    bv_valuation::bv_valuation(unsigned bw) {
        set_bw(bw);
        m_lo.set_bw(bw);
        m_hi.set_bw(bw);
        m_bits.set_bw(bw);
        m_tmp.set_bw(bw);
        m_is_fixed.set_bw(bw);
        m_fixed_values.set_bw(bw);
        eval.set_bw(bw);
        // have lo, hi bits, fixed point to memory allocated within this of size num_bytes each allocated        
        for (unsigned i = 0; i < nw; ++i)
            m_lo[i] = 0, m_hi[i] = 0, m_bits[i] = 0, m_is_fixed[i] = 0, eval[i] = 0, m_fixed_values[i] = 0;
        m_is_fixed[nw - 1] = ~mask;
    }

    void bv_valuation::set_bw(unsigned b) {
        bw = b;
        nw = (bw + sizeof(digit_t) * 8 - 1) / (8 * sizeof(digit_t));
        mask = (1 << (bw % (8 * sizeof(digit_t)))) - 1;
        if (mask == 0)
            mask = ~(digit_t)0;
    }

    bool bv_valuation::commit_eval_check_tabu() { 
        for (unsigned i = 0; i < nw; ++i)
            if (0 != (m_is_fixed[i] & (m_fixed_values[i] ^ eval[i])))                 
                return false;            
        if (!in_range(eval)) 
            return false;        
        commit_eval_ignore_tabu();
        return true;
    }

    void bv_valuation::commit_eval_ignore_tabu() {
        for (unsigned i = 0; i < nw; ++i)
            m_bits[i] = eval[i];
        SASSERT(well_formed());
    }

    bool bv_valuation::in_range(bvect const& bits) const {
        mpn_manager m;
        auto c = m.compare(m_lo.data(), nw, m_hi.data(), nw);
        SASSERT(!has_overflow(bits));
        // full range

        if (c == 0)
            return true;
        // lo < hi: then lo <= bits & bits < hi
        if (c < 0)
            return
            m.compare(m_lo.data(), nw, bits.data(), nw) <= 0 &&
            m.compare(bits.data(), nw, m_hi.data(), nw) < 0;
        // hi < lo: bits < hi or lo <= bits
        return
            m.compare(m_lo.data(), nw, bits.data(), nw) <= 0 ||
            m.compare(bits.data(), nw, m_hi.data(), nw) < 0;
    }

    //
    // largest dst <= src and dst is feasible
    //

    bool bv_valuation::get_at_most(bvect const& src, bvect& dst) const {
        SASSERT(!has_overflow(src));
        src.copy_to(nw, dst);
        sup_feasible(dst);
        if (can_set(dst)) 
            return true;
        
        if (dst < m_lo && m_lo < m_hi) // dst < lo < hi 
            return false;
        if (is_zero(m_hi))
            return false;
        m_hi.copy_to(nw, dst); // hi <= dst < lo or lo < hi <= dst
        sub1(dst);       
        SASSERT(can_set(dst));
        return true;
    }

    //
    // smallest dst >= src and dst is feasible with respect to this.
    bool bv_valuation::get_at_least(bvect const& src, bvect& dst) const {
        SASSERT(!has_overflow(src));
        src.copy_to(nw, dst);
        dst.set_bw(bw);
        inf_feasible(dst);
        if (can_set(dst))
            return true;        

        if (dst > m_lo)
            return false;
        m_lo.copy_to(nw, dst);
        SASSERT(can_set(dst));
        return true;
    }

    bool bv_valuation::set_random_at_most(bvect const& src, random_gen& r) {
        m_tmp.set_bw(bw);
        //verbose_stream() << "set_random_at_most " << src << "\n";
        if (!get_at_most(src, m_tmp))
            return false;

        if (is_zero(m_tmp) && (0 != r(2)))
            return try_set(m_tmp) && m_tmp <= src;

        // random value below tmp
        set_random_below(m_tmp, r);

        //verbose_stream() << "can set " << m_tmp << " " << can_set(m_tmp) << "\n";
        
        return (can_set(m_tmp) || get_at_most(src, m_tmp)) && m_tmp <= src && try_set(m_tmp);
    }

    bool bv_valuation::set_random_at_least(bvect const& src, random_gen& r) {
        m_tmp.set_bw(bw);
        if (!get_at_least(src, m_tmp))
            return false;

        if (is_ones(m_tmp) && (0 != r(10)))
            return try_set(m_tmp);

        // random value at least tmp
        set_random_above(m_tmp, r);

        return (can_set(m_tmp) || get_at_least(src, m_tmp)) && src <= m_tmp && try_set(m_tmp);
    }

    bool bv_valuation::set_random_in_range(bvect const& lo, bvect const& hi, random_gen& r) {
        bvect& tmp = m_tmp;
        if (0 == r(2)) {
            if (!get_at_least(lo, tmp))
                return false;
            SASSERT(in_range(tmp));
            if (hi < tmp)
                return false;
            set_random_above(tmp, r);
            round_down(tmp, [&](bvect const& t) { return hi >= t && in_range(t); });
            if (in_range(tmp) || get_at_least(lo, tmp))
                return lo <= tmp && tmp <= hi && try_set(tmp);
        }
        else {
            if (!get_at_most(hi, tmp))
                return false;
            SASSERT(in_range(tmp));
            if (lo > tmp)
                return false;
            set_random_below(tmp, r);
            round_up(tmp, [&](bvect const& t) { return lo <= t && in_range(t); });
            if (in_range(tmp) || get_at_most(hi, tmp))
                return lo <= tmp && tmp <= hi && try_set(tmp);
        }
        return false;
    }

    void bv_valuation::round_down(bvect& dst, std::function<bool(bvect const&)> const& is_feasible) {      
        for (unsigned i = bw; !is_feasible(dst) && i-- > 0; )
            if (!m_is_fixed.get(i) && dst.get(i))
                dst.set(i, false);      
        repair_sign_bits(dst);
    }

    void bv_valuation::round_up(bvect& dst, std::function<bool(bvect const&)> const& is_feasible) {
        for (unsigned i = 0; !is_feasible(dst) && i < bw; ++i)
            if (!m_is_fixed.get(i) && !dst.get(i))
                dst.set(i, true);
        repair_sign_bits(dst);
    }

    void bv_valuation::set_random_above(bvect& dst, random_gen& r) {
        for (unsigned i = 0; i < nw; ++i)
            dst[i] = dst[i] | (random_bits(r) & ~m_is_fixed[i]);
        repair_sign_bits(dst);
    }

    void bv_valuation::set_random_below(bvect& dst, random_gen& r) {
        if (is_zero(dst))
            return;
        unsigned n = 0, idx = UINT_MAX;
        for (unsigned i = 0; i < bw; ++i)
            if (dst.get(i) && !m_is_fixed.get(i) && (r() % ++n) == 0)
                idx = i;                

        if (idx == UINT_MAX)
            return;
        dst.set(idx, false);
        for (unsigned i = 0; i < idx; ++i) 
            if (!m_is_fixed.get(i))
                dst.set(i, r() % 2 == 0);
        repair_sign_bits(dst);
    }

    bool bv_valuation::set_repair(bool try_down, bvect& dst) {
        for (unsigned i = 0; i < nw; ++i)
            dst[i] = (~m_is_fixed[i] & dst[i]) | (m_is_fixed[i] & m_bits[i]);
        clear_overflow_bits(dst);
        repair_sign_bits(dst);
        if (try_set(dst))
            return true;
        bool repaired = false;
        dst.set_bw(bw);
        if (m_lo < m_hi) {
            for (unsigned i = bw; m_hi <= dst && !in_range(dst) && i-- > 0; )
                if (!m_is_fixed.get(i) && dst.get(i))
                    dst.set(i, false);
            for (unsigned i = 0; i < bw && dst < m_lo && !in_range(dst); ++i)
                if (!m_is_fixed.get(i) && !dst.get(i))
                    dst.set(i, true);
        }
        else {
            for (unsigned i = 0; !in_range(dst) && i < bw; ++i)
                if (!m_is_fixed.get(i) && !dst.get(i))
                    dst.set(i, true);
            for (unsigned i = bw; !in_range(dst) && i-- > 0;)
                if (!m_is_fixed.get(i) && dst.get(i))
                    dst.set(i, false);
        }
        repair_sign_bits(dst);
        repaired = try_set(dst);
        dst.set_bw(0);
        return repaired;
    }

    void bv_valuation::min_feasible(bvect& out) const {
        if (m_lo < m_hi) 
            m_lo.copy_to(nw, out);        
        else {
            for (unsigned i = 0; i < nw; ++i)
                out[i] = m_is_fixed[i] & m_bits[i];
        }
        repair_sign_bits(out);
        SASSERT(!has_overflow(out));
    }

    void bv_valuation::max_feasible(bvect& out) const {
        if (m_lo < m_hi) {
            m_hi.copy_to(nw, out);
            sub1(out);
        }
        else {
            for (unsigned i = 0; i < nw; ++i)
                out[i] = ~m_is_fixed[i] | m_bits[i];
        }
        repair_sign_bits(out);
        SASSERT(!has_overflow(out));
    }

    unsigned bv_valuation::msb(bvect const& src) const {
        SASSERT(!has_overflow(src));
        for (unsigned i = nw; i-- > 0; )
            if (src[i] != 0)
                return i * 8 * sizeof(digit_t) + log2(src[i]);
        return bw;
    }

    unsigned bv_valuation::clz(bvect const& src) const {
        SASSERT(!has_overflow(src));
        unsigned i = bw;
        for (; i-- > 0; )
            if (!src.get(i))
                return bw - 1 - i;
        return bw;
    }


    void bv_valuation::set_value(bvect& bits, rational const& n) {
        for (unsigned i = 0; i < bw; ++i)
            bits.set(i, n.get_bit(i));
        clear_overflow_bits(bits);
    }

    void bv_valuation::get(bvect& dst) const {
        m_bits.copy_to(nw, dst);
    }

    digit_t bv_valuation::random_bits(random_gen& rand) {
        digit_t r = 0;
        for (digit_t i = 0; i < sizeof(digit_t); ++i)
            r ^= rand() << (8 * i);
        return r;
    }

    void bv_valuation::get_variant(bvect& dst, random_gen& r) const {
        for (unsigned i = 0; i < nw; ++i)
            dst[i] = (random_bits(r) & ~m_is_fixed[i]) | (m_is_fixed[i] & m_bits[i]);
        repair_sign_bits(dst);
        clear_overflow_bits(dst);
    }

    bool bv_valuation::set_random(random_gen& r) {
        get_variant(m_tmp, r);
        repair_sign_bits(m_tmp);
        if (try_set(m_tmp))
            return true;

        for (unsigned i = 0; i < nw; ++i)
            m_tmp[i] = random_bits(r);
        clear_overflow_bits(m_tmp);
        // find a random offset within [lo, hi[
        SASSERT(m_lo != m_hi);
        set_sub(eval, m_hi, m_lo);        
        for (unsigned i = bw; i-- > 0 && m_tmp >= eval; ) 
            m_tmp.set(i, false);
        
        // set eval back to m_bits. It was garbage.
        set(eval, m_bits);

        // tmp := lo + tmp is within [lo, hi[
        set_add(m_tmp, m_tmp, m_lo);
        // respect fixed bits
        for (unsigned i = 0; i < bw; ++i)
            if (m_is_fixed.get(i))
                m_tmp.set(i, m_bits.get(i));                
        // decrease tmp until it is in range again
        for (unsigned i = bw; i-- > 0 && !in_range(m_tmp); )
            if (!m_is_fixed.get(i))
                m_tmp.set(i, false);
        repair_sign_bits(m_tmp);
        return try_set(m_tmp);      
    }

    void bv_valuation::repair_sign_bits(bvect& dst) const {
        if (m_signed_prefix == 0)
            return;
        bool sign = m_signed_prefix == bw ? dst.get(bw - 1) : dst.get(bw - m_signed_prefix - 1);
        for (unsigned i = bw; i-- > bw - m_signed_prefix; ) {
            if (dst.get(i) != sign) {
                if (m_is_fixed.get(i)) {
                    unsigned j = bw - m_signed_prefix;
                    if (j > 0 && !m_is_fixed.get(j - 1))
                        dst.set(j - 1, !sign);
                    for (unsigned i = bw; i-- > bw - m_signed_prefix; )
                        if (!m_is_fixed.get(i))
                            dst.set(i, !sign);
                    return;
                }
                else
                    dst.set(i, sign);
            }
        }
    }

    //
    // new_bits != bits => ~fixed
    // 0 = (new_bits ^ bits) & fixedf
    // also check that new_bits are in range
    //
    bool bv_valuation::can_set(bvect const& new_bits) const {
        SASSERT(!has_overflow(new_bits));
        for (unsigned i = 0; i < nw; ++i)
            if (0 != ((new_bits[i] ^ m_fixed_values[i]) & m_is_fixed[i]))
                return false;
        return in_range(new_bits);
    }

    unsigned bv_valuation::to_nat(unsigned max_n) const {
        bvect const& d = m_bits;
        SASSERT(!has_overflow(d));
        return d.to_nat(max_n);
    }

    void bv_valuation::shift_right(bvect& out, unsigned shift) const {
        SASSERT(shift < bw);
        for (unsigned i = 0; i < bw; ++i)
            out.set(i, i + shift < bw ? out.get(i + shift) : false);
        SASSERT(well_formed());
    }

    void bv_valuation::add_range(rational l, rational h) {   

        l = mod(l, rational::power_of_two(bw));
        h = mod(h, rational::power_of_two(bw));
        if (h == l)
            return;

        //verbose_stream() << *this << " lo " << l << " hi " << h << " --> ";

        if (m_lo == m_hi) {
            set_value(m_lo, l);
            set_value(m_hi, h);
        }
        else {            
            auto old_lo = lo();
            auto old_hi = hi();
            if (old_lo < old_hi) {
                if (old_lo < l && l < old_hi && old_hi <= h)
                    set_value(m_lo, l),
                    old_lo = l;
                if (l <= old_lo && old_lo < h && h < old_hi)
                    set_value(m_hi, h);
            }
            else {
                SASSERT(old_hi < old_lo);
                if (h <= old_hi && old_lo <= l) {
                    set_value(m_lo, l);
                    set_value(m_hi, h);
                }
                else if (old_lo <= l && l <= h) {
                    set_value(m_lo, l);
                    set_value(m_hi, h);
                }
                else if (old_lo + 1 == l) 
                    set_value(m_lo, l);                
                else if (old_hi == h + 1)
                    set_value(m_hi, h);                
                else if (old_hi == h && old_lo < l)
                    set_value(m_lo, l);
                else if (old_lo == l && h < old_hi)
                    set_value(m_hi, h);
            }
        }

        SASSERT(!has_overflow(m_lo));
        SASSERT(!has_overflow(m_hi));

        //verbose_stream() << *this << " --> ";

        tighten_range();

        //verbose_stream() << *this << "\n";
        SASSERT(well_formed());
    }

    //
    // update bits based on ranges
    //

    unsigned bv_valuation::diff_index(bvect const& a) const {
        unsigned index = 0;
        for (unsigned i = nw; i-- > 0; ) {
            auto diff = m_is_fixed[i] & (m_fixed_values[i] ^ a[i]);
            if (diff != 0 && index == 0)
                index = 1 + i * 8 * sizeof(digit_t) + log2(diff);
        }
        return index;
    }

    // The least a' >= a, such that the fixed bits in bits agree with a'.
    // 0 if there is no such a'.
    void bv_valuation::inf_feasible(bvect& a) const {
        unsigned lo_index = diff_index(a);
        
        if (lo_index == 0)
            return;
        --lo_index;

        // decrement a[lo_index:0] maximally
        SASSERT(a.get(lo_index) != m_fixed_values.get(lo_index));
        SASSERT(m_is_fixed.get(lo_index));
        for (unsigned i = 0; i <= lo_index; ++i) {
            if (!m_is_fixed.get(i))
                a.set(i, false);
            else if (m_is_fixed.get(i))
                a.set(i, m_fixed_values.get(i));
        }

        // the previous value of a[lo_index] was 0.
        // a[lo_index:0] was incremented, so no need to adjust bits a[:lo_index+1]
        if (a.get(lo_index))
            return;

        // find the minimal increment within a[:lo_index+1]
        for (unsigned i = lo_index + 1; i < bw; ++i) {
            if (!m_is_fixed.get(i) && !a.get(i)) {
                a.set(i, true);
                return;
            }
        }
        // there is no feasiable value a' >= a, so find the least
        // feasiable value a' >= 0.
        for (unsigned i = 0; i < bw; ++i)
            if (!m_is_fixed.get(i))
                a.set(i, false);
    }

    // The greatest a' <= a, such that the fixed bits in bits agree with a'.
    // the greatest a' <= -1 if there is no such a'.

    void bv_valuation::sup_feasible(bvect& a) const {
        unsigned hi_index = diff_index(a);
        if (hi_index == 0)
            return;
        --hi_index;
        SASSERT(a.get(hi_index) != m_fixed_values.get(hi_index));
        SASSERT(m_is_fixed.get(hi_index));

        // increment a[hi_index:0] maximally
        for (unsigned i = 0; i <= hi_index; ++i) {
            if (!m_is_fixed.get(i))
                a.set(i, true);
            else if (m_is_fixed.get(i))
                a.set(i, m_fixed_values.get(i));
        }

        // If a[hi_index:0] was decremented, then no need to adjust bits a[:hi_index+1]
        if (!a.get(hi_index))
            return;

        // find the minimal decrement within a[:hi_index+1]
        for (unsigned i = hi_index + 1; i < bw; ++i) {
            if (!m_is_fixed.get(i) && a.get(i)) {
                a.set(i, false);
                return;
            }
        }

        // a[hi_index:0] was incremented, but a[:hi_index+1] cannot be decremented.
        // maximize a[:hi_index+1] to model wrap around behavior.
        for (unsigned i = hi_index + 1; i < bw; ++i) 
            if (!m_is_fixed.get(i)) 
                a.set(i, true);       
    }

    void bv_valuation::tighten_range() {
        
        if (!has_range())
            return;     

        inf_feasible(m_lo);

        bvect& hi1 = m_tmp;
        hi1.set_bw(bw);
        m_hi.copy_to(nw, hi1);
        sub1(hi1);
        sup_feasible(hi1);
        add1(hi1);
        hi1.copy_to(nw, m_hi);

        if (!has_range())
            return;

        if (!in_range(m_bits) || !in_range(m_fixed_values)) {
            if (!can_set(m_lo))
                return;
            m_lo.copy_to(nw, m_fixed_values);
            m_lo.copy_to(nw, m_bits);
        }        

        if (mod(lo() + 1, rational::power_of_two(bw)) == hi())
            for (unsigned i = 0; i < nw; ++i)
                m_is_fixed[i] = ~0;      
        if (lo() < hi() && hi() < rational::power_of_two(bw - 1))
            for (unsigned i = 0; i < bw; ++i)
                if (hi() < rational::power_of_two(i))
                    m_is_fixed.set(i, true);
        
        SASSERT(well_formed());
    }

    void bv_valuation::set_sub(bvect& out, bvect const& a, bvect const& b) const {
        digit_t c;
        mpn_manager().sub(a.data(), nw, b.data(), nw, out.data(), &c);
        clear_overflow_bits(out);
    }

    bool bv_valuation::set_add(bvect& out, bvect const& a, bvect const& b) const {
        digit_t c;
        mpn_manager().add(a.data(), nw, b.data(), nw, out.data(), nw + 1, &c);
        bool ovfl = out[nw] != 0 || has_overflow(out);
        clear_overflow_bits(out);
        return ovfl;
    }

    bool bv_valuation::set_mul(bvect& out, bvect const& a, bvect const& b, bool check_overflow) const {
        out.reserve(2 * nw);
        SASSERT(out.size() >= 2 * nw);
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

    bool bv_valuation::is_power_of2(bvect const& src) const {
        unsigned c = 0;
        for (unsigned i = 0; i < nw; ++i)
            c += get_num_1bits(src[i]);
        return c == 1;
    }
}
