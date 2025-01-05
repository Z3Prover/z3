/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_bv_valuation.h

Abstract:

    A Stochastic Local Search (SLS) engine

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07

--*/
#pragma once

#include "util/lbool.h"
#include "util/params.h"
#include "util/scoped_ptr_vector.h"
#include "util/uint_set.h"
#include "util/mpz.h"
#include "util/rational.h"

namespace sls {

    class bvect : public svector<digit_t> {
    public:
        unsigned bw = 0;
        unsigned nw = 0;
        unsigned mask = 0;

        bvect() = default;
        bvect(unsigned sz) : svector(sz, (unsigned)0) {}
        void set_bw(unsigned bw);

        void copy_to(unsigned nw, bvect & dst) const {
            SASSERT(nw <= this->size());
            for (unsigned i = 0; i < nw; ++i)
                dst[i] = (*this)[i];
        }

        void set(unsigned bit_idx, bool val) {
            auto _val = static_cast<digit_t>(0 - static_cast<digit_t>(val));
            get_bit_word(bit_idx) ^= (_val ^ get_bit_word(bit_idx)) & get_pos_mask(bit_idx);
        }

        bool get(unsigned bit_idx) const {
            return (get_bit_word(bit_idx) & get_pos_mask(bit_idx)) != 0;
        }

        unsigned parity() const {
            SASSERT(bw > 0);
            for (unsigned i = 0; i < nw; ++i)
                if ((*this)[i] != 0)
                    return (8 * sizeof(digit_t) * i) + trailing_zeros((*this)[i]);
            return bw;
        }

        void set_zero()  {
            for (unsigned i = 0; i < nw; ++i)
                (*this)[i] = 0;
        }

        bvect& set_shift_right(bvect const& a, bvect const& b);
        bvect& set_shift_right(bvect const& a, unsigned shift);
        bvect& set_shift_left(bvect const& a, bvect const& b);

        rational get_value(unsigned nw) const;

        unsigned to_nat(unsigned max_n) const;


        friend bool operator==(bvect const& a, bvect const& b);
        friend bool operator<(bvect const& a, bvect const& b);
        friend bool operator>(bvect const& a, bvect const& b);
        friend bool operator<=(bvect const& a, bvect const& b);
        friend bool operator>=(bvect const& a, bvect const& b);
        friend bool operator<=(digit_t a, bvect const& b);
        friend bool operator<=(bvect const& a, digit_t b);
        friend std::ostream& operator<<(std::ostream& out, bvect const& v);

    private:

        static digit_t get_pos_mask(unsigned bit_idx) {
            return (digit_t)1 << (digit_t)(bit_idx % (8 * sizeof(digit_t)));
        }

        digit_t get_bit_word(unsigned bit_idx) const {
            return (*this)[bit_idx / (8 * sizeof(digit_t))];
        }

        digit_t& get_bit_word(unsigned bit_idx) {
            return (*this)[bit_idx / (8 * sizeof(digit_t))];
        }
    };

    bool operator==(bvect const& a, bvect const& b);
    bool operator<(bvect const& a, bvect const& b);
    bool operator<=(bvect const& a, bvect const& b);
    bool operator>=(bvect const& a, bvect const& b);
    bool operator>(bvect const& a, bvect const& b);
    inline bool operator!=(bvect const& a, bvect const& b) { return !(a == b); }
    std::ostream& operator<<(std::ostream& out, bvect const& v);

    class bv_valuation {
    protected:
        bvect m_bits;
        bvect m_lo, m_hi;                   // range assignment to bit-vector, as wrap-around interval
        bvect m_is_fixed, m_fixed_values;   // fixed values
        bvect m_tmp;
        unsigned m_signed_prefix = 0;

        unsigned mask;

        void repair_sign_bits(bvect& dst) const;


    public:
        unsigned bw;                     // bit-width
        unsigned nw;                     // num words
        bvect eval;                      // current evaluation

        
        bv_valuation(unsigned bw);

        void set_bw(unsigned bw);
        void set_signed(unsigned prefix) { m_signed_prefix = prefix; }

        unsigned num_bytes() const { return (bw + 7) / 8; }

        digit_t bits(unsigned i) const { return m_bits[i]; }
        bvect const& bits() const { return m_bits; }
        bvect const& tmp_bits(bool use_current) const { return use_current ? m_bits : m_tmp; }
        bvect const& fixed() const { return m_is_fixed; }
        digit_t fixed(unsigned i) const { return m_is_fixed[i]; }
        void set_fixed_bit(unsigned i, bool bit) { m_is_fixed.set(i, true); m_fixed_values.set(i, bit); }
        void set_fixed_word(unsigned i, digit_t mask, digit_t value) { m_is_fixed[i] = mask; m_fixed_values[i] = value; }
        bool commit_eval_check_tabu();
        void commit_eval_ignore_tabu();
        bool is_fixed() const { for (unsigned i = bw; i-- > 0; ) if (!m_is_fixed.get(i)) return false; return true; }

        bool get_bit(unsigned i) const { return m_bits.get(i); }
        bool try_set_bit(unsigned i, bool b) {
            SASSERT(in_range(m_bits));
            if (m_is_fixed.get(i) && m_fixed_values.get(i) != b)
                return false;
            m_bits.set(i, b);   
            eval.set(i, b);
            if (in_range(m_bits))
                return true;
            m_bits.set(i, !b);
            eval.set(i, !b);
            return false;
        }

        void set_value(bvect& bits, rational const& r);

        rational get_value() const { return m_bits.get_value(nw); }
        rational get_eval() const { return eval.get_value(nw); }
        rational lo() const { return m_lo.get_value(nw); }
        rational hi() const { return m_hi.get_value(nw); }

        unsigned diff_index(bvect const& a) const;
        void inf_feasible(bvect& a) const;
        void sup_feasible(bvect& a) const;

        void get(bvect& dst) const;
        void add_range(rational lo, rational hi);
        bool has_range() const { return m_lo != m_hi; }
        void tighten_range();

        void save_value() { m_bits.copy_to(nw, m_tmp); }
        void restore_value() { m_tmp.copy_to(nw, m_bits); }

        void clear_overflow_bits(bvect& bits) const {
            SASSERT(nw > 0);
            bits[nw - 1] &= mask;
            SASSERT(!has_overflow(bits));
        }

        bool in_range(bvect const& bits) const;
        bool can_set(bvect const& bits) const;

        bool eq(bv_valuation const& other) const { return eq(other.m_bits); }
        bool eq(bvect const& other) const { return other == m_bits; }

        bool is_zero() const { return is_zero(m_bits); }
        bool is_zero(bvect const& a) const { 
            for (unsigned i = 0; i < nw - 1; ++i)
                if (a[i] != 0)
                    return false;
            return (a[nw - 1] & mask) == 0;          
        }

        bool is_ones() const { return is_ones(m_bits); }

        bool is_ones(bvect const& a) const {
            SASSERT(!has_overflow(a));
            for (unsigned i = 0; i + 1 < nw; ++i)
                if (0 != ~a[i])
                    return false;
            return 0 == (mask & ~a[nw - 1]);
        }

        bool is_one() const { return is_one(m_bits); }
        bool is_one(bvect const& a) const {
            SASSERT(!has_overflow(a));
            for (unsigned i = 1; i < nw; ++i)
                if (0 != a[i])
                    return false;
            return 1 == a[0];
        }

        bool sign() const { return m_bits.get(bw - 1); }

        bool has_overflow(bvect const& bits) const { return 0 != (bits[nw - 1] & ~mask); }

        unsigned parity(bvect const& bits) const { return bits.parity(); }

        void min_feasible(bvect& out) const;
        void max_feasible(bvect& out) const;

        // most significant bit or bw if src = 0
        unsigned msb(bvect const& src) const;

        unsigned clz(bvect const& src) const;

        bool is_power_of2(bvect const& src) const;

        // retrieve largest number at or below (above) src which is feasible
        // with respect to fixed, lo, hi.
        bool get_at_most(bvect const& src, bvect& dst) const;
        bool get_at_least(bvect const& src, bvect& dst) const;

        bool set_random_at_most(bvect const& src, random_gen& r);
        bool set_random_at_least(bvect const& src, random_gen& r);
        bool set_random_in_range(bvect const& lo, bvect const& hi, random_gen& r);

        bool set_repair(bool try_down, bvect& dst);
        void set_random_above(bvect& dst, random_gen& r);
        void set_random_below(bvect& dst, random_gen& r);
        bool set_random(random_gen& r);
        void round_down(bvect& dst, std::function<bool(bvect const&)> const& is_feasible);
        void round_up(bvect& dst, std::function<bool(bvect const&)> const& is_feasible);


        static digit_t random_bits(random_gen& r);
        void get_variant(bvect& dst, random_gen& r) const;
        

        bool try_set(bvect const& src) {
            if (!can_set(src))
                return false;
            set(src);
            return true;
        }

        void set(bvect const& src) {
            for (unsigned i = nw; i-- > 0; )
                eval[i] = src[i];
            clear_overflow_bits(eval);
        }

        void set_zero(bvect& out) const {            
            for (unsigned i = 0; i < nw; ++i)
                out[i] = 0;
        }

        void set_one(bvect& out) const {
            for (unsigned i = 1; i < nw; ++i)
                out[i] = 0;
            out[0] = 1;
        }

        void set_zero() {
            set_zero(eval);
        }

        void sub1(bvect& out) const {
            for (unsigned i = 0; i < bw; ++i) {
                if (out.get(i)) {
                    out.set(i, false);
                    return;
                }
                else
                    out.set(i, true);
            }
        }

        void add1(bvect& out) const {
            for (unsigned i = 0; i < bw; ++i) {
                if (!out.get(i)) {
                    out.set(i, true);
                    return;
                }
                else
                    out.set(i, false);
            }
        }

        void set_sub(bvect& out, bvect const& a, bvect const& b) const;
        bool set_add(bvect& out, bvect const& a, bvect const& b) const;
        bool set_mul(bvect& out, bvect const& a, bvect const& b, bool check_overflow = true) const;
        void shift_right(bvect& out, unsigned shift) const;

        void set_range(bvect& dst, unsigned lo, unsigned hi, bool b) {
            for (unsigned i = lo; i < hi; ++i)
                dst.set(i, b);
        }

        bool try_set_range(bvect& dst, unsigned lo, unsigned hi, bool b) {
            for (unsigned i = lo; i < hi; ++i)
                if (m_is_fixed.get(i) && get_bit(i) != b)
                    return false;
            for (unsigned i = lo; i < hi; ++i)
                dst.set(i, b);
            return true;
        }

        void set(bvect& dst, unsigned v) const {
            dst[0] = v;
            for (unsigned i = 1; i < nw; ++i)
                dst[i] = 0;
        }

        void set(bvect& dst, bvect const& src) const {
            for (unsigned i = 0; i < nw; ++i)
                dst[i] = src[i];
        }

        unsigned to_nat(unsigned max_n) const;

        std::ostream& display(std::ostream& out) const {
            out << m_bits;
            out << " ev: " << eval;
            if (!is_zero(m_is_fixed)) 
                out << " fixed bits: " << m_is_fixed << " fixed value: " << m_fixed_values;            
            if (m_lo != m_hi) 
                out << " [" << m_lo << ", " << m_hi << "[";            
            return out;
        }

        bool well_formed() const {
            return !has_overflow(m_bits) && (!has_range() || in_range(m_fixed_values));
        }

    };

    inline std::ostream& operator<<(std::ostream& out, bv_valuation const& v) { return v.display(out); }

}
