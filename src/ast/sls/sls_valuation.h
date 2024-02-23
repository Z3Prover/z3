/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_valuation.h

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
#include "ast/ast.h"
#include "ast/sls/sls_stats.h"
#include "ast/sls/sls_powers.h"
#include "ast/bv_decl_plugin.h"

namespace bv {



    class bvect : public svector<digit_t> {
        unsigned bw = 0;
        unsigned nw = 0;
        unsigned mask = 0;
    public:
        bvect() {}
        bvect(unsigned sz): svector(sz, (unsigned)0) {}
        void set_bw(unsigned bw);

        void clear_overflow_bits();
        void set_sub(bvect const& a, bvect const& b);

        bool is_one() const {
            SASSERT(bw > 0);
            SASSERT(!has_overflow());
            for (unsigned i = 1; i < nw; ++i)
                if (0 != (*this)[i])
                    return false;
            return 1 == (*this)[0];
        }

        bool is_ones() const {
            SASSERT(bw > 0);
            auto const& a = *this;
            for (unsigned i = 0; i + 1 < nw; ++i)
                if (0 != ~a[i])
                    return false;
            return ((~a[nw - 1]) & mask) == 0;
        }

        bool is_zero() const {
            SASSERT(bw > 0);
            auto const& a = *this;
            for (unsigned i = 0; i + 1 < nw; ++i)
                if (a[i] != 0)
                    return false;
            return (a[nw - 1] & mask) == 0;
        }

        bool has_overflow() const {
            SASSERT(bw > 0);
            for (unsigned i = bw; i < nw * sizeof(digit_t) * 8; ++i)
                if (get(i))
                    return true;
            return false;
        }

        bool get(unsigned bit_idx) const {
            return (get_bit_word(bit_idx) & get_pos_mask(bit_idx)) != 0;
        }


        unsigned parity() const {
            SASSERT(bw > 0);
            SASSERT(!has_overflow());
            for (unsigned i = 0; i < nw; ++i)
                if ((*this)[i] != 0)
                    return (8 * sizeof(digit_t) * i) + trailing_zeros((*this)[i]);
            return bw;
        }

        friend bool operator==(bvect const& a, bvect const& b);
        friend bool operator<(bvect const& a, bvect const& b);
        friend bool operator>(bvect const& a, bvect const& b);
        friend bool operator<=(bvect const& a, bvect const& b);
        friend bool operator>=(bvect const& a, bvect const& b);

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

    class sls_valuation {
    protected:
        bvect m_bits;
        bvect lo, hi;        // range assignment to bit-vector, as wrap-around interval

        unsigned mask;
        rational get_value(bvect const& bits) const;
        bool round_up(bvect& dst) const;
        bool round_down(bvect& dst) const;

        std::ostream& print_bits(std::ostream& out, bvect const& bits) const;


    public:
        unsigned bw;                     // bit-width
        unsigned nw;                     // num words
        bvect fixed;                     // bit assignment and don't care bit
        sls_valuation(unsigned bw);

        unsigned num_bytes() const { return (bw + 7) / 8; }

        digit_t bits(unsigned i) const { return m_bits[i]; }
        bvect const& bits() const { return m_bits; }

        bool get_bit(unsigned i) const { return get(m_bits, i); }
        bool try_set_bit(unsigned i, bool b) {
            if (get(fixed, i) && get_bit(i) != b)
                return false;
            set(m_bits, i, b);
            return true;
        }

        void set_value(bvect& bits, rational const& r);

        rational get_value() const { return get_value(m_bits); }
        rational get_lo() const { return get_value(lo); }
        rational get_hi() const { return get_value(hi); }

        void get(bvect& dst) const;
        void add_range(rational lo, rational hi);
        bool has_range() const { return lo != hi; }
        void init_fixed();

        void clear_overflow_bits(bvect& bits) const { bits.clear_overflow_bits(); }
        bool in_range(bvect const& bits) const;
        bool can_set(bvect const& bits) const;

        bool eq(sls_valuation const& other) const { return eq(other.m_bits); }
        bool eq(bvect const& other) const { return other == m_bits; }

        bool is_zero() const { return m_bits.is_zero(); }
        bool is_zero(bvect const& a) const { return a.is_zero(); }

        bool is_ones() const { return m_bits.is_ones(); }

        bool is_one() const { return m_bits.is_one(); }
        // bool is_one(bvect const& a) const { return a.is_one(); }

        bool sign() const { return get(m_bits, bw - 1); }

        bool has_overflow(bvect const& bits) const { return bits.has_overflow(); }

        unsigned parity(bvect const& bits) const { return bits.parity(); }

        void min_feasible(bvect& out) const;
        void max_feasible(bvect& out) const;

        // most significant bit or bw if src = 0
        unsigned msb(bvect const& src) const;

        bool is_power_of2(bvect const& src) const;

        // retrieve largest number at or below (above) src which is feasible
        // with respect to fixed, lo, hi.
        bool get_at_most(bvect const& src, bvect& dst) const;
        bool get_at_least(bvect const& src, bvect& dst) const;

        bool set_repair(bool try_down, bvect& dst);

        bool try_set(bvect const& src) {
            if (!can_set(src))
                return false;
            set(src);
            return true;
        }

        void set(bvect const& src) {
            for (unsigned i = nw; i-- > 0; )
                m_bits[i] = src[i];
            clear_overflow_bits(m_bits);
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
            set_zero(m_bits);
        }

        void sub1(bvect& out) const {
            for (unsigned i = 0; i < bw; ++i) {
                if (get(out, i)) {
                    set(out, i, false);
                    return;
                }
                else
                    set(out, i, true);
            }
        }

        void set_sub(bvect& out, bvect const& a, bvect const& b) const;
        bool set_add(bvect& out, bvect const& a, bvect const& b) const;
        bool set_mul(bvect& out, bvect const& a, bvect const& b, bool check_overflow = true) const;
        void shift_right(bvect& out, unsigned shift) const;

        void set_range(bvect& dst, unsigned lo, unsigned hi, bool b) {
            for (unsigned i = lo; i < hi; ++i)
                set(dst, i, b);
        }

        void set(bvect& d, unsigned bit_idx, bool val) const {
            d.set(bit_idx, val);
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

        bool get(bvect const& d, unsigned bit_idx) const {
            return d.get(bit_idx);
        }

        unsigned to_nat(unsigned max_n);

        std::ostream& display(std::ostream& out) const {
            out << "V:";
            out << std::hex;

            print_bits(out, m_bits);
            out << " fix:";
            print_bits(out, fixed);

            if (lo != hi) {
                out << " [";
                print_bits(out, lo);
                out << ", ";
                print_bits(out, hi);
                out << "[";
            }
            out << std::dec;
            return out;
        }

        bool well_formed() const {
            return !has_overflow(m_bits) && (!has_range() || in_range(m_bits));
        }

    private:



    };

    class sls_pre_valuation : public sls_valuation {
    public:
        sls_pre_valuation(unsigned bw):sls_valuation(bw) {}
        bvect& bits() { return m_bits; }
        void set_bit(unsigned i, bool v) { set(m_bits, i, v); }
        
        
    };

    inline std::ostream& operator<<(std::ostream& out, sls_valuation const& v) { return v.display(out); }

}
