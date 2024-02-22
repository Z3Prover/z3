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

    class sls_valuation {
    protected:
        svector<digit_t> m_bits;
    public:
        unsigned bw;                     // bit-width
        unsigned nw;                     // num words
        svector<digit_t> lo, hi;        // range assignment to bit-vector, as wrap-around interval
        svector<digit_t> fixed;    // bit assignment and don't care bit
        sls_valuation(unsigned bw);

        unsigned num_bytes() const { return (bw + 7) / 8; }

        digit_t bits(unsigned i) const { return m_bits[i]; }
        svector<digit_t> const& bits() const { return m_bits; }
        void set_bit(unsigned i, bool v) { set(m_bits, i, v); }
        bool get_bit(unsigned i) const { return get(m_bits, i); }

        void set_value(svector<digit_t>& bits, rational const& r);
        void get_value(svector<digit_t> const& bits, rational& r) const;
        void get(svector<digit_t>& dst) const;
        void add_range(rational lo, rational hi);
        void init_fixed();
        void set1(svector<digit_t>& bits);

        void clear_overflow_bits(svector<digit_t>& bits) const;
        bool in_range(svector<digit_t> const& bits) const;
        bool can_set(svector<digit_t> const& bits) const;

        bool eq(sls_valuation const& other) const { return eq(other.m_bits); }

        bool eq(svector<digit_t> const& other) const { return eq(other, m_bits); }
        bool eq(svector<digit_t> const& a, svector<digit_t> const& b) const;
        bool gt(svector<digit_t> const& a, svector<digit_t> const& b) const;
        bool lt(svector<digit_t> const& a, svector<digit_t> const& b) const;
        bool le(svector<digit_t> const& a, svector<digit_t> const& b) const;

        bool is_zero() const { return is_zero(m_bits); }
        bool is_zero(svector<digit_t> const& a) const {
            for (unsigned i = 0; i < nw; ++i)
                if (a[i] != 0)
                    return false;
            return true;
        }
        bool is_ones() const { return is_ones(m_bits); }
        bool is_ones(svector<digit_t> const& a) const {
            auto bound = bw % (sizeof(digit_t) * 8) == 0 ? nw : nw - 1;
            for (unsigned i = 0; i < bound; ++i)
                if (a[i] != (a[i] ^ 0))
                    return false;
            if (bound < nw) {
                for (unsigned i = bound * sizeof(digit_t) * 8; i < bw; ++i)
                    if (!get(a, i))
                        return false;
            }
            return true;
        }

        bool is_one() const { return is_one(m_bits); }
        bool is_one(svector<digit_t> const& bits) const {
            if (1 != bits[0])
                return false;
            for (unsigned i = 1; i < nw; ++i)
                if (0 != bits[i])
                    return false;
            return true;
        }

        bool sign() const { return get(m_bits, bw - 1); }

        bool has_overflow(svector<digit_t> const& bits) const {
            for (unsigned i = bw; i < nw * sizeof(digit_t) * 8; ++i)
                if (get(bits, i))
                    return true;
            return false;
        }

        unsigned parity(svector<digit_t> const& bits) const {
            for (unsigned i = 0; i < nw; ++i)
                if (bits[i] != 0)
                    return (8 * sizeof(digit_t) * i) + trailing_zeros(bits[i]);
            return bw;
        }

        void min_feasible(svector<digit_t>& out) const;
        void max_feasible(svector<digit_t>& out) const;

        // most significant bit or bw if src = 0
        unsigned msb(svector<digit_t> const& src) const;

        bool is_power_of2(svector<digit_t> const& src) const;

        // retrieve largest number at or below (above) src which is feasible
        // with respect to fixed, lo, hi.
        bool get_at_most(svector<digit_t> const& src, svector<digit_t>& dst) const;
        bool get_at_least(svector<digit_t> const& src, svector<digit_t>& dst) const;
        bool round_up(svector<digit_t>& dst) const;
        bool round_down(svector<digit_t>& dst) const;
        bool set_repair(bool try_down, svector<digit_t>& dst);

        bool try_set(svector<digit_t> const& src) {
            if (!can_set(src))
                return false;
            set(src);
            return true;
        }

        void set(svector<digit_t> const& src) {
            for (unsigned i = nw; i-- > 0; )
                m_bits[i] = src[i];
            clear_overflow_bits(m_bits);
        }

        void set_zero(svector<digit_t>& out) const {
            for (unsigned i = 0; i < nw; ++i)
                out[i] = 0;
        }

        void set_one(svector<digit_t>& out) const {
            for (unsigned i = 1; i < nw; ++i)
                out[i] = 0;
            out[0] = 1;
        }

        void set_zero() {
            set_zero(m_bits);
        }

        void sub1(svector<digit_t>& out) const {
            for (unsigned i = 0; i < bw; ++i) {
                if (get(out, i)) {
                    set(out, i, false);
                    return;
                }
                else
                    set(out, i, true);
            }
        }

        void set_sub(svector<digit_t>& out, svector<digit_t> const& a, svector<digit_t> const& b) const;
        bool set_add(svector<digit_t>& out, svector<digit_t> const& a, svector<digit_t> const& b) const;
        bool set_mul(svector<digit_t>& out, svector<digit_t> const& a, svector<digit_t> const& b, bool check_overflow = true) const;
        void shift_right(svector<digit_t>& out, unsigned shift) const;

        void set_range(svector<digit_t>& dst, unsigned lo, unsigned hi, bool b) {
            for (unsigned i = lo; i < hi; ++i)
                set(dst, i, b);
        }

        void set(svector<digit_t>& d, unsigned bit_idx, bool val) const {
            auto _val = static_cast<digit_t>(0 - static_cast<digit_t>(val));
            get_bit_word(d, bit_idx) ^= (_val ^ get_bit_word(d, bit_idx)) & get_pos_mask(bit_idx);
        }

        void set(svector<digit_t>& dst, unsigned v) const {
            dst[0] = v;
            for (unsigned i = 1; i < nw; ++i)
                dst[i] = 0;
        }

        void set(svector<digit_t>& dst, svector<digit_t> const& src) const {
            for (unsigned i = 0; i < nw; ++i)
                dst[i] = src[i];
        }

        bool get(svector<digit_t> const& d, unsigned bit_idx) const {
            return (get_bit_word(d, bit_idx) & get_pos_mask(bit_idx)) != 0;
        }

        unsigned to_nat(svector<digit_t> const& d, unsigned max_n);



        std::ostream& display(std::ostream& out) const {
            out << "V:";
            out << std::hex;
            auto print_bits = [&](svector<digit_t> const& v) {
                bool nz = false;
                for (unsigned i = nw; i-- > 0;)
                    if (nz)
                        out << std::setw(8) << std::setfill('0') << v[i];
                    else if (v[i] != 0)
                        out << v[i], nz = true;
                if (!nz)
                    out << "0";
                };

            print_bits(m_bits);
            out << " fix:";
            print_bits(fixed);

            if (!eq(lo, hi)) {
                out << " [";
                print_bits(lo);
                out << ", ";
                print_bits(hi);
                out << "[";
            }
            out << std::dec;
            return out;
        }

    private:
        static digit_t get_pos_mask(unsigned bit_idx) {
            return (digit_t)1 << (digit_t)(bit_idx % (8 * sizeof(digit_t)));
        }

        static digit_t get_bit_word(svector<digit_t> const& bits, unsigned bit_idx) {
            return bits[bit_idx / (8 * sizeof(digit_t))];
        }

        static digit_t& get_bit_word(svector<digit_t>& bits, unsigned bit_idx) {
            return bits[bit_idx / (8 * sizeof(digit_t))];
        }
    };

    class sls_pre_valuation : public sls_valuation {
    public:
        sls_pre_valuation(unsigned bw):sls_valuation(bw) {}
        svector<digit_t>& bits() { return m_bits; }
    };

    inline std::ostream& operator<<(std::ostream& out, sls_valuation const& v) { return v.display(out); }

}
