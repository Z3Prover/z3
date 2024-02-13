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

    struct sls_valuation {
        unsigned bw;           // bit-width
        unsigned nw;           // num words
        svector<digit_t> lo,  hi;     // range assignment to bit-vector, as wrap-around interval
        svector<digit_t> bits, fixed;    // bit assignment and don't care bit
        bool is_feasible() const; // the current bit-evaluation is between lo and hi.
        sls_valuation(unsigned bw);
        ~sls_valuation();
        
        unsigned num_bytes() const { return (bw + 7) / 8; }

        void set_value(svector<digit_t>& bits, rational const& r);
        void get_value(svector<digit_t> const& bits, rational& r) const;
        void add_range(rational lo, rational hi);
        void set1(svector<digit_t>& bits);

        void clear_overflow_bits(svector<digit_t>& bits) const;
        bool can_set(svector<digit_t> const& bits) const;

        bool eq(sls_valuation const& other) const;

        bool gt(svector<digit_t> const& a, svector<digit_t> const& b) const {
            return 0 > memcmp(a.data(), b.data(), num_bytes());
        }

        unsigned parity(svector<digit_t> const& bits) const {
            unsigned i = 0;
            for (; i < bw && !get(bits, i); ++i);
            return i;               
        }

        bool try_set(svector<digit_t> const& src) {
            if (!can_set(src))
                return false;
            set(src);
            return true;
        }

        void set(svector<digit_t> const& src) {
            for (unsigned i = nw; i-- > 0; )
                bits[i] = src[i];
            clear_overflow_bits(bits);
        }

        void set_fixed(svector<digit_t> const& src) {
            for (unsigned i = nw; i-- > 0; )
                fixed[i] = src[i];
        }

        void set(svector<digit_t>& d, unsigned bit_idx, bool val) const {
            auto _val = static_cast<digit_t>(0 - static_cast<digit_t>(val));
            get_bit_word(d, bit_idx) ^= (_val ^ get_bit_word(d, bit_idx)) & get_pos_mask(bit_idx);
        }

        bool get(svector<digit_t> const& d, unsigned bit_idx) const {
            return (get_bit_word(d, bit_idx) & get_pos_mask(bit_idx)) != 0;
        }

        unsigned to_nat(svector<digit_t> const& d, unsigned max_n);

        static digit_t get_pos_mask(unsigned bit_idx) {
            return (digit_t)1 << (digit_t)(bit_idx % (8 * sizeof(digit_t)));
        }

        static digit_t get_bit_word(svector<digit_t> const& bits, unsigned bit_idx) {
            return bits[bit_idx / (8 * sizeof(digit_t))];
        }

        static digit_t& get_bit_word(svector<digit_t>& bits, unsigned bit_idx) {
            return bits[bit_idx / (8 * sizeof(digit_t))];
        }

        std::ostream& display(std::ostream& out) const {
            out << std::hex;
            for (unsigned i = 0; i < nw; ++i)
                out << bits[i];
            out << " ";
            for (unsigned i = 0; i < nw; ++i)
                out << fixed[i];
            out << std::dec;
            return out;
        }
    };

    inline std::ostream& operator<<(std::ostream& out, sls_valuation const& v) { return v.display(out); }

}
