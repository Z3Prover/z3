/*++
Copyright (c) 2021 Jamey Sharp

Module Name:

    bit_blaster_adder

Abstract:

    Combinational logic adder for bit-blasting

Author:

    Jamey Sharp <jamey@minilop.net> 2021-08-19

--*/

#pragma once

#include "ast/ast.h"
#include "ast/rewriter/bool_rewriter.h"
#include "util/rational.h"

class bit_blaster_adder {
public:
    typedef rational numeral;

    bit_blaster_adder(bool_rewriter & rewriter, unsigned sz, numeral const & value = numeral::zero());
    bit_blaster_adder(bool_rewriter & rewriter, unsigned sz, expr * const * bits);

    bit_blaster_adder(bool_rewriter & rewriter, expr_ref_vector & value):
        bit_blaster_adder(rewriter, value.size(), value.data()) {}

    bit_blaster_adder(bit_blaster_adder const & other):
        bit_blaster_adder(other.m_rewriter, other.size()) {
        *this += other;
    }

    bit_blaster_adder(bit_blaster_adder &&) noexcept = default;

    // Return the sum of the known-constant inputs to this adder.
    void constant_bits(numeral & value) const {
        value = m_constant % power(size());
    }

    // Return the sum of the non-constant inputs to this adder.
    void variable_bits(expr_ref_vector & out_bits) const;

    // Return the sum of all inputs to this adder.
    void total_bits(expr_ref_vector & out_bits) const;

    unsigned size() const {
        return m_variable.size();
    }

    ast_manager & m() const {
        return m_rewriter.m();
    }

    bit_blaster_adder & operator+=(bit_blaster_adder const & other) {
        SASSERT(size() == other.size());
        return add_shifted(other, 0);
    }

    bit_blaster_adder & add_bit(unsigned idx, bool bit) {
        SASSERT(idx < size());
        if (bit)
            m_constant += power(idx);
        return *this;
    }

    bit_blaster_adder & add_bit(unsigned idx, expr * bit) {
        SASSERT(idx < size());
        if (m().is_true(bit))
            m_constant += power(idx);
        else if (!m().is_false(bit))
            m_variable[idx].push_back(bit);
        return *this;
    }

    bit_blaster_adder & add_bit(unsigned idx, expr_ref & bit) {
        return add_bit(idx, bit.get());
    }

    bit_blaster_adder & add_shifted(bit_blaster_adder const & other, unsigned shift);
    bit_blaster_adder & add_shifted(unsigned sz, expr * const * bits, unsigned shift);

    bit_blaster_adder & add_shifted(expr_ref_vector const & bits, unsigned shift) {
        return add_shifted(bits.size(), bits.data(), shift);
    }

    bit_blaster_adder & add_shifted(numeral const & value, unsigned shift) {
        m_constant += value * power(shift);
        return *this;
    }

protected:
    bool_rewriter & m_rewriter;
    numeral m_constant;
    vector< expr_ref_vector > m_variable;

    numeral power(unsigned n) const { return numeral::power_of_two(n); }

    void sum_bits(vector< expr_ref_vector > & columns, expr_ref_vector & out_bits) const;
};
