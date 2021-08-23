/*++
Copyright (c) 2021 Jamey Sharp

Module Name:

    bit_blaster_adder

Abstract:

    Combinational logic adder for bit-blasting

Author:

    Jamey Sharp <jamey@minilop.net> 2021-08-19

--*/

#include "ast/rewriter/bit_blaster/bit_blaster_adder.h"

bit_blaster_adder::bit_blaster_adder(bool_rewriter & rewriter, unsigned sz, numeral const & value):
    m_rewriter(rewriter),
    m_constant(value)
{
    reduce();
    expr_ref_vector empty(m());
    m_variable.resize(sz, empty);
}

bit_blaster_adder::bit_blaster_adder(bool_rewriter & rewriter, unsigned sz, expr * const * bits):
    bit_blaster_adder(rewriter, sz)
{
    for (unsigned i = 0; i < sz; i++)
        add_bit(i, bits[i]);
}

void bit_blaster_adder::sum_bits(vector< expr_ref_vector > & columns, expr_ref_vector & out_bits) const {
    SASSERT(out_bits.empty());

    expr_ref_vector carries(m());
    expr_ref tmp1(m()), tmp2(m()), tmp3(m());

    for (auto & column : columns) {
        column.append(carries);
        carries.reset();

        while (column.size() >= 3) {
            expr * a = column.back();
            column.pop_back();
            expr * b = column.back();
            column.pop_back();
            expr * c = column.back();
            column.pop_back();

            m_rewriter.mk_xor(a, b, tmp1);
            m_rewriter.mk_xor(tmp1, c, tmp2);
            column.push_back(tmp2);

            m_rewriter.mk_and(a, b, tmp2);
            m_rewriter.mk_and(tmp1, c, tmp3);
            // tmp2 and tmp3 can't be true at the same time, so use
            // whichever of mk_or vs mk_xor makes the most sense here.
            m_rewriter.mk_or(tmp2, tmp3, tmp1);
            carries.push_back(tmp1);
        }

        if (column.size() == 2) {
            expr * a = column.back();
            column.pop_back();
            expr * b = column.back();
            column.pop_back();

            m_rewriter.mk_xor(a, b, tmp1);
            column.push_back(tmp1);

            m_rewriter.mk_and(a, b, tmp1);
            carries.push_back(tmp1);
        }

        out_bits.push_back(column.get(0, m().mk_false()));
    }

    SASSERT(out_bits.size() == size());
}

void bit_blaster_adder::variable_bits(expr_ref_vector & out_bits) const {
    vector< expr_ref_vector > columns(m_variable);
    sum_bits(columns, out_bits);
}

void bit_blaster_adder::total_bits(expr_ref_vector & out_bits) const {
    vector< expr_ref_vector > columns(m_variable);

    expr_ref one(m());
    one = m().mk_true();
    for (unsigned i = 0; i < size(); i++)
        if (m_constant.get_bit(i))
            columns[i].push_back(one);

    sum_bits(columns, out_bits);
}

bit_blaster_adder & bit_blaster_adder::add_shifted(bit_blaster_adder const & other, unsigned shift) {
    add_shifted(other.m_constant, shift);
    for (unsigned i = 0; shift + i < size(); i++)
        m_variable[shift + i].append(other.m_variable[i]);
    return *this;
}

bit_blaster_adder & bit_blaster_adder::add_shifted(unsigned sz, expr * const * bits, unsigned shift) {
    if (sz > size() - shift)
        sz = size() - shift;
    for (unsigned i = 0; i < sz; i++)
        add_bit(shift + i, bits[i]);
    return *this;
}
