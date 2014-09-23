/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    fixed_bit_vector.cpp

Abstract:

    Simple bitvector implementation for fixed size bit-vectors.

Author:

    Nikolaj Bjorner (nbjorner) 2014-9-15.
    Leonardo de Moura (leonardo) 2006-10-03.

Revision History:
    Based on bit_vector.cpp

--*/

#include<limits.h>
#include"fixed_bit_vector.h"
#include"trace.h"
#include"hash.h"

void fixed_bit_vector::set(fixed_bit_vector const& other, unsigned hi, unsigned lo) {
    if ((lo % 32) == 0) {
        unsigned sz32 = (hi-lo+1)/32;
        unsigned lo32 = lo/32;
        for (unsigned i = 0; i < sz32; ++i) {
            m_data[lo32 + i] = other.m_data[i];
        }
        for (unsigned i = sz32*32; i < hi - lo + 1; ++i) {
            set(lo + i, other.get(i));
        }
        return;
    }
    for (unsigned i = 0; i < hi - lo + 1; ++i) {
        set(lo + i, other.get(i));
    }
}

fixed_bit_vector_manager::fixed_bit_vector_manager(unsigned num_bits):
    m_alloc("fixed_bit_vector") {
    m_num_bits = num_bits;
    m_num_words = num_words(num_bits);
    m_num_bytes = m_num_words * sizeof(unsigned);
    unsigned bit_rest = m_num_bits % 32;
    m_mask = (1U << bit_rest) - 1;
    if (m_mask == 0) m_mask = UINT_MAX;
}


fixed_bit_vector* fixed_bit_vector_manager::allocate() {
    if (m_num_bytes == 0) return &m_0;
    return static_cast<fixed_bit_vector*>(m_alloc.allocate(m_num_bytes));
}

fixed_bit_vector* fixed_bit_vector_manager::allocate0() {
    fixed_bit_vector* result = allocate();
    fill0(*result);
    return result;
}

fixed_bit_vector* fixed_bit_vector_manager::allocate1() {
    fixed_bit_vector* result = allocate();
    fill1(*result);
    return result;
}

fixed_bit_vector* fixed_bit_vector_manager::allocate(fixed_bit_vector const& bv) {
    fixed_bit_vector* result = allocate();
    copy(*result, bv);
    return result;
}

void fixed_bit_vector_manager::deallocate(fixed_bit_vector* bv) {
    if (m_num_bytes > 0) m_alloc.deallocate(m_num_bytes, bv);
}


void fixed_bit_vector_manager::copy(fixed_bit_vector& dst, fixed_bit_vector const& src) const {
    memcpy(dst.m_data, src.m_data, num_bytes());
}


fixed_bit_vector& 
fixed_bit_vector_manager::fill0(fixed_bit_vector& bv) const {
    memset(bv.m_data, 0, num_bytes());
    return bv;
}

fixed_bit_vector& 
fixed_bit_vector_manager::fill1(fixed_bit_vector& bv) const {
    memset(bv.m_data, 0xFF, num_bytes());
    return bv;
}

fixed_bit_vector& 
fixed_bit_vector_manager::set_and(fixed_bit_vector& dst, fixed_bit_vector const& src) const {
    for (unsigned i = 0; i < m_num_words; i++) 
        dst.m_data[i] &= src.m_data[i];
    return dst;
}

fixed_bit_vector& 
fixed_bit_vector_manager::set_or(fixed_bit_vector& dst,  fixed_bit_vector const& src) const {
    for (unsigned i = 0; i < m_num_words; i++) 
        dst.m_data[i] |= src.m_data[i];
    return dst;
}

fixed_bit_vector& 
fixed_bit_vector_manager::set_neg(fixed_bit_vector& dst) const {
    for (unsigned i = 0; i < m_num_words; i++) 
        dst.m_data[i] = ~dst.m_data[i];
    return dst;
}

unsigned fixed_bit_vector_manager::last_word(fixed_bit_vector const& bv) const {
    unsigned n = num_words();
    if (n == 0) return 0;
    return bv.m_data[n-1] & m_mask;
}

bool fixed_bit_vector_manager::equals(fixed_bit_vector const& a, fixed_bit_vector const& b) const {
    if (&a == &b) return true;
    unsigned n = num_words();
    if (n == 0)
        return true;
    for (unsigned i = 0; i < n - 1; i++) {
        if (a.m_data[i] != b.m_data[i])
            return false;
    }
    return last_word(a) == last_word(b);
}
unsigned fixed_bit_vector_manager::hash(fixed_bit_vector const& src) const {
    return string_hash(reinterpret_cast<char const* const>(src.m_data), num_bits()/8, num_bits());
}

bool fixed_bit_vector_manager::contains(fixed_bit_vector const& a, fixed_bit_vector const& b) const {
    unsigned n = num_words();
    if (n == 0)
        return true;
    
    for (unsigned i = 0; i < n - 1; ++i) {
        if ((a.m_data[i] & b.m_data[i]) != b.m_data[i])
            return false;
    }
    unsigned b_data = last_word(b);
    return (last_word(a) & b_data) == b_data;
}

std::ostream& fixed_bit_vector_manager::display(std::ostream& out, fixed_bit_vector const& b) const {
    unsigned i = num_bits();
    while (i > 0) {
        --i;
        if (b.get(i))
            out << "1";
        else
            out << "0";
    }
    return out;
}



