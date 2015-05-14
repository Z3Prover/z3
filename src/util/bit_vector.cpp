/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bitvector.cpp

Abstract:

    Simple bitvector implementation

Author:

    Leonardo de Moura (leonardo) 2006-10-03.

Revision History:

--*/
#include<limits.h>
#include"bit_vector.h"
#include"trace.h"

#define DEFAULT_CAPACITY 2

#define MK_MASK(_num_bits_) ((1U << _num_bits_) - 1)

void bit_vector::expand_to(unsigned new_capacity) {
    if (m_data) {
        m_data = (unsigned*)memory::reallocate(m_data, new_capacity * sizeof(unsigned));
    } else {
        m_data = alloc_svect(unsigned, new_capacity);
    }
    memset(m_data + m_capacity, 0, (new_capacity - m_capacity) * sizeof(unsigned));
    m_capacity = new_capacity;
}

void bit_vector::resize(unsigned new_size, bool val) {
    if (new_size <= m_num_bits) {
        m_num_bits = new_size;
        return;
    }
 
    TRACE("bit_vector", tout << "expanding: " << new_size << " capacity: " << m_capacity << " num words: " 
          << num_words(new_size) << "\n";);

    if (num_words(new_size) > m_capacity) {
        expand_to((num_words(new_size) * 3 + 1) >> 1);
    }


    unsigned bwidx   = m_num_bits/32;
    unsigned ewidx   = num_words(new_size);
    unsigned * begin = m_data + bwidx;
    unsigned pos     = m_num_bits % 32;
    unsigned mask    = MK_MASK(pos);
    int      cval;

    if (val) {
        *begin |= ~mask;
        cval    = ~0;
    }
    else {
        *begin &= mask;
        cval    = 0;
    }

    TRACE("bit_vector",
          tout << "num_bits: " << m_num_bits << "\n";
          tout << "bwidx:    " << bwidx << "\n";
          tout << "ewidx:    " << ewidx << "\n";
          tout << "pos:      " << pos << "\n";
          tout << "mask:     " << std::hex << mask << "\n" << std::dec;
          tout << "cval:     " << cval << "\n";);

    if (bwidx < ewidx) {
        memset(begin + 1, cval, (ewidx - bwidx - 1) * sizeof(unsigned));
    }
    
    m_num_bits = new_size;
}

void bit_vector::shift_right(unsigned k) {
    if (k == 0)
        return;
    unsigned new_num_bits  = m_num_bits + k;
    unsigned old_num_words = num_words(m_num_bits);
    unsigned new_num_words = num_words(new_num_bits);
    resize(m_num_bits + k, false);
    unsigned bit_shift  = k % (8 * sizeof(unsigned));
    unsigned word_shift = k / (8 * sizeof(unsigned));
    if (word_shift > 0) {
        unsigned j = old_num_words;
        unsigned i = old_num_words + word_shift;
        while (j > 0) {
            --j; --i;
            m_data[i] = m_data[j];
        }
        while (i > 0) {
            --i;
            m_data[i] = 0;
        }
    }
    if (bit_shift > 0) {
        DEBUG_CODE({
            for (unsigned i = 0; i < word_shift; i++) {
                SASSERT(m_data[i] == 0);
            }
        });
        unsigned comp_shift = (8 * sizeof(unsigned)) - bit_shift;
        unsigned prev = 0;
        for (unsigned i = word_shift; i < new_num_words; i++) {
            unsigned new_prev = (m_data[i] >> comp_shift);
            m_data[i] <<= bit_shift;
            m_data[i] |= prev;
            prev = new_prev;
        }
    }
}

bool bit_vector::operator==(bit_vector const & source) const {
    if (m_num_bits != source.m_num_bits)
        return false;
    unsigned n = num_words();
    if (n == 0)
        return true;
    unsigned i;
    for (i = 0; i < n - 1; i++) {
        if (m_data[i] != source.m_data[i])
            return false;
    }
    unsigned bit_rest = source.m_num_bits % 32;
    unsigned mask = MK_MASK(bit_rest);
    if (mask == 0) mask = UINT_MAX;
    return (m_data[i] & mask) == (source.m_data[i] & mask);
}

bit_vector & bit_vector::operator|=(bit_vector const & source) {
    if (size() < source.size())
        resize(source.size(), false);
    unsigned n2 = source.num_words();
    SASSERT(n2 <= num_words());
    unsigned bit_rest = source.m_num_bits % 32;
    if (bit_rest == 0) {
        unsigned i = 0;
        for (i = 0; i < n2; i++)
            m_data[i] |= source.m_data[i];
    }
    else {
        unsigned i = 0;
        for (i = 0; i < n2 - 1; i++)
            m_data[i] |= source.m_data[i];
        unsigned mask = MK_MASK(bit_rest);
        m_data[i] |= source.m_data[i] & mask;
    }
    return *this;
}

bit_vector & bit_vector::operator&=(bit_vector const & source) {
    unsigned n1 = num_words();
    unsigned n2 = source.num_words();
    if (n1 == 0)
        return *this;
    if (n2 > n1) {
        for (unsigned i = 0; i < n1; i++)
            m_data[i] &= source.m_data[i];
    }
    else {
        SASSERT(n2 <= n1);
        unsigned bit_rest = source.m_num_bits % 32;
        unsigned i = 0;
        if (bit_rest == 0) {
            for (i = 0; i < n2; i++)
                m_data[i] &= source.m_data[i];
        }
        else {
            for (i = 0; i < n2 - 1; i++)
                m_data[i] &= source.m_data[i];
            unsigned mask = MK_MASK(bit_rest);
            m_data[i] &= (source.m_data[i] & mask);
            
        }
        for (i = n2; i < n1; i++)
            m_data[i] = 0;
    }
    return *this;
}

void bit_vector::display(std::ostream & out) const {
#if 1
    unsigned i = m_num_bits;
    while (i > 0) {
        --i;
        if (get(i))
            out << "1";
        else
            out << "0";
    }
#else
    for (unsigned i = 0; i < m_num_bits; i++) {
        if (get(i))
            out << "1";
        else
            out << "0";
        if ((i + 1) % 32 == 0) out << "\n";
    } 
#endif
}

bool bit_vector::contains(bit_vector const& other) const {
    unsigned n = num_words();
    if (n == 0)
        return true;
    
    for (unsigned i = 0; i < n - 1; ++i) {
        if ((m_data[i] & other.m_data[i]) != other.m_data[i])
            return false;
    }
    unsigned bit_rest = m_num_bits % 32;
    unsigned mask = (1U << bit_rest) - 1;
    if (mask == 0) mask = UINT_MAX;
    unsigned other_data = other.m_data[n-1] & mask;
    return (m_data[n-1] & other_data) == other_data;
}

unsigned bit_vector::get_hash() const {
    return string_hash(reinterpret_cast<char const* const>(m_data), size()/8,  0);
}

bit_vector& bit_vector::neg() {
    unsigned n = num_words();
    for (unsigned i = 0; i < n; ++i) {
        m_data[i] = ~m_data[i];
    }
    return *this;
}

void fr_bit_vector::reset() {
    unsigned sz = size();
    unsigned_vector::const_iterator it  = m_one_idxs.begin();
    unsigned_vector::const_iterator end = m_one_idxs.end();
    for (; it != end; ++it) {
        unsigned idx = *it;
        if (idx < sz)
            unset(idx);
    }
    m_one_idxs.reset();
}
