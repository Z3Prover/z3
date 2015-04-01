/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bit_vector.h

Abstract:

    Simple bitvector implementation.

Author:

    Leonardo de Moura (leonardo) 2006-10-03.

Revision History:

--*/
#ifndef _BIT_VECTOR_H_
#define _BIT_VECTOR_H_

#include<string.h>
#include"debug.h"
#include"vector.h"
#include"memory_manager.h"

COMPILE_TIME_ASSERT(sizeof(unsigned) == 4);
#define BV_DEFAULT_CAPACITY 2

class bit_vector {
protected:
    unsigned    m_num_bits; 
    unsigned    m_capacity; //!< in words
    unsigned *  m_data;

    static unsigned get_pos_mask(unsigned bit_idx) {
        return 1 << (bit_idx % 32);
    }
    
    static unsigned num_words(unsigned num_bits) { 
        // return (num_bits % 32) == 0 ? (num_bits / 32) : ((num_bits / 32) + 1);
        return (num_bits + 31) / 32;
    }

    void expand_to(unsigned new_capacity);

    void expand() {
        expand_to(m_capacity == 0 ? BV_DEFAULT_CAPACITY : ((m_capacity * 3 + 1) >> 1));
    }

    unsigned get_bit_word(unsigned bit_idx) const {
        SASSERT(bit_idx < size());
        return m_data[bit_idx / 32];
    }

    unsigned & get_bit_word(unsigned bit_idx) {
        SASSERT(bit_idx < size());
        return m_data[bit_idx / 32];
    }

public:
    bit_vector():
        m_num_bits(0),
        m_capacity(0),
        m_data(0) {
    }

    bit_vector(unsigned reserve_num_bits) :
        m_num_bits(0),
        m_capacity(num_words(reserve_num_bits)),
        m_data(alloc_svect(unsigned, m_capacity)) {
        memset(m_data, 0, m_capacity * sizeof(unsigned));
    }

    bit_vector(bit_vector const & source):
        m_num_bits(source.m_num_bits),
        m_capacity(source.m_capacity),
        m_data(alloc_svect(unsigned, source.m_capacity)) {
        memcpy(m_data, source.m_data, source.m_capacity * sizeof(unsigned));
    }
    
    bit_vector(unsigned const * source, int num_bits):
        m_num_bits(num_bits),
        m_capacity(num_words(num_bits)),
        m_data(alloc_svect(unsigned, m_capacity)) {
        memcpy(m_data, source, m_capacity * sizeof(unsigned));
    }

    ~bit_vector() {
        dealloc_svect(m_data);
    }
    
    void reset() {
        memset(m_data, 0, m_capacity * sizeof(unsigned));
        m_num_bits = 0;
    }

    void swap(bit_vector & other) {
        std::swap(m_data, other.m_data);
        std::swap(m_num_bits, other.m_num_bits);
        std::swap(m_capacity, other.m_capacity);
    }

    // Increase the size of the bit_vector by k 0-bits.
    void shift_right(unsigned k);

    void fill0() {
        memset(m_data, 0, m_capacity * sizeof(unsigned));
    }

    unsigned size() const { 
        return m_num_bits; 
    }

    bool empty() const {
        return m_num_bits == 0;
    }

    unsigned num_words() const { 
        return num_words(m_num_bits); 
    }

    unsigned get_word(unsigned word_idx) const {
        return m_data[word_idx];
    }

    unsigned get_hash() const;
    
    bool get(unsigned bit_idx) const {
        SASSERT(bit_idx < size());
        bool r = (get_bit_word(bit_idx) & get_pos_mask(bit_idx)) != 0;
        return r;
    }

    void set(unsigned bit_idx) {
        SASSERT(bit_idx < size());
        get_bit_word(bit_idx) |= get_pos_mask(bit_idx);
    }

    void unset(unsigned bit_idx) {
        SASSERT(bit_idx < size());
        get_bit_word(bit_idx) &= ~get_pos_mask(bit_idx);
    }
    
    void set(unsigned bit_idx, bool val) {
        SASSERT(bit_idx < size());
        int _val = static_cast<int>(val);
        get_bit_word(bit_idx) ^= (-_val ^ get_bit_word(bit_idx)) & get_pos_mask(bit_idx);
    }

    void push_back(bool val) {
        unsigned idx = m_num_bits;
        m_num_bits++;
        if (num_words(m_num_bits) > m_capacity) {
            expand();
        }
        set(idx, val);
      }

    void pop_back() {
        SASSERT(m_num_bits > 0);
        m_num_bits--;
    }

    bool back() const {
        SASSERT(!empty());
        bool r = get(m_num_bits - 1);
        return r;
    }

    void shrink(unsigned new_size) {
        SASSERT(new_size <= m_num_bits);
        m_num_bits = new_size;
    }

    void resize(unsigned new_size, bool val = false);

    void reserve(unsigned sz, bool val = false) {
        if (sz > size()) 
            resize(sz, val);
    }

    bool operator==(bit_vector const & other) const;

    bool operator!=(bit_vector const & other) const { return !operator==(other); }

    bit_vector & operator=(bit_vector const & source) {
        m_num_bits = source.m_num_bits;
        if (m_capacity < source.m_capacity) {
            dealloc_svect(m_data);
            m_data     = alloc_svect(unsigned, source.m_capacity);
            m_capacity = source.m_capacity;
        }
        memcpy(m_data, source.m_data, source.m_capacity * sizeof(unsigned));
        return *this;
    }

    bit_vector & operator|=(bit_vector const & source);

    bit_vector & operator&=(bit_vector const & source);

    bit_vector & neg();
    
    void display(std::ostream & out) const;

    bool contains(const bit_vector & other) const;

};

inline std::ostream & operator<<(std::ostream & out, bit_vector const & b) {
    b.display(out);
    return out;
}

/**
   \brief Bitvector class with fast reset.
   This class should be used if the reset is frequently called.
*/
class fr_bit_vector : private bit_vector {
    unsigned_vector m_one_idxs;
public:
    void reset();

    void fill0() {
        bit_vector::fill0();
        m_one_idxs.reset();
    }

    void set(unsigned idx) {
        m_one_idxs.push_back(idx);
        bit_vector::set(idx);
    }

    void set(unsigned idx, bool val) {
        if (val)
            m_one_idxs.push_back(idx);
        bit_vector::set(idx, val);
    }
    
    void push_back(bool val) {
        if (val)
            m_one_idxs.push_back(size());
        bit_vector::push_back(val);
    }
};

#endif /* _BIT_VECTOR_H_ */

