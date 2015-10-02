/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    fixed_bit_vector.h

Abstract:

    Simple bitvector implementation for fixed size bit-vectors.

Author:

    Nikolaj Bjorner (nbjorner) 2014-9-15.

Revision History:

    Related to bit_vector, but is based on a manager.

--*/
#ifndef FIXED_BIT_VECTOR_H_
#define FIXED_BIT_VECTOR_H_

#include<string.h>
#include"debug.h"
#include"small_object_allocator.h"

class fixed_bit_vector {
    friend class fixed_bit_vector_manager;
    friend class tbv_manager;
    unsigned    m_data[1];

    static unsigned get_pos_mask(unsigned bit_idx) {
        return 1 << (bit_idx % 32);
    }


    unsigned get_bit_word(unsigned bit_idx) const {
        return m_data[bit_idx / 32];
    }

    unsigned & get_bit_word(unsigned bit_idx) {
        return m_data[bit_idx / 32];
    }

public:

    fixed_bit_vector() {}
    
    ~fixed_bit_vector() {}
    
    unsigned get_word(unsigned word_idx) const { return m_data[word_idx]; }

    bool operator[](unsigned bit_idx) const {
        return get(bit_idx);
    }
    
    bool get(unsigned bit_idx) const {
        return (get_bit_word(bit_idx) & get_pos_mask(bit_idx)) != 0;
    }
    
private:
    void set(unsigned bit_idx) {
        get_bit_word(bit_idx) |= get_pos_mask(bit_idx);
    }

    void unset(unsigned bit_idx) {
        get_bit_word(bit_idx) &= ~get_pos_mask(bit_idx);
    }
    
    void set(unsigned bit_idx, bool val) {
        int _val = static_cast<int>(val);
        get_bit_word(bit_idx) ^= (-_val ^ get_bit_word(bit_idx)) & get_pos_mask(bit_idx);
    }

    // assign bits this[lo:hi] := other[0:hi-lo+1]
    void set(fixed_bit_vector const& other, unsigned hi, unsigned lo);

};

class fixed_bit_vector_manager {
    friend class fixed_bit_vector;
    small_object_allocator m_alloc;
    unsigned               m_num_bits;
    unsigned               m_num_bytes;
    unsigned               m_num_words;
    unsigned               m_mask;
    fixed_bit_vector       m_0;

    static unsigned num_words(unsigned num_bits) { 
        return (num_bits + 31) / 32;
    }    

public:
    fixed_bit_vector_manager(unsigned num_bits);

    void reset() { m_alloc.reset(); }
    fixed_bit_vector* allocate();
    fixed_bit_vector* allocate1();
    fixed_bit_vector* allocate0();
    fixed_bit_vector* allocate(fixed_bit_vector const& bv);
    void deallocate(fixed_bit_vector* bv);

    void copy(fixed_bit_vector& dst, fixed_bit_vector const& src) const;
    unsigned num_words() const { return m_num_words; }
    unsigned num_bytes() const { return m_num_bytes; }
    unsigned num_bits() const { return m_num_bits; }
    fixed_bit_vector& reset(fixed_bit_vector& bv) const { return fill0(bv); }
    fixed_bit_vector& fill0(fixed_bit_vector& bv) const;
    fixed_bit_vector& fill1(fixed_bit_vector& bv) const;
    fixed_bit_vector& set_and(fixed_bit_vector& dst, fixed_bit_vector const& src) const;
    fixed_bit_vector& set_or(fixed_bit_vector& dst,  fixed_bit_vector const& src) const;
    fixed_bit_vector& set_neg(fixed_bit_vector& dst) const;
    unsigned last_word(fixed_bit_vector const& bv) const;
    unsigned get_mask() const { return m_mask; }
    bool equals(fixed_bit_vector const& a, fixed_bit_vector const& b) const;
    unsigned hash(fixed_bit_vector const& src) const;
    bool contains(fixed_bit_vector const& a, fixed_bit_vector const& b) const;
    std::ostream& display(std::ostream& out, fixed_bit_vector const& b) const;    
    void set(fixed_bit_vector& dst, unsigned bit_idx) {
        SASSERT(bit_idx < num_bits());
        dst.set(bit_idx);
    }
    void unset(fixed_bit_vector& dst, unsigned bit_idx) {
        SASSERT(bit_idx < num_bits());
        dst.unset(bit_idx);
    }
    
    void set(fixed_bit_vector& dst, unsigned bit_idx, bool val) {
        SASSERT(bit_idx < num_bits());
        dst.set(bit_idx, val);
    }

    // assign bits this[lo:hi] := other[0:hi-lo+1]
    void set(fixed_bit_vector& dst, fixed_bit_vector const& other, unsigned hi, unsigned lo) {
        SASSERT(lo <= hi && hi < num_bits());
        dst.set(other, hi, lo);
    }

};




#endif /* FIXED_BIT_VECTOR_H_ */

