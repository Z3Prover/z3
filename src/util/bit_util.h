/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    bit_util.h

Abstract:

    Bit hacking utilities.

Author:

    Leonardo de Moura (leonardo) 2012-09-11.

Revision History:

--*/
#pragma once

#include <span>

/**
   \brief Return the position of the most significant (set) bit of a
   nonzero unsigned integer.
*/
unsigned msb_pos(unsigned v);

/**
   \brief Return the number of leading zeros bits in a nonzero unsigned integer.
*/
unsigned nlz_core(unsigned x);

/**
   \brief Return the number of leading zero bits in data (a number of sz words).
*/
unsigned nlz(std::span<unsigned const> data);

// Backward compatibility overload
inline unsigned nlz(unsigned sz, unsigned const * data) {
    return nlz(std::span<unsigned const>(data, sz));
}

/**
   \brief Return the number of trailing zeros in a nonzero unsigned number.
*/
unsigned ntz_core(unsigned x);

/**
   \brief Return the number of trailing zero bits in data (a number of sz words).
*/
unsigned ntz(std::span<unsigned const> data);

// Backward compatibility overload
inline unsigned ntz(unsigned sz, unsigned const * data) {
    return ntz(std::span<unsigned const>(data, sz));
}

/**
   \brief dst <- src
   
   Truncate if src.size() > dst.size().
   Fill range [src.size(), dst.size()) of dst with zeros if dst.size() > src.size().
*/
void copy(std::span<unsigned const> src, std::span<unsigned> dst);

// Backward compatibility overload
inline void copy(unsigned src_sz, unsigned const * src, unsigned dst_sz, unsigned * dst) {
    copy(std::span<unsigned const>(src, src_sz), std::span<unsigned>(dst, dst_sz));
}

/**
   \brief Return true if all words of data are zero.
*/
bool is_zero(std::span<unsigned const> data);

// Backward compatibility overload
inline bool is_zero(unsigned sz, unsigned const * data) {
    return is_zero(std::span<unsigned const>(data, sz));
}

/**
   \brief Set all words of data to zero.
*/
void reset(std::span<unsigned> data);

// Backward compatibility overload
inline void reset(unsigned sz, unsigned * data) {
    reset(std::span<unsigned>(data, sz));
}

/**
   \brief dst <- src << k
   Store in dst the result of shifting src k bits to the left.
   The result is truncated by dst.size().

   \pre !src.empty()
   \pre !dst.empty()
*/
void shl(std::span<unsigned const> src, unsigned k, std::span<unsigned> dst);

// Backward compatibility overload
inline void shl(unsigned src_sz, unsigned const * src, unsigned k, unsigned dst_sz, unsigned * dst) {
    shl(std::span<unsigned const>(src, src_sz), k, std::span<unsigned>(dst, dst_sz));
}

/**
   \brief dst <- src >> k
   Store in dst the result of shifting src k bits to the right.

   \pre dst.size() == src.size() or both sizes can differ (handled generically)
   \pre !src.empty()
   \pre !dst.empty()
*/
void shr(std::span<unsigned const> src, unsigned k, std::span<unsigned> dst);

// Backward compatibility overloads
inline void shr(unsigned sz, unsigned const * src, unsigned k, unsigned * dst) {
    shr(std::span<unsigned const>(src, sz), k, std::span<unsigned>(dst, sz));
}

inline void shr(unsigned src_sz, unsigned const * src, unsigned k, unsigned dst_sz, unsigned * dst) {
    shr(std::span<unsigned const>(src, src_sz), k, std::span<unsigned>(dst, dst_sz));
}



/**
   \brief Return true if one of the first k bits of src is not zero.
*/
bool has_one_at_first_k_bits(std::span<unsigned const> data, unsigned k);

// Backward compatibility overload
inline bool has_one_at_first_k_bits(unsigned sz, unsigned const * data, unsigned k) {
    return has_one_at_first_k_bits(std::span<unsigned const>(data, sz), k);
}


/**
   \brief data <- data + 1
   
   Return true if no overflow occurred.
*/
bool inc(std::span<unsigned> data);

// Backward compatibility overload
inline bool inc(unsigned sz, unsigned * data) {
    return inc(std::span<unsigned>(data, sz));
}

/**
   \brief data <- data - 1
   
   Return true if no underflow occurred.
*/
bool dec(std::span<unsigned> data);

// Backward compatibility overload
inline bool dec(unsigned sz, unsigned * data) {
    return dec(std::span<unsigned>(data, sz));
}

/**
   \brief Return true if data1 < data2. 

   Both must have the same size.
*/
bool lt(std::span<unsigned> data1, std::span<unsigned> data2);

// Backward compatibility overload
inline bool lt(unsigned sz, unsigned * data1, unsigned * data2) {
    return lt(std::span<unsigned>(data1, sz), std::span<unsigned>(data2, sz));
}


/**
   \brief Store in c the a+b. This procedure assumes that a,b,c are vectors of the same size.
   Return false if a+b overflows.
*/
bool add(std::span<unsigned const> a, std::span<unsigned const> b, std::span<unsigned> c);

// Backward compatibility overload
inline bool add(unsigned sz, unsigned const * a, unsigned const * b, unsigned * c) {
    return add(std::span<unsigned const>(a, sz), std::span<unsigned const>(b, sz), std::span<unsigned>(c, sz));
}

