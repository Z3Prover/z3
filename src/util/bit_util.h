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
#ifndef _BIT_UTIL_H_
#define _BIT_UTIL_H_

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
unsigned nlz(unsigned sz, unsigned const * data);

/**
   \brief Return the number of trailing zeros in a nonzero unsigned number.
*/
unsigned ntz_core(unsigned x);

/**
   \brief Return the number of trailing zero bits in data (a number of sz words).
*/
unsigned ntz(unsigned sz, unsigned const * data);

/**
   \brief dst <- src
   
   Trucate if src_sz > dst_sz.
   Fill range [src_sz, dst_sz) of dst with zeros if dst_sz > src_sz.
*/
void copy(unsigned src_sz, unsigned const * src, unsigned dst_sz, unsigned * dst);

/**
   \brief Return true if all words of data are zero.
*/
bool is_zero(unsigned sz, unsigned const * data);

/**
   \brief Set all words of data to zero.
*/
void reset(unsigned sz, unsigned * data);

/**
   \brief dst <- src << k
   Store in dst the result of shifting src k bits to the left.
   The result is truncated by dst_sz.

   \pre src_sz != 0
   \pre dst_sz != 0
*/
void shl(unsigned src_sz, unsigned const * src, unsigned k, unsigned dst_sz, unsigned * dst);

/**
   \brief dst <- src >> k
   Store in dst the result of shifting src k bits to the right.

   \pre dst must have size sz.
   \pre src_sz != 0
   \pre dst_sz != 0
*/
void shr(unsigned sz, unsigned const * src, unsigned k, unsigned * dst);

/**
   \brief dst <- src >> k
   Store in dst the result of shifting src k bits to the right.

   Trucate if src_sz > dst_sz.
   Fill range [src_sz, dst_sz) of dst with zeros if dst_sz > src_sz.

   \pre src_sz != 0
   \pre dst_sz != 0
*/
void shr(unsigned src_sz, unsigned const * src, unsigned k, unsigned dst_sz, unsigned * dst);

/**
   \brief Return true if one of the first k bits of src is not zero.
*/
bool has_one_at_first_k_bits(unsigned sz, unsigned const * data, unsigned k);


/**
   \brief data <- data + 1
   
   Return true if no overflow occurred.
*/
bool inc(unsigned sz, unsigned * data);

/**
   \brief data <- data - 1
   
   Return true if no underflow occurred.
*/
bool dec(unsigned sz, unsigned * data);

/**
   \brief Return true if data1 < data2. 

   Both must have the same size.
*/
bool lt(unsigned sz, unsigned * data1, unsigned * data2);


/**
   \brief Store in c the a+b. This procedure assumes that a,b,c are vectors of size sz.
   Return false if a+b overflows.
*/
bool add(unsigned sz, unsigned const * a, unsigned const * b, unsigned * c);

#endif
