/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    bit_util.cpp

Abstract:

    Bit hacking utilities.

Author:

    Leonardo de Moura (leonardo) 2012-09-11.

Revision History:

--*/
#include"bit_util.h"
#include"util.h"
#include"debug.h"
#include <cstring>

/**
   \brief (Debugging version) Return the position of the most significant (set) bit of a
   nonzero unsigned integer.
*/
#ifdef Z3DEBUG
unsigned slow_msb_pos(unsigned v) {
    SASSERT(v != 0);
    unsigned r = 0;
    while (v != 1) {
        v = v >> 1;
        r++;
    }
    return r;
}
#endif

/**
   \brief Return the position of the most significant (set) bit of a
   nonzero unsigned integer.
*/
unsigned msb_pos(unsigned v) {
    SASSERT(v != 0);
#ifdef Z3DEBUG
    unsigned expected = slow_msb_pos(v);
#endif
    unsigned r, shift;
    r = (v > 0xFFFF) << 4; 
    v >>= r;
    shift = (v > 0xFF) << 3; 
    v >>= shift; 
    r |= shift;
    shift = (v > 0xF) << 2; 
    v >>= shift; 
    r |= shift;
    shift = (v > 0x3) << 1; 
    v >>= shift; 
    r |= shift;
    r |= (v >> 1);
    SASSERT(r == expected);
    return r;
}

/**
   \brief Return the number of leading zeros bits in a nonzero unsigned integer.
*/
unsigned nlz_core(unsigned x) {
    SASSERT(x != 0);
#ifdef __GNUC__
    return __builtin_clz(x);
#else
    return 31 - msb_pos(x);
#endif
}

/**
   \brief Return the number of leading zero bits in data (a number of sz words).
*/
unsigned nlz(unsigned sz, unsigned const * data) {
    unsigned r = 0;
    unsigned i = sz;
    while (i > 0) {
        --i;
        unsigned d = data[i];
        if (d == 0)
            r += 32;
        else
            return r + nlz_core(d);
    }
    return r;
}

/**
   \brief Return the number of trailing zeros in a nonzero unsigned number.
*/
unsigned ntz_core(unsigned x) {
    SASSERT(x != 0);
#ifdef __GNUC__
    return __builtin_ctz(x);
#else
    float f = static_cast<float>(x & static_cast<unsigned>(-static_cast<int>(x)));
    unsigned u;
    SASSERT(sizeof(u) == sizeof(f));
    memcpy(&u, &f, sizeof(u));
    return (u >> 23) - 0x7f;
#endif
}

/**
   \brief Return the number of trailing zero bits in data (a number of sz words).
*/
unsigned ntz(unsigned sz, unsigned const * data) {
    unsigned r = 0;
    for (unsigned i = 0; i < sz; i++) {
        unsigned d = data[i];
        if (d == 0)
            r += 32;
        else
            return r + ntz_core(d);
    }
    return r;
}

/**
   \brief dst <- src
   
   Trucate if src_sz > dst_sz.
   Fill range [src_sz, dst_sz) of dst with zeros if dst_sz > src_sz.
*/
void copy(unsigned src_sz, unsigned const * src, 
          unsigned dst_sz, unsigned * dst) {
    if (dst_sz >= src_sz) {
        unsigned i;
        for (i = 0; i < src_sz; i++) 
            dst[i] = src[i];
        for (; i < dst_sz; i++) 
            dst[i] = 0;
    }
    else {
        SASSERT(dst_sz < src_sz);
        for (unsigned i = 0; i < dst_sz; i++)
            dst[i] = src[i];
    }
}

/**
   \brief Return true if all words of data are zero.
*/
bool is_zero(unsigned sz, unsigned const * data) {
    for (unsigned i = 0; i < sz; i++) 
        if (data[i])
            return false;
    return true;
}

/**
   \brief Set all words of data to zero.
*/
void reset(unsigned sz, unsigned * data) {
    for (unsigned i = 0; i < sz; i++)
        data[i] = 0;
}

/**
   \brief dst <- src << k
   Store in dst the result of shifting src k bits to the left.
   The result is truncated by dst_sz.

   \pre src_sz != 0
   \pre dst_sz != 0
*/
void shl(unsigned src_sz, unsigned const * src, unsigned k, 
         unsigned dst_sz, unsigned * dst) {
    SASSERT(src_sz != 0);
    SASSERT(dst_sz != 0);
    SASSERT(k != 0);
    unsigned word_shift  = k / (8 * sizeof(unsigned));
    unsigned bit_shift   = k % (8 * sizeof(unsigned));
    if (word_shift > 0) {
        unsigned j = src_sz;
        unsigned i = src_sz + word_shift;
        if (i > dst_sz) {
            if (j >= i - dst_sz)
                j -= (i - dst_sz); 
            else
                j = 0;
            i  = dst_sz;
        }
        else if (i < dst_sz) {
            for (unsigned r = i; r < dst_sz; r++)
                dst[r] = 0;
        }
        while (j > 0) {
            --j; --i;
            dst[i] = src[j];
        }
        while (i > 0) {
            --i;
            dst[i] = 0;
        }
        if (bit_shift > 0) {
            unsigned comp_shift = (8 * sizeof(unsigned)) - bit_shift;
            unsigned prev       = 0;
            for (unsigned i = word_shift; i < dst_sz; i++) {
                unsigned new_prev = (dst[i] >> comp_shift);
                dst[i] <<= bit_shift;
                dst[i] |= prev;
                prev = new_prev;
            }
        }
    }
    else {
        unsigned comp_shift = (8 * sizeof(unsigned)) - bit_shift;
        unsigned prev       = 0;
        if (src_sz > dst_sz)
            src_sz = dst_sz;
        for (unsigned i = 0; i < src_sz; i++) {
            unsigned new_prev = (src[i] >> comp_shift);
            dst[i] = src[i];
            dst[i] <<= bit_shift;
            dst[i] |= prev;
            prev = new_prev;
        }
        if (dst_sz > src_sz) {
            dst[src_sz] = prev;
            for (unsigned i = src_sz+1; i < dst_sz; i++)
                dst[i] = 0;
        }
    }
}

/**
   \brief dst <- src >> k
   Store in dst the result of shifting src k bits to the right.

   \pre dst must have size sz.
   \pre src_sz != 0
   \pre dst_sz != 0
*/
void shr(unsigned sz, unsigned const * src, unsigned k, unsigned * dst) {
    unsigned digit_shift = k / (8 * sizeof(unsigned));
    if (digit_shift >= sz) {
        reset(sz, dst);
        return;
    }
    unsigned bit_shift   = k % (8 * sizeof(unsigned));
    unsigned comp_shift  = (8 * sizeof(unsigned)) - bit_shift;
    unsigned new_sz      = sz - digit_shift;
    if (new_sz < sz) {
        unsigned i       = 0;
        unsigned j       = digit_shift;
        if (bit_shift != 0) {
            for (; i < new_sz - 1; i++, j++) {
                dst[i] = src[j];
                dst[i] >>= bit_shift;
                dst[i] |= (src[j+1] << comp_shift);
            }
            dst[i] = src[j];
            dst[i] >>= bit_shift;
        }
        else {
            for (; i < new_sz; i++, j++) {
                dst[i] = src[j];
            }
        }
        for (unsigned i = new_sz; i < sz; i++)
            dst[i] = 0;
    }
    else {
        SASSERT(new_sz == sz);
        SASSERT(bit_shift != 0);
        unsigned i       = 0;
        for (; i < new_sz - 1; i++) {
            dst[i] = src[i];
            dst[i] >>= bit_shift;
            dst[i] |= (src[i+1] << comp_shift);
        }
        dst[i] = src[i];
        dst[i] >>= bit_shift;
    }
}

void shr(unsigned src_sz, unsigned const * src, unsigned k, unsigned dst_sz, unsigned * dst) {
    unsigned digit_shift = k / (8 * sizeof(unsigned));
    if (digit_shift >= src_sz) {
        reset(dst_sz, dst);
        return;
    }
    unsigned bit_shift   = k % (8 * sizeof(unsigned));
    unsigned comp_shift  = (8 * sizeof(unsigned)) - bit_shift;
    unsigned new_sz      = src_sz - digit_shift;
    if (digit_shift > 0) {
        unsigned i       = 0;
        unsigned j       = digit_shift;
        if (bit_shift != 0) {
            unsigned sz = new_sz;
            if (new_sz > dst_sz)
                sz = dst_sz;
            for (; i < sz - 1; i++, j++) {
                dst[i] = src[j];
                dst[i] >>= bit_shift;
                dst[i] |= (src[j+1] << comp_shift);
            }
            dst[i] = src[j];
            dst[i] >>= bit_shift;
            if (new_sz > dst_sz)
                dst[i] |= (src[j+1] << comp_shift);
        }
        else {
            if (new_sz > dst_sz)
                new_sz = dst_sz;
            for (; i < new_sz; i++, j++) {
                dst[i] = src[j];
            }
        }
    }
    else {
        SASSERT(new_sz == src_sz);
        SASSERT(bit_shift != 0);
        unsigned sz = new_sz;
        if (new_sz > dst_sz)
            sz = dst_sz;
        unsigned i       = 0;
        for (; i < sz - 1; i++) {
            dst[i] = src[i];
            dst[i] >>= bit_shift;
            dst[i] |= (src[i+1] << comp_shift);
        }
        dst[i] = src[i];
        dst[i] >>= bit_shift;
        if (new_sz > dst_sz)
            dst[i] |= (src[i+1] << comp_shift);
    }
    for (unsigned i = new_sz; i < dst_sz; i++)
        dst[i] = 0;
}

/**
   \brief Return true if one of the first k bits of src is not zero.
*/
bool has_one_at_first_k_bits(unsigned sz, unsigned const * data, unsigned k) {
    SASSERT(sz != 0);
    unsigned word_sz = k / (8 * sizeof(unsigned));
    if (word_sz > sz)
        word_sz = sz;
    for (unsigned i = 0; i < word_sz; i++) {
        if (data[i] != 0)
            return true;
    }
    if (word_sz < sz) {
        unsigned bit_sz  = k % (8 * sizeof(unsigned));
        unsigned mask    = (1u << bit_sz) - 1;
        return (data[word_sz] & mask) != 0;
    }
    return false;
}

bool inc(unsigned sz, unsigned * data) {
    for (unsigned i = 0; i < sz; i++) {
        data[i]++;
        if (data[i] != 0)
            return true; // no overflow
    }
    return false; // overflow
}

bool dec(unsigned sz, unsigned * data) {
    for (unsigned i = 0; i < sz; i++) {
        data[i]--;
        if (data[i] != UINT_MAX)
            return true; // no underflow
    }
    return false; // underflow
}

bool lt(unsigned sz, unsigned * data1, unsigned * data2) {
    unsigned i = sz;
    while (i > 0) {
        --i;
        if (data1[i] < data2[i])
            return true;
        if (data1[i] > data2[i])
            return false;
    }
    return false;
}

bool add(unsigned sz, unsigned const * a, unsigned const * b, unsigned * c) {
    unsigned k = 0;
    for (unsigned j = 0; j < sz; j++) {
        unsigned r = a[j] + b[j]; 
        bool c1 = r < a[j];
        c[j] = r + k;    
        bool c2 = c[j] < r;
        k = c1 | c2;
    }
    return k == 0;
}

