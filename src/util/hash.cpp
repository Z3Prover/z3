/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    hash.cpp

Abstract:

    Basic hash computation support.

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

--*/

#include "util/debug.h"
#include "util/hash.h"
#include <string.h>

static unsigned read_unsigned(const char *s) {
  unsigned n;
  memcpy(&n, s, sizeof(unsigned));
  return n;
}

// I'm using Bob Jenkin's hash function.
// http://burtleburtle.net/bob/hash/doobs.html
unsigned string_hash(const char * str, unsigned length, unsigned init_value) {
    unsigned a, b, c, len;

    /* Set up the internal state */
    len = length;
    a = b = 0x9e3779b9;  /* the golden ratio; an arbitrary value */
    c = init_value;      /* the previous hash value */

    /*---------------------------------------- handle most of the key */
    SASSERT(sizeof(unsigned) == 4);
    while (len >= 12) {
        a += read_unsigned(str);
        b += read_unsigned(str+4);
        c += read_unsigned(str+8);
        mix(a,b,c);
        str += 12; len -= 12;
    }

    /*------------------------------------- handle the last 11 bytes */
    c += length;
    switch(len) {        /* all the case statements fall through */
    case 11: 
        c+=((unsigned)str[10]<<24);
        Z3_fallthrough;
    case 10: 
        c+=((unsigned)str[9]<<16);
        Z3_fallthrough;
    case 9 : 
        c+=((unsigned)str[8]<<8);
        Z3_fallthrough;
        /* the first byte of c is reserved for the length */
    case 8 : 
        b+=((unsigned)str[7]<<24);
        Z3_fallthrough;
    case 7 : 
        b+=((unsigned)str[6]<<16);
        Z3_fallthrough;
    case 6 : 
        b+=((unsigned)str[5]<<8);
        Z3_fallthrough;
    case 5 : 
        b+=str[4];
        Z3_fallthrough;
    case 4 : 
        a+=((unsigned)str[3]<<24);
        Z3_fallthrough;
    case 3 : 
        a+=((unsigned)str[2]<<16);
        Z3_fallthrough;
    case 2 : 
        a+=((unsigned)str[1]<<8);
        Z3_fallthrough;
    case 1 : 
        a+=str[0];
        /* case 0: nothing left to add */
        break;
    }
    mix(a,b,c);
    /*-------------------------------------------- report the result */
    return c;
}

#ifdef Z3_ENABLE_FAST_HASH
// xxHash32-inspired fast string hash implementation
namespace z3_fast_hash {

// Optimized string hash using xxHash32-like algorithm
unsigned fast_string_hash(const char* data, unsigned len, uint32_t seed) {
    // xxHash32 constants
    static constexpr uint32_t PRIME32_1 = 0x9E3779B1U;
    static constexpr uint32_t PRIME32_2 = 0x85EBCA77U;
    static constexpr uint32_t PRIME32_3 = 0xC2B2AE3DU;
    static constexpr uint32_t PRIME32_4 = 0x27D4EB2FU;
    static constexpr uint32_t PRIME32_5 = 0x165667B1U;

    const uint8_t* p = reinterpret_cast<const uint8_t*>(data);
    const uint8_t* const bEnd = p + len;
    uint32_t h32;

    if (len >= 16) {
        const uint8_t* const limit = bEnd - 16;
        uint32_t v1 = seed + PRIME32_1 + PRIME32_2;
        uint32_t v2 = seed + PRIME32_2;
        uint32_t v3 = seed + 0;
        uint32_t v4 = seed - PRIME32_1;

        do {
            // Process 4x 4-byte chunks (16 bytes per iteration)
            v1 = ((v1 + (*(uint32_t*)p) * PRIME32_2) << 13 | (v1 + (*(uint32_t*)p) * PRIME32_2) >> 19) * PRIME32_1;
            p += 4;
            v2 = ((v2 + (*(uint32_t*)p) * PRIME32_2) << 13 | (v2 + (*(uint32_t*)p) * PRIME32_2) >> 19) * PRIME32_1;
            p += 4;
            v3 = ((v3 + (*(uint32_t*)p) * PRIME32_2) << 13 | (v3 + (*(uint32_t*)p) * PRIME32_2) >> 19) * PRIME32_1;
            p += 4;
            v4 = ((v4 + (*(uint32_t*)p) * PRIME32_2) << 13 | (v4 + (*(uint32_t*)p) * PRIME32_2) >> 19) * PRIME32_1;
            p += 4;
        } while (p <= limit);

        h32 = ((v1 << 1) | (v1 >> 31)) + ((v2 << 7) | (v2 >> 25)) +
              ((v3 << 12) | (v3 >> 20)) + ((v4 << 18) | (v4 >> 14));
    } else {
        h32 = seed + PRIME32_5;
    }

    h32 += (uint32_t)len;

    // Process remaining bytes (0-15 bytes)
    while (p + 4 <= bEnd) {
        h32 += (*(uint32_t*)p) * PRIME32_3;
        h32 = ((h32 << 17) | (h32 >> 15)) * PRIME32_4;
        p += 4;
    }

    while (p < bEnd) {
        h32 += (*p) * PRIME32_5;
        h32 = ((h32 << 11) | (h32 >> 21)) * PRIME32_1;
        p++;
    }

    // Final avalanche mixing
    h32 ^= h32 >> 15;
    h32 *= PRIME32_2;
    h32 ^= h32 >> 13;
    h32 *= PRIME32_3;
    h32 ^= h32 >> 16;

    return h32;
}

} // namespace z3_fast_hash
#endif // Z3_ENABLE_FAST_HASH

