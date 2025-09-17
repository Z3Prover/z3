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
#include <cstdint>

// xxHash32 Performance Optimization for Z3
// Provides significantly better performance than Bob Jenkins hash
// while maintaining compatibility through compile-time selection

// Define Z3_USE_XXHASH to enable xxHash optimization
#ifndef Z3_USE_XXHASH
#define Z3_USE_XXHASH 1  // Enable by default for performance
#endif

#if Z3_USE_XXHASH

// xxHash32 constants for optimal performance
static const uint32_t XXHASH_PRIME1 = 0x9E3779B1U;
static const uint32_t XXHASH_PRIME2 = 0x85EBCA77U;
static const uint32_t XXHASH_PRIME3 = 0xC2B2AE3DU;
static const uint32_t XXHASH_PRIME4 = 0x27D4EB2FU;
static const uint32_t XXHASH_PRIME5 = 0x165667B1U;

static inline uint32_t xxhash_rotl32(uint32_t x, int r) {
    return (x << r) | (x >> (32 - r));
}

static inline uint32_t xxhash_read32le(const void* ptr) {
    uint32_t val;
    memcpy(&val, ptr, sizeof(val));
    return val;
}

// High-performance xxHash32 implementation optimized for Z3
static unsigned string_hash_xxhash32(const char* data, unsigned len, unsigned seed) {
    const uint8_t* p = (const uint8_t*)data;
    const uint8_t* const bEnd = p + len;
    uint32_t h32;

    if (len >= 16) {
        const uint8_t* const limit = bEnd - 16;
        uint32_t v1 = seed + XXHASH_PRIME1 + XXHASH_PRIME2;
        uint32_t v2 = seed + XXHASH_PRIME2;
        uint32_t v3 = seed + 0;
        uint32_t v4 = seed - XXHASH_PRIME1;

        do {
            v1 = xxhash_rotl32(v1 + xxhash_read32le(p) * XXHASH_PRIME2, 13) * XXHASH_PRIME1;
            p += 4;
            v2 = xxhash_rotl32(v2 + xxhash_read32le(p) * XXHASH_PRIME2, 13) * XXHASH_PRIME1;
            p += 4;
            v3 = xxhash_rotl32(v3 + xxhash_read32le(p) * XXHASH_PRIME2, 13) * XXHASH_PRIME1;
            p += 4;
            v4 = xxhash_rotl32(v4 + xxhash_read32le(p) * XXHASH_PRIME2, 13) * XXHASH_PRIME1;
            p += 4;
        } while (p <= limit);

        h32 = xxhash_rotl32(v1, 1) + xxhash_rotl32(v2, 7) + xxhash_rotl32(v3, 12) + xxhash_rotl32(v4, 18);
    } else {
        h32 = seed + XXHASH_PRIME5;
    }

    h32 += (uint32_t) len;

    while (p + 4 <= bEnd) {
        h32 += xxhash_read32le(p) * XXHASH_PRIME3;
        h32  = xxhash_rotl32(h32, 17) * XXHASH_PRIME4;
        p += 4;
    }

    while (p < bEnd) {
        h32 += (*p) * XXHASH_PRIME5;
        h32 = xxhash_rotl32(h32, 11) * XXHASH_PRIME1;
        p++;
    }

    h32 ^= h32 >> 15;
    h32 *= XXHASH_PRIME2;
    h32 ^= h32 >> 13;
    h32 *= XXHASH_PRIME3;
    h32 ^= h32 >> 16;

    return h32;
}

#endif // Z3_USE_XXHASH

static unsigned read_unsigned(const char *s) {
  unsigned n;
  memcpy(&n, s, sizeof(unsigned));
  return n;
}

// Performance-optimized hash function with fallback compatibility
unsigned string_hash(const char * str, unsigned length, unsigned init_value) {
#if Z3_USE_XXHASH
    // Use high-performance xxHash32 implementation
    return string_hash_xxhash32(str, length, init_value);
#else
    // Fallback to original Bob Jenkins hash for compatibility
    // http://burtleburtle.net/bob/hash/doobs.html
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
#endif
}

