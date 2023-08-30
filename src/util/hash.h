/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    hash.h

Abstract:

    Basic hash computation support.

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

--*/
#pragma once

#include <algorithm>
#include <cstring>
#include "util/util.h"

// halfsip(1,3) hash
// Inspired from https://github.com/veorq/SipHash/blob/master/halfsiphash.c
// In public domain

#define ROTL(x, b) (uint32_t)(((x) << (b)) | ((x) >> (32 - (b))))

#define U32TO8_LE(p, v)                                                        \
    (p)[0] = (uint8_t)((v));                                                   \
    (p)[1] = (uint8_t)((v) >> 8);                                              \
    (p)[2] = (uint8_t)((v) >> 16);                                             \
    (p)[3] = (uint8_t)((v) >> 24);

#define U8TO32_LE(p)                                                           \
    (((uint32_t)((p)[0])) | ((uint32_t)((p)[1]) << 8) |                        \
     ((uint32_t)((p)[2]) << 16) | ((uint32_t)((p)[3]) << 24))

class GenHash {
    uint32_t v0 = 0;
    uint32_t v1 = 0;
    uint32_t v2 = UINT32_C(0x6c796765);
    uint32_t v3 = UINT32_C(0x74656462);
    uint32_t total_length = 0;

    void sipround() {
        v0 += v1;
        v1 = ROTL(v1, 5);
        v1 ^= v0;
        v0 = ROTL(v0, 16);
        v2 += v3;
        v3 = ROTL(v3, 8);
        v3 ^= v2;
        v0 += v3;
        v3 = ROTL(v3, 7);
        v3 ^= v0;
        v2 += v1;
        v1 = ROTL(v1, 13);
        v1 ^= v2;
        v2 = ROTL(v2, 16);
    }

    void c_rounds() {
        sipround();
    }

    void d_rounds() {
        sipround();
        sipround();
        sipround();
    }


    void hash(const void *in, size_t inlen) {
        unsigned char *ni = (unsigned char *)in;
        const unsigned char *end = ni + inlen - (inlen % sizeof(uint32_t));

        total_length += inlen;

        for (; ni != end; ni += 4) {
            uint32_t m = U8TO32_LE(ni);
            v3 ^= m;
            c_rounds();
            v0 ^= m;
        }

        if (int left = inlen & 3) {
            uint32_t b = ((uint32_t)inlen) << 24;
            switch (left) {
            case 3:
                b |= ((uint32_t)ni[2]) << 16;
                Z3_fallthrough;
            case 2:
                b |= ((uint32_t)ni[1]) << 8;
                Z3_fallthrough;
            case 1:
                b |= ((uint32_t)ni[0]);
                break;
            }
            v3 ^= b;
            c_rounds();
            v0 ^= b;
        }
    }

public:
    void add(int v) {
        hash(&v, sizeof(v));
    }

    void add(unsigned v) {
        hash(&v, sizeof(v));
    }

    void add(uint64_t v) {
        hash(&v, sizeof(v));
    }

    void add(double v) {
        hash(&v, sizeof(v));
    }

    void add(const std::string &str) {
        hash(str.c_str(), str.size());
    }

    void add(const void *ptr, size_t sz) {
        hash(ptr, sz);
    }

    unsigned operator()() {
        uint32_t b = total_length << 24;
        v3 ^= b;
        c_rounds();
        v0 ^= b;

        v2 ^= 0xff;
        d_rounds();
        b = v1 ^ v3;

        uint8_t array[4];
        U32TO8_LE(array, b);
        unsigned out;
        std::memcpy(&out, array, sizeof(out));
        return out;
    }
};




#define mix(a,b,c)              \
{                               \
  a -= b; a -= c; a ^= (c>>13); \
  b -= c; b -= a; b ^= (a<<8);  \
  c -= a; c -= b; c ^= (b>>13); \
  a -= b; a -= c; a ^= (c>>12); \
  b -= c; b -= a; b ^= (a<<16); \
  c -= a; c -= b; c ^= (b>>5);  \
  a -= b; a -= c; a ^= (c>>3);  \
  b -= c; b -= a; b ^= (a<<10); \
  c -= a; c -= b; c ^= (b>>15); \
}

inline unsigned hash_u(unsigned a) {
   a = (a+0x7ed55d16) + (a<<12);
   a = (a^0xc761c23c) ^ (a>>19);
   a = (a+0x165667b1) + (a<<5);
   a = (a+0xd3a2646c) ^ (a<<9);
   a = (a+0xfd7046c5) + (a<<3);
   a = (a^0xb55a4f09) ^ (a>>16);
   return a;
}

inline unsigned hash_ull(unsigned long long a) {
  a  = (~a) + (a << 18); 
  a ^= (a >> 31);
  a += (a << 2) + (a << 4);
  a ^= (a >> 11);
  a += (a << 6);
  a ^= (a >> 22);
  return static_cast<unsigned>(a);
}

inline unsigned combine_hash(unsigned h1, unsigned h2) {
    h2 -= h1; h2 ^= (h1 << 8);
    h1 -= h2; h2 ^= (h1 << 16);
    h2 -= h1; h2 ^= (h1 << 10);
    return h2;
}

inline unsigned hash_u_u(unsigned a, unsigned b) {
    return combine_hash(hash_u(a), hash_u(b));
}

unsigned string_hash(const char * str, unsigned len, unsigned init_value);

inline unsigned unsigned_ptr_hash(unsigned const* vec, unsigned len, unsigned init_value) {
    return string_hash((char const*)(vec), len*4, init_value);
}

template<typename Composite, typename GetKindHashProc, typename GetChildHashProc>
unsigned get_composite_hash(Composite app, unsigned n, GetKindHashProc const & khasher = GetKindHashProc(), GetChildHashProc const & chasher = GetChildHashProc()) {
    unsigned a, b, c;
    unsigned kind_hash = khasher(app);

    a = b = 0x9e3779b9;
    c = 11;    

    switch (n) {
    case 0:
        return c;
    case 1:
        a += kind_hash;
        b  = chasher(app, 0);
        mix(a, b, c);
        return c;
    case 2:
        a += kind_hash;
        b += chasher(app, 0);
        c += chasher(app, 1);
        mix(a, b, c);
        return c;
    case 3:
        a += chasher(app, 0);
        b += chasher(app, 1);
        c += chasher(app, 2);
        mix(a, b, c);
        a += kind_hash;
        mix(a, b, c);
        return c;
    default:
        while (n >= 3) {
            n--;
            a += chasher(app, n);
            n--;
            b += chasher(app, n);
            n--;
            c += chasher(app, n);
            mix(a, b, c);
        }
        
        a += kind_hash;
        switch (n) {
        case 2:
            b += chasher(app, 1);
            Z3_fallthrough;
        case 1:
            c += chasher(app, 0);
        }
        mix(a, b, c);
        return c;
    }
}

template<typename Composite>
struct default_kind_hash_proc { unsigned operator()(Composite const & c) const { return 17; } };

struct int_hash {
    typedef int data_t;
    unsigned operator()(int x) const { return static_cast<unsigned>(x); }
};

struct unsigned_hash {
    typedef unsigned data_t;
    unsigned operator()(unsigned x) const { return x; }
};

struct size_t_hash {
    typedef size_t data_t;
    unsigned operator()(size_t x) const { return static_cast<unsigned>(x); }
};

struct uint64_hash {
    typedef uint64_t data_t;
    unsigned operator()(uint64_t x) const { return static_cast<unsigned>(x); }
};

struct bool_hash {
    typedef bool data_t;
    unsigned operator()(bool x) const { return static_cast<unsigned>(x); }
};

template<typename T>
struct obj_hash {
    typedef T data_t;
    unsigned operator()(const T & e) const { 
        return e.hash();
    }
};

template<typename T>
struct obj_ptr_hash {
    typedef T * data_t;
    unsigned operator()(T * a) const {
        return a->hash();
    }
};

template<typename T1, typename T2>
struct obj_ptr_pair_hash {
    typedef std::pair<T1*, T2*> data_t;
    unsigned operator()(data_t const & d) const {
        return combine_hash(d.first->hash(), d.second->hash());
    }
};

template<typename T1, typename T2, typename T3>
struct triple {
    T1 first;
    T2 second;
    T3 third;
    triple(): first(T1()), second(T2()), third(T3()) {}
    triple(T1 f, T2 s, T3 t): first(f), second(s), third(t) {}

    bool operator==(triple const& other) const {
        return 
            first == other.first &&
            second == other.second &&
            third == other.third;
    }
};

template<typename Hash1, typename Hash2, typename Hash3>
struct triple_hash : private Hash1 {
    Hash2 m_hash2;
    Hash3 m_hash3;
    typedef triple<typename Hash1::data_t, typename Hash2::data_t, typename Hash3::data> data_t;
    triple_hash(Hash1 const & h1 = Hash1(), Hash2 const & h2 = Hash2(), Hash3 const & h3 = Hash3()):
        Hash1(h1),
        m_hash2(h2),
        m_hash3(h3) {
    }

    unsigned operator()(std::pair<typename Hash1::data_t, typename Hash2::data_t> const & p) const {
        return combine_hash(combine_hash(Hash1::operator()(p.first), m_hash2.operator()(p.second)), m_hash3.operator()(p.third));
    }
};

template<typename T1, typename T2, typename T3>
struct obj_ptr_triple_hash {
    typedef triple<T1*, T2*, T3*> data_t;
    unsigned operator()(data_t const & d) const {
        return combine_hash(combine_hash(d.first->hash(), d.second->hash()), d.third->hash());
    }
};

template<typename Hash1, typename Hash2>
struct pair_hash : private Hash1 {
    Hash2 m_hash2;
    typedef std::pair<typename Hash1::data_t, typename Hash2::data_t> data_t;
    pair_hash(Hash1 const & h1 = Hash1(), Hash2 const & h2 = Hash2()):
        Hash1(h1),
        m_hash2(h2) {
    }

    unsigned operator()(std::pair<typename Hash1::data_t, typename Hash2::data_t> const & p) const {
        return combine_hash(Hash1::operator()(p.first), m_hash2.operator()(p.second));
    }
};

template<typename T>
inline unsigned get_ptr_hash(T * ptr) {
    return static_cast<unsigned>(reinterpret_cast<size_t>(ptr));
}

template<typename T>
struct ptr_hash {
    typedef T * data_t;
    unsigned operator()(T * ptr) const { 
        return get_ptr_hash(ptr);
    }
};

inline unsigned mk_mix(unsigned a, unsigned b, unsigned c) {
    mix(a, b, c);
    return c;
}


