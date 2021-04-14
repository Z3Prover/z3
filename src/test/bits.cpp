
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

// Test some bit hacks
#include "util/util.h"
#include "util/debug.h"
#include "util/vector.h"
#include "util/mpz.h"
#include "util/bit_util.h"

static void tst_shl(unsigned src_sz, unsigned const * src, unsigned k, 
                    unsigned dst_sz, unsigned const * dst, bool trace = true) {
    if (trace) {
        std::cout << "shl({";
        for (unsigned i = 0; i < src_sz; i++) {
            if (i > 0) std::cout << ", ";
            std::cout << src[i];
        }
        std::cout << "}, " << k << ")" << std::endl;
    }
    svector<unsigned> actual_dst;
    actual_dst.resize(dst_sz, 0xAAAAAAAA);
    for (unsigned sz = 1; sz <= dst_sz; sz++) {
        if (trace)
            std::cout << "  for sz = " << sz << std::endl;
        shl(src_sz, src, k, sz, actual_dst.data());
        ENSURE(!has_one_at_first_k_bits(sz, actual_dst.data(), k));
        for (unsigned i = 0; i < sz; i++) {
            if (trace && dst[i] != actual_dst[i])
                std::cout << "UNEXPECTED RESULT at [" << i << "]: " << actual_dst[i] << ", expected: " << dst[i] << "\n";
            ENSURE(dst[i] == actual_dst[i]);
        }
        if (sz == src_sz) {
            unsigned nz1 = nlz(sz, src);
            if (nz1 >= k && !is_zero(sz, src)) {
                unsigned nz2 = nlz(sz, actual_dst.data());
                if (nz1 - k != nz2) {
                    if (trace)
                        std::cout << "nlz BUG, nlz1: " << nz1 << ", k: " << k << ", nlz2: " << nz2 << std::endl;
                    UNREACHABLE();
                }
            }
        }
        if (sz >= src_sz + (k/32) + 1) {
            svector<unsigned> new_src;
            new_src.resize(sz, 0xAAAAAAAA);
            shr(sz, actual_dst.data(), k, new_src.data());
            for (unsigned i = 0; i < src_sz; i++) {
                if (trace && src[i] != new_src[i]) {
                    std::cout << "shr BUG, inverting shl, at bit[" << i << "], " << new_src[i] << ", expected: " << src[i] << std::endl;
                }
                ENSURE(src[i] == new_src[i]);
            }
        }
    }
    if (trace)
        std::cout << "  shift by 1, k times" << std::endl;
    copy(src_sz, src, dst_sz, actual_dst.data());
    for (unsigned i = 0; i < k; i++) {
        shl(dst_sz, actual_dst.data(), 1, dst_sz, actual_dst.data());
    }
    for (unsigned i = 0; i < dst_sz; i++) {
        if (trace && dst[i] != actual_dst[i])
            std::cout << "UNEXPECTED RESULT at [" << i << "]: " << actual_dst[i] << ", expected: " << dst[i] << "\n";
        ENSURE(dst[i] == actual_dst[i]);
    }
    if (src_sz <= dst_sz) {
        if (trace)
            std::cout << "  self-shl" << std::endl;
        shl(src_sz, src, k, src_sz, const_cast<unsigned*>(src));
        for (unsigned i = 0; i < src_sz; i++) {
            if (trace && src[i] != dst[i])
                std::cout << "UNEXPECTED RESULT at [" << i << "]: " << src[i] << ", expected: " << dst[i] << "\n";
            ENSURE(src[i] == actual_dst[i]);
        }
    }
}

static void tst_shl() {
    {
        unsigned src[2] = {0, 2}; unsigned dst[2] = {0, 2<<10};
        tst_shl(2, src, 10, 2, dst);
    }
    {
        unsigned src[2] = {2, 0}; unsigned dst[2] = {0, 2<<10};
        tst_shl(2, src, 42, 2, dst);
    }
    {
        unsigned src[2] = {0, 0}; unsigned dst[3] = {0, 0, 0};
        tst_shl(2, src, 1, 3, dst);
    }
    {
        unsigned src[2] = {0x80000009, 5}; unsigned dst[2] = {18, 11};
        tst_shl(2, src, 1, 2, dst);
    }
    {
        unsigned src[2] = {0x80000009, 0x80000005}; unsigned dst[2] = {18, 11};
        tst_shl(2, src, 1, 2, dst);
    }
    {
        unsigned src[2] = {0x80000009, 0x80000005}; unsigned dst[3] = {18, 11, 1};
        tst_shl(2, src, 1, 3, dst);
    }
    {
        unsigned src[2] = {0x80000009, 0x80000005}; unsigned dst[3] = {0, 18, 11};
        tst_shl(2, src, 33, 3, dst);
    }
    {
        unsigned src[2] = {0x80000009, 0x80000005}; unsigned dst[4] = {0, 18, 11, 1};
        tst_shl(2, src, 33, 4, dst);
    }
    {
        unsigned src[2] = {0xFFFFFFFF, 0xFFFFFFFF}; unsigned dst[2] = {0xFFFFFFF0, 0xFFFFFFFF};
        tst_shl(2, src, 4, 2, dst);
    }
}

static void tst_shr(unsigned src_sz, unsigned const * src, unsigned k, 
                    unsigned const * dst, bool trace = true) {
    if (trace) {
        std::cout << "shr({";
        for (unsigned i = 0; i < src_sz; i++) {
            if (i > 0) std::cout << ", ";
            std::cout << src[i];
        }
        std::cout << "}, " << k << ")" << std::endl;
    }
    svector<unsigned> actual_dst;
    actual_dst.resize(src_sz, 0xAAAAAAAA);
    shr(src_sz, src, k, actual_dst.data());
    for (unsigned i = 0; i < src_sz; i++) {
        if (trace && dst[i] != actual_dst[i])
            std::cout << "UNEXPECTED RESULT at [" << i << "]: " << actual_dst[i] << ", expected: " << dst[i] << "\n";
        ENSURE(dst[i] == actual_dst[i]);
    }
}

static void tst_shr() {
    {
        unsigned src[2] = {0, 0}; unsigned dst[2] = {0, 0};
        tst_shr(2, src, 1, dst);
    }
}

static void tst_shl_rand(unsynch_mpz_manager & m, unsigned sz, unsigned k, bool trace = true) {
    // create a random bitvector of of size sz
    svector<unsigned> src;
    for (unsigned i = 0; i < sz; i++) {
        src.push_back(rand());
    }
    // convert src into a mpz number
    scoped_mpz _src(m);
    scoped_mpz tmp(m);
    unsigned i = sz; 
    while (i > 0) {
        --i;
        m.mul2k(_src, 32);
        m.set(tmp, src[i]);
        m.add(_src, tmp, _src);
    }
    // shift left by multiplying by 2^k
    scoped_mpz _dst(m);
    m.set(_dst, _src);
    m.mul2k(_dst, k);
    // convert _dst into a vector of unsigned values
    svector<unsigned> dst;
    scoped_mpz max(m);
    m.set(max, 1);
    m.mul2k(max, 32);
    while (!m.is_zero(_dst)) {
        m.mod(_dst, max, tmp);
        ENSURE(m.is_uint64(tmp) && m.get_uint64(tmp) < UINT_MAX);
        dst.push_back(static_cast<unsigned>(m.get_uint64(tmp)));
        m.div(_dst, max, _dst);
    }
    while (dst.size() < src.size())
        dst.push_back(0);
    dst.push_back(0);
    unsigned word_shift = (k / 32);
    for (unsigned i = 0; i < word_shift; i++)
        dst.push_back(0);
    tst_shl(src.size(), src.data(), k, dst.size(), dst.data(), trace);
}

static void tst_shl_rand(unsigned N, unsigned sz, unsigned k, bool trace = false) {
    unsynch_mpz_manager m;
    for (unsigned i = 0; i < N; i++) {
        unsigned _sz = rand() % sz;
        if (_sz == 0) 
            _sz = 1;
        unsigned _k  = rand() % k;
        if (_k == 0)
            _k = 1;
        tst_shl_rand(m, _sz, _k, trace);
    }
}

void tst_bits() {
    tst_shr();
    tst_shl();
    tst_shl_rand(100000, 4, 100);
}




