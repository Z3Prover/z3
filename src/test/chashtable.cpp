/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    chashtable.cpp

Abstract:

    Hashtable with chaining.  
    
Author:

    Leonardo de Moura (leonardo) 2011-04-14.

Revision History:

--*/
#include "util/chashtable.h"
#include "util/hashtable.h"
#include "util/hash.h"
#include "util/util.h"
#include <iostream>
#include <cstdint>
#include <vector>

typedef chashtable<int, int_hash, default_eq<int> > int_table;
typedef cmap<int, int, int_hash, default_eq<int> > int_map;

template class chashtable<int, int_hash, default_eq<int> >;
template class cmap<int, int, int_hash, default_eq<int> >;

template<typename T>
static void display(T const & beg, T const & end) {
    for (T it = beg; it != end; ++it)
        std::cout << *it << " ";
    std::cout << "\n";
}

static void tst1() {
    int_table t;
    t.insert(10);
    ENSURE(t.contains(10));
    t.insert(20);
    ENSURE(t.contains(20));
    t.insert(30);
    ENSURE(t.contains(30));
    ENSURE(t.size() == 3);
    display(t.begin(), t.end());
    t.erase(20);
    ENSURE(!t.contains(20));
    ENSURE(t.size() == 2);
}

struct dummy_hash {
    unsigned operator()(int v) const { return v % 2; }
};

typedef chashtable<int, dummy_hash, default_eq<int> > dint_table;

template class chashtable<int, dummy_hash, default_eq<int> >;

static void tst2() {
    dint_table t;
    t.insert(10);
    t.insert(12);
    ENSURE(t.used_slots() == 1);
    display(t.begin(), t.end());
    t.insert(13);
    display(t.begin(), t.end());
    ENSURE(t.used_slots() == 2);
    t.insert(14);
    ENSURE(t.used_slots() == 2);
    ENSURE(t.size() == 4);
    display(t.begin(), t.end());
    t.erase(12);
    ENSURE(!t.contains(12));
    ENSURE(t.size() == 3);
    ENSURE(t.contains(10));
    ENSURE(!t.contains(12));
    ENSURE(t.contains(14));
    ENSURE(t.contains(13));
    t.insert(16);
    ENSURE(t.size() == 4);
    t.insert(18);
    ENSURE(t.size() == 5);
    ENSURE(t.used_slots() == 2);
    display(t.begin(), t.end());
    t.erase(10);
    display(t.begin(), t.end());
    ENSURE(!t.contains(10));
    ENSURE(!t.contains(12));
    ENSURE(t.contains(14));
    ENSURE(t.contains(13));
    ENSURE(t.contains(16));
    ENSURE(t.contains(18));
}

static void tst3() {
    dint_table t;
    t.insert(10);
    t.insert(12);
    ENSURE(t.used_slots() == 1);
    ENSURE(t.contains(10));
    ENSURE(t.contains(12));
    t.erase(12);
    t.erase(10);
    ENSURE(t.empty());
    ENSURE(t.empty());
    ENSURE(t.used_slots() == 0);
    t.insert(10);
    ENSURE(t.used_slots() == 1);
    ENSURE(t.contains(10));
    ENSURE(t.size() == 1);
}

typedef int_hashtable<int_hash, default_eq<int> > int_set;

template<typename T>
static void tst4(unsigned num, unsigned N) {
    int_set s;
    T       t;
    for (unsigned i = 0; i < num; ++i) {
        int v = rand() % N;
        if (rand() % 3 == 2) {
            TRACE(chashtable, tout << "erase " << v << "\n";);
            s.erase(v);
            t.erase(v);
            ENSURE(!t.contains(v));
        }
        else {
            TRACE(chashtable, tout << "insert " << v << "\n";);
            s.insert(v);
            t.insert(v);
            ENSURE(t.contains(v));
        }
        ENSURE(s.size() == t.size());
        ENSURE(s.empty() == t.empty());
    }
    std::cout << "size: " << s.size() << " " << t.size() << "\n";
    int_set::iterator it1  = s.begin();
    int_set::iterator end1 = s.end();
    for(; it1 != end1; ++it1) {
        ENSURE(t.contains(*it1));
    }

    typename T::iterator it2  = t.begin();
    typename T::iterator end2 = t.end();
    for(; it2 != end2; ++it2) {
        ENSURE(s.contains(*it2));
        ENSURE(t.contains(*it2));
    }
}

static void tst5() {
    dint_table t;
    t.insert(4);
    t.insert(9);
    t.insert(8);
    t.insert(1);
    t.erase(1);
    t.insert(7);
    t.insert(1);
    t.insert(2);
}

static void tst6() {
    int_map m;
    m.insert(10, 4);
    ENSURE(m.contains(10));
    DEBUG_CODE({
        int r;
        ENSURE(m.find(10, r) && r == 4);
    });
}

static unsigned combine_hash_old(unsigned h1, unsigned h2) {
    h2 -= h1; h2 ^= (h1 << 8);
    h1 -= h2; h2 ^= (h1 << 16);
    h2 -= h1; h2 ^= (h1 << 10);
    return h2;
}

struct hash_projection_stats {
    unsigned m_occupied = 0;
    uint64_t m_uniform_error = 0;
};

template<typename CombineHash>
static hash_projection_stats get_projection_stats(CombineHash const& combine, unsigned bits, bool low_bits) {
    constexpr unsigned num_samples = 1u << 16;
    constexpr unsigned seed = 0x12345678u;
    constexpr unsigned alignment_shift = 12;
    SASSERT(bits <= 16);
    unsigned const num_buckets = 1u << bits;
    unsigned const mask = num_buckets - 1;
    std::vector<unsigned> counts(num_buckets, 0);
    for (unsigned i = 0; i < num_samples; ++i) {
        unsigned h = combine(i << alignment_shift, seed);
        unsigned b = low_bits ? (h & mask) : (h >> (32 - bits));
        counts[b]++;
    }

    hash_projection_stats st;
    for (unsigned c : counts) {
        if (c != 0)
            ++st.m_occupied;
        int64_t diff = static_cast<int64_t>(c) * num_buckets - num_samples;
        st.m_uniform_error += static_cast<uint64_t>(diff * diff);
    }
    return st;
}

static void tst_combine_hash_low_bits() {
    constexpr unsigned num_samples = 1u << 16;
    constexpr unsigned bits8 = 8;
    constexpr unsigned bits16 = 16;

    auto old_low8 = get_projection_stats(combine_hash_old, bits8, true);
    auto new_low8 = get_projection_stats(combine_hash, bits8, true);
    auto old_low16 = get_projection_stats(combine_hash_old, bits16, true);
    auto new_low16 = get_projection_stats(combine_hash, bits16, true);
    auto old_high8 = get_projection_stats(combine_hash_old, bits8, false);
    auto new_high8 = get_projection_stats(combine_hash, bits8, false);
    auto old_high16 = get_projection_stats(combine_hash_old, bits16, false);
    auto new_high16 = get_projection_stats(combine_hash, bits16, false);

    unsigned old_low8_collisions = num_samples - old_low8.m_occupied;
    unsigned new_low8_collisions = num_samples - new_low8.m_occupied;
    unsigned old_low16_collisions = num_samples - old_low16.m_occupied;
    unsigned new_low16_collisions = num_samples - new_low16.m_occupied;

    ENSURE(new_low8_collisions < old_low8_collisions);
    ENSURE(new_low16_collisions < old_low16_collisions);
    ENSURE(new_low8.m_uniform_error < old_low8.m_uniform_error);
    ENSURE(new_low16.m_uniform_error < old_low16.m_uniform_error);
    // The high bits should remain well distributed after the update.
    ENSURE(new_high8.m_uniform_error < old_high8.m_uniform_error * 2);
    ENSURE(new_high16.m_uniform_error < old_high16.m_uniform_error * 2);

    std::cout << "combine_hash old/new low8 collisions: "
              << old_low8_collisions << "/" << new_low8_collisions << "\n";
    std::cout << "combine_hash old/new low16 collisions: "
              << old_low16_collisions << "/" << new_low16_collisions << "\n";
    std::cout << "combine_hash old/new low8 uniform_error: "
              << old_low8.m_uniform_error << "/" << new_low8.m_uniform_error << "\n";
    std::cout << "combine_hash old/new low16 uniform_error: "
              << old_low16.m_uniform_error << "/" << new_low16.m_uniform_error << "\n";
    std::cout << "combine_hash old/new high8 uniform_error: "
              << old_high8.m_uniform_error << "/" << new_high8.m_uniform_error << "\n";
    std::cout << "combine_hash old/new high16 uniform_error: "
              << old_high16.m_uniform_error << "/" << new_high16.m_uniform_error << "\n";
}

void tst_chashtable() {
    tst1();
    tst2();
    tst3();
    tst6();
    tst4<dint_table>(1000,10);
    tst4<dint_table>(10000,10);
    tst4<int_table>(50000,1000);
    tst_combine_hash_low_bits();
    tst5();
}
