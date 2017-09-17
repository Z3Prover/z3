/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include <string>
#include "util/lp/numeric_pair.h"
#include "util/debug.h"
#include <unordered_map>
template <typename A, typename B>
bool try_get_val(const std::unordered_map<A,B> & map, const A& key, B & val) {
    const auto it = map.find(key);
    if (it == map.end()) return false;
    val = it->second;
    return true;
}

template <typename A, typename B>
bool contains(const std::unordered_map<A, B> & map, const A& key) {
    return map.find(key) != map.end();
}

namespace lp {
    inline void throw_exception(const std::string & str) {
        throw default_exception(str);
    }
    typedef z3_exception exception;

    template <typename X> inline X zero_of_type() { return numeric_traits<X>::zero(); }
    template <typename X> inline X one_of_type() { return numeric_traits<X>::one(); }
    template <typename X> inline bool is_zero(const X & v) { return numeric_traits<X>::is_zero(v); }
    template <typename X> inline bool is_pos(const X & v) { return numeric_traits<X>::is_pos(v); }
    template <typename X> inline bool is_neg(const X & v) { return numeric_traits<X>::is_neg(v); }

    template <typename X> inline bool precise() { return numeric_traits<X>::precise(); }
}
namespace std {
template<>
struct hash<rational> {
    inline size_t operator()(const rational & v) const {
        return v.hash();
    }
};
}

template <class T>
inline void hash_combine(std::size_t & seed, const T & v) {
    seed ^= std::hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

namespace std {
template<typename S, typename T> struct hash<pair<S, T>> {
    inline size_t operator()(const pair<S, T> & v) const {
        size_t seed = 0;
        hash_combine(seed, v.first);
        hash_combine(seed, v.second);
        return seed;
    }
};

template<>
struct hash<lp::numeric_pair<lp::mpq>> {
    inline size_t operator()(const lp::numeric_pair<lp::mpq> & v) const {
        size_t seed = 0;
        hash_combine(seed, v.x);
        hash_combine(seed, v.y);
        return seed;
    }
};

}
