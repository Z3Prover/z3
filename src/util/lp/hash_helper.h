/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
#include <utility>
#include <functional>
#include "util/numerics/mpq.h"
#ifdef __CLANG__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wmismatched-tags"
#endif
namespace std {
template<>
struct hash<lean::mpq> {
    inline size_t operator()(const lean::mpq & v) const {
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
}
#ifdef __CLANG__
#pragma clang diagnostic pop
#endif
