/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
  This file should be present in z3 and in Lean.
*/
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

#ifdef lp_for_z3

#ifdef Z3DEBUG
#define LEAN_DEBUG 1
#endif

namespace lean {
    inline void throw_exception(const std::string & str) {
        throw default_exception(str);
    }
    typedef z3_exception exception;

#define lean_assert(_x_) { SASSERT(_x_); }
    inline void lean_unreachable() { lean_assert(false); }
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
struct hash<lean::numeric_pair<lean::mpq>> {
    inline size_t operator()(const lean::numeric_pair<lean::mpq> & v) const {
        size_t seed = 0;
        hash_combine(seed, v.x);
        hash_combine(seed, v.y);
        return seed;
    }
};

}
#else // else  of #if  lp_for_z3
#include <utility>
#include <functional>
//include "util/numerics/mpq.h"
//include "util/numerics/numeric_traits.h"
//include "util/numerics/double.h"

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
namespace lean {
template <typename X> inline bool  precise() { return numeric_traits<X>::precise();}
template <typename X> inline X one_of_type() { return numeric_traits<X>::one(); }
template <typename X> inline bool is_zero(const X & v) { return numeric_traits<X>::is_zero(v); }
template <typename X> inline double  get_double(const X & v) { return numeric_traits<X>::get_double(v); }
template <typename T> inline T zero_of_type() {return numeric_traits<T>::zero();}
inline void throw_exception(std::string str) { throw exception(str); }
template <typename T> inline T from_string(std::string const & ) { lean_unreachable();}
template <> double inline from_string<double>(std::string const & str) { return atof(str.c_str());}
template <> mpq inline from_string<mpq>(std::string const & str) {
    return mpq(atof(str.c_str()));
}

} // closing lean
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
struct hash<lean::numeric_pair<lean::mpq>> {
    inline size_t operator()(const lean::numeric_pair<lean::mpq> & v) const {
        size_t seed = 0;
        hash_combine(seed, v.x);
        hash_combine(seed, v.y);
        return seed;
    }
};
} // std
#ifdef __CLANG__
#pragma clang diagnostic pop
#endif
#endif
