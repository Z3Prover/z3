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
template <typename C>
void print_vector(const C & t, std::ostream & out) {
    for (const auto & p : t)
        out << p << " ";
    out << std::endl;
}

template <typename A, typename B>
bool try_get_value(const std::unordered_map<A,B> & map, const A& key, B & val) {
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
#define Z3DEBUG 1
#endif

namespace lp {

template <typename T>
void print_linear_combination_of_column_indices_only(const T & coeffs, std::ostream & out) {
    bool first = true;
    for (const auto & it : coeffs) {
        auto val = it.coeff();
        if (first) {
            first = false;
        } else {
            if (val.is_pos()) {
                out << " + ";
            } else {
                out << " - ";
                val = -val;
            }
        }
        if (val == 1)
            out << " ";
        else 
            out << T_to_string(val);
        
        out << "x" << it.var();
    }
}

inline void throw_exception(std::string && str) {
    throw default_exception(std::move(str));
}
typedef z3_exception exception;

#define lp_assert(_x_) { SASSERT(_x_); }
inline void lp_unreachable() { lp_assert(false); }
template <typename X> inline X zero_of_type() { return numeric_traits<X>::zero(); }
template <typename X> inline X one_of_type() { return numeric_traits<X>::one(); }
template <typename X> inline bool is_zero(const X & v) { return numeric_traits<X>::is_zero(v); }
template <typename X> inline bool is_pos(const X & v) { return numeric_traits<X>::is_pos(v); }
template <typename X> inline bool is_neg(const X & v) { return numeric_traits<X>::is_neg(v); }
template <typename X> inline bool is_int(const X & v) { return numeric_traits<X>::is_int(v); }

template <typename X> inline X ceil_ratio(const X & a, const X & b) { return numeric_traits<X>::ceil_ratio(a, b); }
template <typename X> inline X floor_ratio(const X & a, const X & b) { return numeric_traits<X>::floor_ratio(a, b); }


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
struct hash<lp::mpq> {
    inline size_t operator()(const lp::mpq & v) const {
        return v.hash();
    }
};
}
namespace lp {
template <typename X> inline bool  precise() { return numeric_traits<X>::precise();}
template <typename X> inline X one_of_type() { return numeric_traits<X>::one(); }
template <typename X> inline bool is_zero(const X & v) { return numeric_traits<X>::is_zero(v); }
template <typename X> inline bool is_pos(const X & v) { return numeric_traits<X>::is_pos(v); }
template <typename X> inline bool is_int(const X & v) { return numeric_traits<X>::is_int(v); }
template <typename X> inline X ceil_ratio(const X & a, const X & b) { return numeric_traits<X>::ceil_ratio(a, b); }
template <typename X> inline X floor_ratio(const X & a, const X & b) { return numeric_traits<X>::floor_ratio(v); }


template <typename X> inline double  get_double(const X & v) { return numeric_traits<X>::get_double(v); }
template <typename T> inline T zero_of_type() {return numeric_traits<T>::zero();}
inline void throw_exception(std::string str) { throw exception(str); }
template <typename T> inline T from_string(std::string const & ) { lp_unreachable();}
template <> double inline from_string<double>(std::string const & str) { return atof(str.c_str());}
template <> mpq inline from_string<mpq>(std::string const & str) {
    return mpq(atof(str.c_str()));
}

} // closing lp
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
} // std
#ifdef __CLANG__
#pragma clang diagnostic pop
#endif
#endif
