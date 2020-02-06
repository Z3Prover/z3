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
#include "math/lp/numeric_pair.h"
#include "util/debug.h"
#include <unordered_map>
#include <unordered_set>
template <typename C>
std::ostream& print_vector(const C & t, std::ostream & out) {
    for (const auto & p : t)
        out << p << " ";
    return out;
}
template <typename C>
std::ostream& print_vector_of_ptrs(const C & t, std::ostream & out) {
    for (const auto & p : t)
        out << (*p) << ", ";
    return out;
}

template <typename C, typename D>
bool contains(const C & collection, const D & key) {
    return collection.find(key) != collection.end();
}

template <typename C>
std::ostream& print_vector(const C * t, unsigned size, std::ostream & out) {
    for (unsigned i = 0; i < size; i++ )
        out << t[i] << " ";
    out << std::endl;
    return out;
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

#ifdef Z3DEBUG
#define Z3DEBUG 1
#endif

namespace lp {

template <typename K> 
bool is_non_decreasing(const K& v) {
    auto a = v.begin();
    if (a == v.end())
        return true; // v is empty
    auto b = v.begin();
    b++;
    for (; b != v.end(); a++, b++) {
        if (*a > *b)
            return false;
    }
    return true; 
}

template <typename T>
std::ostream& print_linear_combination_customized(const vector<std::pair<T, unsigned>> & coeffs, std::function<std::string (unsigned)> var_str, std::ostream & out) {
    bool first = true;
    for (const auto & it : coeffs) {
        T val = it.first;
        if (first) {
            first = false;
            if (val.is_neg()) {
                out << "- ";
                val = -val;
            }    
        } else {
            if (val.is_pos()) {
                out << " + ";
            } else {
                out << " - ";
                val = -val;
            }
        }
        if (val != 1) {
            out << T_to_string(val);
        }
        out << var_str(it.second);
    }
    return out;
}


template <typename T>
std::ostream& print_linear_combination_of_column_indices_only(const vector<std::pair<T, unsigned>> & coeffs, std::ostream & out) {
    return print_linear_combination_customized(
        coeffs,
        [](unsigned j) {std::stringstream ss; ss << "v" << j; return ss.str();},
        out); 
}
template <typename T, typename K>
std::ostream& print_linear_combination_indices_only(const T & coeffs, std::ostream & out) {
    vector<std::pair<K, unsigned>>  cfs;
    
    for (const auto & it : coeffs) {
        cfs.push_back(std::make_pair(it.coeff(), it.var()));
    }
    return print_linear_combination_of_column_indices_only<K>(cfs, out);
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
template <typename X> inline bool is_integer(const X & v) { return numeric_traits<X>::is_int(v); }

template <typename X> inline X ceil_ratio(const X & a, const X & b) { return numeric_traits<X>::ceil_ratio(a, b); }
template <typename X> inline X floor_ratio(const X & a, const X & b) { return numeric_traits<X>::floor_ratio(a, b); }


template <typename X> inline bool precise() { return numeric_traits<X>::precise(); }


// returns true if a factor of b
template <typename T>
bool is_proper_factor(const T & a, const T & b) {
    if (a.size() >= b.size())
        return false;
    SASSERT(lp::is_non_decreasing(a) && lp::is_non_decreasing(b));
    auto i = a.begin();
    auto j = b.begin();
    
    while (true) {
        if (i == a.end()) {
            return true;
        }
        if (j == b.end()) {
            return false;
        }

        if (*i == *j) {
            i++;j++;
            continue;
        } 

        j++;
    }
}

    // b / a, where a is a factor of b and both vectors are sorted
template <typename T>
svector<unsigned> vector_div(const T & b, const T & a) {
    SASSERT(lp::is_non_decreasing(a));
    SASSERT(lp::is_non_decreasing(b));
    SASSERT(is_proper_factor(a, b));
    svector<unsigned> r;
    auto i = a.begin();
    auto j = b.begin();
    
    while (true) {
        if (j == b.end()) {
            break;
        }
        if (i == a.end()) {
            r.push_back(*j);
            j++;
            continue;
        }

        if (*i == *j) {
            i++;j++;
            continue;
        } 

        r.push_back(*j);
        j++;
    }
    return r;
}

} // namespace lp

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

inline
void intersect_set(std::unordered_set<unsigned>& p, const std::unordered_set<unsigned>& w) {
        for (auto it = p.begin(); it != p.end(); ) {
            auto iit = it;
            iit ++;
            if (w.find(*it) == w.end())
                p.erase(it);
            it = iit;
        }
    }


}


