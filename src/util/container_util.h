/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    container_util.h

Abstract:

    Useful functions for containers

Author:

    Krystof Hoder, Nikolaj Bjorner 2017-10-24

Revision History:

    Extracted from dl_util.h

--*/

#ifndef CONTAINER_UTIL_H_
#define CONTAINER_UTIL_H_

// -----------------------------------
//
// container functions
//
// -----------------------------------

template<class Set1, class Set2>
void set_intersection(Set1 & tgt, const Set2 & src) {
    svector<typename Set1::data> to_remove;
    for (auto const& itm : tgt) 
        if (!src.contains(itm)) 
            to_remove.push_back(itm);
    while (!to_remove.empty()) {
        tgt.remove(to_remove.back());
        to_remove.pop_back();
    }
}

template<class Set>
void set_difference(Set & tgt, const Set & to_remove) {
    for (auto const& itm : to_remove) 
        tgt.remove(itm);
}

template<class Set1, class Set2>
void set_union(Set1 & tgt, const Set2 & to_add) {
    for (auto const& itm : to_add) 
        tgt.insert(itm);
}

template<class T>
void unite_disjoint_maps(T & tgt, const T & src) {
    for (auto const& kv : src) {
        SASSERT(!tgt.contains(kv.m_key));
        tgt.insert(kv.m_key, kv.m_value);
    }
}

template<class T, class U>
void collect_map_range(T & acc, const U & map) {
    for (auto const& kv : map) 
        acc.push_back(kv.m_value);
}


template<class T>
void print_container(const T & begin, const T & end, std::ostream & out) {
    T it = begin;
    out << "(";
    bool first = true;
    for(; it!=end; ++it) {
        if(first) { first = false; } else { out << ","; }
        out << (*it);
    }
    out << ")";
}

template<class T>
void print_container(const T & cont, std::ostream & out) {
    print_container(cont.begin(), cont.end(), out);
}

template<class T, class M>
void print_container(const ref_vector<T,M> & cont, std::ostream & out) {
    print_container(cont.c_ptr(), cont.c_ptr() + cont.size(), out);
}

template<class T>
void print_map(const T & cont, std::ostream & out) {
    out << "(";
    bool first = true;
    for (auto const& kv : cont) {
        if (first) { first = false; } else { out << ","; }
        out << kv.m_key << "->" << kv.m_value;
    }
    out << ")";
}

template<class It, class V> 
unsigned find_index(const It & begin, const It & end, const V & val) {
    It it = begin;
    for (unsigned idx = 0; it != end; it++, idx++) {
        if (*it == val) {
            return idx;
        }
    }
    return UINT_MAX;
}

template<class T, class U>
bool containers_equal(const T & begin1, const T & end1, const U & begin2, const U & end2) {
    T it1 = begin1;
    U it2 = begin2;
    for (; it1 != end1 && it2 != end2 && *it1 == *it2; ++it1, ++it2) {};
    return it1 == end1 && it2 == end2;
}

#endif
