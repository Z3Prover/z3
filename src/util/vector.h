/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    vector.h

Author:

    Daniel Schemmel 2019-2-23

--*/

#pragma once

#include "buffvec.h"
#include "hash.h"

template<typename T, typename SZ = unsigned>
using vector = buffvec<T, SZ, 0>;

inline std::ostream& operator<<(std::ostream& out, vector<unsigned> const& v) {
    for (unsigned u : v) out << u << " ";
    return out;
}

template<typename Hash, typename Vec>
struct vector_hash_tpl {
    Hash m_hash;
    typedef Vec data;

    unsigned operator()(data const& v, unsigned idx) const { return m_hash(v[idx]); }

    vector_hash_tpl(Hash const& h = Hash()):m_hash(h) {}

    unsigned operator()(data const& v) const {
        if (v.empty()) {
            return 778;
        }
        return get_composite_hash<data, default_kind_hash_proc<data>, vector_hash_tpl>(v, v.size());
    }
};

template<typename Hash>
struct vector_hash : public vector_hash_tpl<Hash, vector<typename Hash::data> > {};
