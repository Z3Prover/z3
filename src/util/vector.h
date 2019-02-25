/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    vector.h

Author:

    Daniel Schemmel 2019-2-23

--*/

#ifndef VECTOR_H_
#define VECTOR_H_

#include "old_vector.h"
#include "hash.h"

template<typename T, bool CallDestructors=true, typename SZ = unsigned>
using vector = old_vector<T, CallDestructors, SZ>;

template<typename T, typename SZ = unsigned>
using svector = old_svector<T, SZ>;

template<typename T>
using ptr_vector = old_ptr_vector<T>;

using int_vector         = old_svector<int>;
using unsigned_vector    = old_svector<unsigned>;
using char_vector        = old_svector<char>;
using signed_char_vector = old_svector<signed char>;
using double_vector      = old_svector<double>;

inline std::ostream& operator<<(std::ostream& out, unsigned_vector const& v) {
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

template<typename Hash>
struct svector_hash : public vector_hash_tpl<Hash, svector<typename Hash::data> > {};

#endif /* VECTOR_H_ */
