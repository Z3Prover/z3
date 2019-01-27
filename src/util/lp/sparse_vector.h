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
#include "util/vector.h"
#include <utility>
#include "util/debug.h"
#include "util/lp/lp_utils.h"
#include "util/lp/lp_settings.h"
namespace lp {

template <typename T>
class sparse_vector {
public:
    vector<std::pair<unsigned, T>>  m_data;
    void push_back(unsigned index, T val) {
        m_data.push_back(std::make_pair(index, val));
    }
#ifdef Z3DEBUG
    T operator[] (unsigned i) const {
        for (auto &t : m_data) {
            if (t.first == i) return t.second;
        }
        return numeric_traits<T>::zero();
    }
#endif
    void divide(T const & a) {
        lp_assert(!lp_settings::is_eps_small_general(a, 1e-12));
        for (auto & t : m_data) {  t.second /= a; }
    }

    unsigned size() const {
        return m_data.size();
    }
};
}
