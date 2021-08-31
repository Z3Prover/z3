/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    lim_vector.h

Abstract:

    Vector that restores during backtracking.

Author:

    Nikolaj Bjorner (nbjorner) 2020-29-09

--*/
#pragma once

#include "util/vector.h"

template<typename T>
class lim_svector : public svector<T, unsigned> {
    unsigned_vector  m_lim;
public:
    void push_scope() {
        m_lim.push_back(this->size());
    }

    void pop_scope(unsigned num_scopes) {
        SASSERT(num_scopes > 0);
        unsigned old_sz = m_lim.size() - num_scopes;
        this->shrink(m_lim[old_sz]);
        m_lim.shrink(old_sz);
    }

    unsigned num_scopes() const { return m_lim.size(); }

    unsigned old_size(unsigned n) const { return m_lim[m_lim.size() - n]; }
};

