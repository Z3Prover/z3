/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    scoped_numeral_vector.h

Abstract:

    Wrapper for easying the pain when using vectors of numerals.

Author:

    Leonardo de Moura (leonardo) 2011-12-03

Revision History:

--*/
#pragma once

#include "util/vector.h"

template<typename Manager>
class _scoped_numeral_vector : public svector<typename Manager::numeral> {
    Manager & m_manager;
public:
    _scoped_numeral_vector(Manager & m):m_manager(m) {}

    _scoped_numeral_vector(const _scoped_numeral_vector & other) : m_manager(other.m_manager) {
        for (unsigned i = 0, e = other.size(); i != e; ++i) {
            push_back((*this)[i]);
        }
    }

    _scoped_numeral_vector(_scoped_numeral_vector&&) = default;

    ~_scoped_numeral_vector() {
        reset();
    }

    void reset() {
        auto sz = this->size();
        for (unsigned i = 0; i < sz; i++) {
            m().del(this->operator[](i));
        }
        svector<typename Manager::numeral>::reset();
    }

    Manager & m() const { return m_manager; }

    void push_back(typename Manager::numeral const & v) {
        svector<typename Manager::numeral>::push_back(typename Manager::numeral());
        m_manager.set(this->back(), v);
    }

    void pop_back() {
        shrink(this->size()-1);
    }

    void shrink(unsigned sz) {
        unsigned old_sz = this->size();
        if (old_sz == sz)
            return;
        for (unsigned i = sz; i < old_sz; i++)
            m().del(this->operator[](i));
        svector<typename Manager::numeral>::shrink(sz);
    }

    void resize(unsigned sz) {
        unsigned old_sz = this->size();
        if (sz <= old_sz)
            shrink(sz);
        svector<typename Manager::numeral>::resize(sz, 0);
    }
};
