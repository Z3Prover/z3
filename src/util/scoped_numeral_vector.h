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
#ifndef _SCOPED_NUMERAL_VECTOR_H_
#define _SCOPED_NUMERAL_VECTOR_H_

#include"vector.h"

template<typename Manager>
class _scoped_numeral_vector : public svector<typename Manager::numeral> {
    Manager & m_manager;
    _scoped_numeral_vector(_scoped_numeral_vector const & v);
public:
    _scoped_numeral_vector(Manager & m):m_manager(m) {}
    ~_scoped_numeral_vector() {
        reset();
    }

    void reset() {
        unsigned sz = this->size();
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
        typename Manager::numeral zero(0);
        svector<typename Manager::numeral>::resize(sz, zero);
    }
};

#endif
