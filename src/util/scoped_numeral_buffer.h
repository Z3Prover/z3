/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    scoped_numeral_buffer.h

Abstract:

    Wrapper for easying the pain when using buffers of numerals.

Author:

    Leonardo de Moura (leonardo) 2012-01-23

Revision History:

--*/
#ifndef _SCOPED_NUMERAL_BUFFER_H_
#define _SCOPED_NUMERAL_BUFFER_H_

#include"buffer.h"

template<typename Manager, unsigned INITIAL_SIZE = 16>
class _scoped_numeral_buffer : public sbuffer<typename Manager::numeral, INITIAL_SIZE> {
    typedef sbuffer<typename Manager::numeral, INITIAL_SIZE> super;
    Manager & m_manager;
    _scoped_numeral_buffer(_scoped_numeral_buffer const & v);
public:
    _scoped_numeral_buffer(Manager & m):m_manager(m) {}
    ~_scoped_numeral_buffer() {
        reset();
    }

    void reset() {
        unsigned sz = this->size();
        for (unsigned i = 0; i < sz; i++) {
            m().del(this->operator[](i));
        }
        super::reset();
    }

    Manager & m() const { return m_manager; }

    void push_back(typename Manager::numeral const & v) {
        super::push_back(typename Manager::numeral());
        m_manager.set(this->back(), v);
    }

    void shrink(unsigned sz) {
        unsigned old_sz = this->size();
        if (old_sz == sz)
            return;
        for (unsigned i = sz; i < old_sz; i++)
            m().del(this->operator[](i));
        super::shrink(sz);
    }

    void resize(unsigned sz) {
        unsigned old_sz = this->size();
        if (sz <= old_sz)
            shrink(sz);
        typename Manager::numeral zero(0);
        super::resize(sz, zero);
    }
};

#endif
