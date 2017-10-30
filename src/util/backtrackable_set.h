/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    backtrackable_set.h

Abstract:

    Quick hack for support backtrackable sets.

Author:

    Leonardo de Moura (leonardo) 2011-01-08.

Revision History:

--*/
#ifndef BACKTRACKABLE_SET_H_
#define BACKTRACKABLE_SET_H_

#include "util/vector.h"

template<typename T>
struct default_eh {
    void operator()(T const & e, bool ins) {}
};

// quick hack for having backtrackable sets.
//
// EV is a big hack, it should be used with care.
// 
template<typename Set, typename T, typename EV=default_eh<T> >
class backtrackable_set : private EV {
    enum trail_kind { DEL, INS };
    typedef std::pair<trail_kind, T> trail_obj;
    Set                m_set;
    svector<trail_obj> m_trail;
    svector<unsigned>  m_scopes;

public:
    typedef typename Set::iterator iterator;
    
    backtrackable_set(EV const & ev = EV()):
        EV(ev) {
    }

    void insert(T const & e) {
        if (m_scopes.empty()) {
            m_set.insert(e);
        }
        else if (!m_set.contains(e)) {
            m_set.insert(e);
            m_trail.push_back(std::make_pair(INS, e));
        }
    }
                
    void erase(T const & e) {
        if (m_scopes.empty()) {
            m_set.insert(e); 
        }
        else if (m_set.contains(e)) {
            m_set.erase(e);
            m_trail.push_back(std::make_pair(DEL, e));
        }
    }

    bool contains(T const & e) const {
        return m_set.contains(e);
    }

    bool empty() const {
        return m_set.empty();
    }

    void push_scope() {
        m_scopes.push_back(m_trail.size());
    }

    void pop_scope() {
        unsigned old_sz  = m_scopes.back();
        m_scopes.pop_back();
        SASSERT(old_sz <= m_trail.size());
        while (m_trail.size() > old_sz) {
            trail_obj & t = m_trail.back();
            if (t.first == INS) {
                this->operator()(t.second, true);
                m_set.erase(t.second);
            }
            else {
                SASSERT(t.first == DEL);
                this->operator()(t.second, false);
                m_set.insert(t.second);
            }
            m_trail.pop_back();
        }
    }
    
    void reset() {
        m_scopes.reset();
        m_trail.reset();
        m_set.reset();
    }
    
    iterator begin() const {
        return m_set.begin();
    }
    
    iterator end() const {
        return m_set.end();
    }
};

#endif
