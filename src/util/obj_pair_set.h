/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    obj_pair_set.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-04-19

Revision History:

--*/
#ifndef OBJ_PAIR_SET_H_
#define OBJ_PAIR_SET_H_

#include"chashtable.h"

template<typename T1, typename T2>
class obj_pair_set {
public:
    typedef std::pair<T1*, T2*> obj_pair;
protected:
    struct hash_proc {
        unsigned operator()(obj_pair const & p) const { return combine_hash(p.first->hash(), p.second->hash()); }
    };
    struct eq_proc {
        bool operator()(obj_pair const & p1, obj_pair const & p2) const { return p1 == p2; }
    };
    typedef chashtable<obj_pair, hash_proc, eq_proc> set;
    set m_set;
public:
    obj_pair_set() {}
    void insert(T1 * t1, T2 * t2) { m_set.insert(obj_pair(t1, t2)); }
    void insert(obj_pair const & p) { m_set.insert(p); }
    bool insert_if_not_there(T1 * t1, T2 * t2) { return m_set.insert_if_not_there2(obj_pair(t1, t2)); }
    bool insert_if_not_there(obj_pair const & p) { return m_set.insert_if_not_there2(p); }
    void erase(T1 * t1, T2 * t2) { return m_set.erase(obj_pair(t1, t2)); }
    void erase(obj_pair const & p) { return m_set.erase(p); }
    bool contains(T1 * t1, T2 * t2) const { return m_set.contains(obj_pair(t1, t2)); }
    bool contains(obj_pair const & p) const { return m_set.contains(p); }
    void reset() { m_set.reset(); }
    bool empty() const { return m_set.empty(); }

    typedef typename chashtable<obj_pair, hash_proc, eq_proc>::iterator iterator;

    iterator begin() { return m_set.begin(); }
    iterator end() { return m_set.end(); }
};

#endif
