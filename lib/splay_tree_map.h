/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    splay_tree_map.h

Abstract:

    A mapping as a splay tree.

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#ifndef _SPLAY_TREE_MAP_H_
#define _SPLAY_TREE_MAP_H_

#include"splay_tree.h"

template<typename Key, typename Data, typename Compare>
class splay_tree_map {
    typedef std::pair<Key, Data> entry;

    struct entry_compare : private Compare {
        entry_compare(Compare const & c):Compare(c) {}
        int operator()(entry const & e1, entry const & e2) const {
            return Compare::operator()(e1.first, e2.first);
        }
    };

    typedef splay_tree<entry, entry_compare> tree;
    
    tree m_tree;
    
    template<typename Visitor>
    struct core_visitor_wrapper {
        Visitor & m_visitor;
        core_visitor_wrapper(Visitor & v):m_visitor(v) {}
        bool visit_right(entry const & k) { return m_visitor.visit_right(k.first); }
        bool visit_left(entry const & k) {  return m_visitor.visit_left(k.first); }
        void operator()(entry const & k) { m_visitor.operator()(k.first, k.second); }
    };

    template<typename Visitor>
    struct visitor_wrapper {
        Visitor & m_visitor;
        visitor_wrapper(Visitor & v):m_visitor(v) {}
        void operator()(entry const & k) { m_visitor.operator()(k.first, k.second); }
    };

public:
    splay_tree_map(Compare const & c = Compare()):
        m_tree(entry_compare(c)) {}

    void insert(Key const & k, Data const & d) {
        m_tree.insert(entry(k, d));
    }

    bool find(Key const & k, Data & r) const {
        entry e(k, r);
        if (m_tree.find(e, e)) {
            r = e.second;
            return true;
        }
        return false;
    }

    void erase(Key const & k) {
        entry e;
        e.first = k;
        m_tree.erase(e);
    }

    void reset() { m_tree.reset(); }

    bool empty() const { return m_tree.empty(); }

    void display(std::ostream & out) const { m_tree.display(out); }

    template<typename Visitor>
    void visit_core(Visitor & v) {
        core_visitor_wrapper<Visitor> w(v);
        m_tree.visit_core(w);
    }

    template<typename Visitor>
    void visit(Visitor & v) {
        visitor_wrapper<Visitor> w(v);
        m_tree.visit(w);
    }

    template<typename Visitor>
    void visit_le(Visitor & v, Key const & k) {
        visitor_wrapper<Visitor> w(v);
        entry e;
        e.first = k;
        m_tree.visit_le(w, e);
    }

    template<typename Visitor>
    void visit_ge(Visitor & v, Key const & k) {
        visitor_wrapper<Visitor> w(v);
        entry e;
        e.first = k;
        m_tree.visit_ge(w, e);
    }
};

#endif /* _SPLAY_TREE_MAP_H_ */

