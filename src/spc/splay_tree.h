/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    splay_tree.h

Abstract:

    Splay trees

Author:

    Leonardo de Moura (leonardo) 2008-01-31.

Revision History:

--*/
#ifndef _SPLAY_TREE_H_
#define _SPLAY_TREE_H_

#include"util.h"
#include"buffer.h"

template<typename Key, typename Compare>
class splay_tree : private Compare {
    struct cell {
        Key    m_key;
        cell * m_left;
        cell * m_right;

        cell():m_left(0), m_right(0) {}
        cell(Key const & k, cell * l = 0, cell * r = 0):
            m_key(k), m_left(l), m_right(r) {}
    };

    cell * m_root;
    int compare(Key const & k1, Key const & k2) const { return Compare::operator()(k1, k2); }
    cell * splay(cell * c, Key const & k);

    void display_core(std::ostream & out, cell * c) const {
        if (c) {
            out << "(" << c->m_key << " ";
            display_core(out, c->m_left);
            out << " ";
            display_core(out, c->m_right);
            out << ")";
        }
        else 
            out << "null";
    }

public:
    splay_tree(Compare const & c = Compare()):
        Compare(c),
        m_root(0) {}
    
    ~splay_tree() {
        m_root = 0;
    }

    void insert(Key const & k);

    bool find(Key const & k, Key & r) const;

    void erase(Key const & k);

    void reset();

    bool empty() const { return m_root == 0; }

    bool singleton() const { return m_root != 0 && m_root->m_left == 0 && m_root->m_right == 0; }

    /**
       \brief Visit nodes in the splay tree in ascending order.
       The Visitor functor should provide the following methods:
       
       - bool visit_left(Key const & k)
         return true if the left child should be visited

       - bool visit_right(Key const & k)
         return true if the right child should be visited

       - void operator()(Key const & k)
         do something with the key.
    */
    template<typename Visitor>
    void visit_core(Visitor & v) {
        typedef std::pair<cell *, bool> entry;
        if (m_root) {
            buffer<entry> todo;
            todo.push_back(entry(m_root, false));
            while (!todo.empty()) {
                entry & curr = todo.back();
                cell * c = curr.first;
                if (!curr.second) {
                    curr.second = true;
                    if (c->m_left && v.visit_left(c->m_key))
                        todo.push_back(entry(c->m_left, false));
                }
                else {
                    v(c->m_key);
                    todo.pop_back();
                    if (c->m_right && v.visit_right(c->m_key))
                        todo.push_back(entry(c->m_right, false));
                }
            }
        }
    }

    template<typename Visitor>
    struct all_visitor_wrapper {
        Visitor & m_visitor;
        all_visitor_wrapper(Visitor & v):m_visitor(v) {}
        bool visit_right(Key const & k) { return true; }
        bool visit_left(Key const & k) { return true; }
        void operator()(Key const & k) { m_visitor.operator()(k); }
    };

    /**
       \brief Visit all nodes in the splay tree in ascending order.

       - void operator()(Key const & k)
         do something with the key pair.
    */
    template<typename Visitor>
    void visit(Visitor & v) {
        all_visitor_wrapper<Visitor> w(v);
        visit_core(w);
    }

    template<typename Visitor, bool LE>
    struct visitor_wrapper {
        Visitor &    m_visitor;
        splay_tree & m_tree;
        Key          m_key;
        visitor_wrapper(Visitor & v, splay_tree & t, Key const & k):m_visitor(v), m_tree(t), m_key(k) {}
        bool visit_left(Key const & k) { 
            return LE || m_tree.compare(k, m_key) > 0;
        }
        bool visit_right(Key const & k) { 
            return !LE || m_tree.compare(k, m_key) < 0;
        }
        void operator()(Key const & k) {
            if ((LE  && m_tree.compare(k, m_key) <= 0) ||
                (!LE && m_tree.compare(k, m_key) >= 0)) 
                m_visitor.operator()(k);
        }
    };

    /**
       \brief Visit all nodes with keys less than or equal to k.

       - void operator()(Key const & k)
         do something with the key.
    */
    template<typename Visitor>
    void visit_le(Visitor & v, Key const & k) {
        visitor_wrapper<Visitor, true> w(v, *this, k);
        visit_core(w);
    }

    /**
       \brief Visit all nodes with keys greater than or equal to k.

       - void operator()(Key const & k)
         do something with the key.
    */
    template<typename Visitor>
    void visit_ge(Visitor & v, Key const & k) {
        visitor_wrapper<Visitor, false> w(v, *this, k);
        visit_core(w);
    }

    void display(std::ostream & out) const {
        display_core(out, m_root);
    }
};

#endif
