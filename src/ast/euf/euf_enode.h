/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_enode.h

Abstract:

    enode layer

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-23

--*/

#include "util/vector.h"
#include "ast/ast.h"
#include "ast/euf/euf_justification.h"

#pragma once

namespace euf {

    class enode;

    typedef ptr_vector<enode> enode_vector;
    typedef std::pair<enode*,enode*> enode_pair;
    typedef svector<enode_pair> enode_pair_vector;

    class enode {
        expr*         m_owner;
        bool          m_mark1 { false };
        bool          m_mark2 { false };
        bool          m_commutative { false };
        bool          m_update_children { false };
        bool          m_interpreted { false };
        unsigned      m_class_size { 1 };
        unsigned      m_table_id { UINT_MAX };
        enode_vector  m_parents;
        enode*        m_next;
        enode*        m_root;
        enode*        m_target { nullptr };
        justification m_justification;
        unsigned      m_num_args;
        enode*        m_args[0];        

        friend class enode_args;
        friend class enode_parents;
        friend class enode_class;
        friend class etable;
        friend class egraph;

        static unsigned get_enode_size(unsigned num_args) {
            return sizeof(enode) + num_args * sizeof(enode*);
        }

        static enode* mk(region& r, expr* f, unsigned num_args, enode* const* args) {
            SASSERT(num_args <= (is_app(f) ? to_app(f)->get_num_args() : 0));
            void* mem = r.allocate(get_enode_size(num_args));
            enode* n = new (mem) enode();
            n->m_owner = f;
            n->m_next = n;
            n->m_root = n;
            n->m_commutative = num_args == 2 && is_app(f) && to_app(f)->get_decl()->is_commutative();
            n->m_num_args = num_args;
            for (unsigned i = 0; i < num_args; ++i) {
                SASSERT(to_app(f)->get_arg(i) == args[i]->get_owner());
                n->m_args[i] = args[i];
            }
            return n;
        }
        
        void set_update_children() { m_update_children = true; }
    public:
        ~enode() { 
            SASSERT(m_root == this); 
            SASSERT(class_size() == 1); 
            if (m_update_children) {
                for (unsigned i = 0; i < num_args(); ++i) {
                    SASSERT(m_args[i]->get_root()->m_parents.back() == this);
                    m_args[i]->get_root()->m_parents.pop_back();
                }
            }
        }

        enode* const* args() const { return m_args; }
        unsigned num_args() const { return m_num_args; }
        unsigned num_parents() const { return m_parents.size(); }
        bool interpreted() const { return m_interpreted; }
        bool commutative() const { return m_commutative; }
        void mark_interpreted() { SASSERT(num_args() == 0); m_interpreted = true; }

        enode* get_arg(unsigned i) const { SASSERT(i < num_args()); return m_args[i]; }        
        unsigned hash() const { return m_owner->hash(); }
        func_decl* get_decl() const { return is_app(m_owner) ? to_app(m_owner)->get_decl() : nullptr; } 
        unsigned get_table_id() const { return m_table_id; }
        void     set_table_id(unsigned t) { m_table_id = t; }

        void mark1() { m_mark1 = true; }
        void unmark1() { m_mark1 = false; }
        bool is_marked1() { return m_mark1; }
        void mark2() { m_mark2 = true; }
        void unmark2() { m_mark2 = false; }
        bool is_marked2() { return m_mark2; }
        void add_parent(enode* p) { m_parents.push_back(p); }
        unsigned class_size() const { return m_class_size; }
        enode* get_root() const { return m_root; }
        expr*  get_owner() const { return m_owner; }
        unsigned get_owner_id() const { return m_owner->get_id(); }
        void inc_class_size(unsigned n) { m_class_size += n; }
        void dec_class_size(unsigned n) { m_class_size -= n; }

        void reverse_justification();
        bool reaches(enode* n) const;

        enode* const* begin_parents() const { return m_parents.begin(); }
        enode* const* end_parents() const { return m_parents.end(); }

        void invariant();
        bool congruent(enode* n) const;
    };

    class enode_args {
        enode& n;
    public:
        enode_args(enode& _n):n(_n) {}
        enode_args(enode* _n):n(*_n) {}
        enode* const* begin() const { return n.m_args; }
        enode* const* end()   const { return n.m_args + n.num_args(); }
    };

    class enode_parents {
        enode const& n;
    public:
        enode_parents(enode const& _n):n(_n) {}
        enode_parents(enode const* _n):n(*_n) {}
        enode* const* begin() const { return n.m_parents.begin(); }
        enode* const* end()   const { return n.m_parents.end(); }
    };

    class enode_class {
        enode & n;
    public:
        class iterator {
            enode* m_first;
            enode* m_last;
        public:
            iterator(enode* n, enode* m): m_first(n), m_last(m) {} 
            enode* operator*() { return m_first; }
            iterator& operator++() { if (!m_last) m_last = m_first; m_first = m_first->m_next; return *this; }
            iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
            bool operator==(iterator const& other) const { return m_last == other.m_last && m_first == other.m_first; }
            bool operator!=(iterator const& other) const { return !(*this == other); }            
        };
        enode_class(enode & _n):n(_n) {}
        enode_class(enode * _n):n(*_n) {}
        iterator begin() const { return iterator(&n, nullptr); }
        iterator end() const { return iterator(&n, &n); }
    };
}
