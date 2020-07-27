/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dependency.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-12-10.

Revision History:

--*/
#pragma once

#include "util/vector.h"
#include "util/region.h"

template<typename C>
class dependency_manager {
public:
    typedef typename C::value         value;
    typedef typename C::value_manager value_manager;
    typedef typename C::allocator     allocator;

    class dependency { 
        unsigned  m_ref_count:30;
        unsigned  m_mark:1;
        unsigned  m_leaf:1;
        friend class dependency_manager;
        dependency(bool leaf):
            m_ref_count(0),
            m_mark(false),
            m_leaf(leaf) {
        }
        bool is_marked() const { return m_mark == 1; }
        void mark() { m_mark = true; }
        void unmark() { m_mark = false; }
    public:
        unsigned get_ref_count() const { return m_ref_count; }
        bool is_leaf() const { return m_leaf == 1; }
    };

private:
    struct join : public dependency {
        dependency *    m_children[2];
        join(dependency * d1, dependency * d2):
            dependency(false) {
            m_children[0] = d1;
            m_children[1] = d2;
        }
    };
    
    struct leaf : public dependency {
        value     m_value;
        leaf(value const & v):
            dependency(true),
            m_value(v) {
        }
    };

    static join * to_join(dependency * d) { SASSERT(!d->is_leaf()); return static_cast<join*>(d); }
    static leaf * to_leaf(dependency * d) { SASSERT(d->is_leaf()); return static_cast<leaf*>(d); }

    value_manager &         m_vmanager;
    allocator  &            m_allocator;
    ptr_vector<dependency>  m_todo;

    void inc_ref(value const & v) {
        if (C::ref_count)
            m_vmanager.inc_ref(v);
    }

    void dec_ref(value const & v) {
        if (C::ref_count)
            m_vmanager.dec_ref(v);
    }

    void del(dependency * d) {
        SASSERT(d);
        m_todo.push_back(d);
        while (!m_todo.empty()) {
            d = m_todo.back();
            m_todo.pop_back();
            if (d->is_leaf()) {
                dec_ref(to_leaf(d)->m_value);
                to_leaf(d)->~leaf();
                m_allocator.deallocate(sizeof(leaf), to_leaf(d));
            }
            else {
                for (unsigned i = 0; i < 2; i++) {
                    dependency * c = to_join(d)->m_children[i];
                    SASSERT(c->m_ref_count > 0);
                    c->m_ref_count--;
                    if (c->m_ref_count == 0)
                        m_todo.push_back(c);
                }
                to_join(d)->~join();
                m_allocator.deallocate(sizeof(join), to_join(d));
            }
        }
    }

    void unmark_todo() {
        typename ptr_vector<dependency>::iterator it  = m_todo.begin();
        typename ptr_vector<dependency>::iterator end = m_todo.end();
        for (; it != end; ++it) {
            (*it)->unmark();
        }
        m_todo.reset();
    }

public:
    
    dependency_manager(value_manager & m, allocator & a):
        m_vmanager(m),
        m_allocator(a) {
    }

    void inc_ref(dependency * d) {
        if (d)
            d->m_ref_count++;
    }
    
    void dec_ref(dependency * d) {
        if (d) {
            SASSERT(d->m_ref_count > 0);
            d->m_ref_count--;
            if (d->m_ref_count == 0)
                del(d);
        }
    }
        
    dependency * mk_empty() {
        return nullptr;
    }

    dependency * mk_leaf(value const & v) {
        void * mem = m_allocator.allocate(sizeof(leaf));
        inc_ref(v);
        return new (mem) leaf(v);
    }
    
    dependency * mk_join(dependency * d1, dependency * d2) {
        if (d1 == nullptr) {
            return d2;
        }
        else if (d2 == nullptr) {
            return d1; 
        }
        else if (d1 == d2) {
            return d1;
        }
        else {
            void * mem = m_allocator.allocate(sizeof(join));
            inc_ref(d1); inc_ref(d2);
            return new (mem) join(d1, d2);
        }
    }

    bool contains(dependency * d, value const & v) {
        if (d) {
            m_todo.reset();
            d->mark();
            m_todo.push_back(d);
            unsigned qhead = 0;
            while (qhead < m_todo.size()) {
                d = m_todo[qhead];
                qhead++;
                if (d->is_leaf()) {
                    if (to_leaf(d)->m_value == v) {
                        unmark_todo();
                        return true;
                    }
                }
                else {
                    for (unsigned i = 0; i < 2; i++) {
                        dependency * child = to_join(d)->m_children[i];
                        if (!child->is_marked()) {
                            m_todo.push_back(child);
                            child->mark();
                        }
                    }
                }
            }
            unmark_todo();
        }
        return false;
    }

    void linearize(dependency * d, vector<value, false> & vs) {
        if (d) {
            m_todo.reset();
            d->mark();
            m_todo.push_back(d);
            unsigned qhead = 0;
            while (qhead < m_todo.size()) {
                d = m_todo[qhead];
                qhead++;
                if (d->is_leaf()) {
                    vs.push_back(to_leaf(d)->m_value);
                }
                else {
                    for (unsigned i = 0; i < 2; i++) {
                        dependency * child = to_join(d)->m_children[i];
                        if (!child->is_marked()) {
                            m_todo.push_back(child);
                            child->mark();
                        }
                    }
                }
            }
            unmark_todo();
        }
    }
};

/**
   \brief Version of the dependency_manager where 
   memory management is scoped (i.e., reference counting is ignored),
   and push_scope/pop_scope are used instead. 

   Value must be a primitive type such as an integer or pointer.
*/
template<typename Value>
class scoped_dependency_manager {

    class config {
    public:
        static const bool ref_count        = true;

        typedef Value value;

        class value_manager {
        public:
            void inc_ref(value const & v) {
            }

            void dec_ref(value const & v) {
            }
        };

        class allocator {
            region   m_region;
        public:
            void * allocate(size_t sz) {
                return m_region.allocate(sz);
            }
            
            void deallocate(size_t sz, void * mem) {
            }
            
            void push_scope() { 
                m_region.push_scope(); 
            }
            
            void pop_scope(unsigned num) {
                m_region.pop_scope(num);
            }
            
            void reset() {
                m_region.reset();
            }
        };
    };

    typedef dependency_manager<config>       dep_manager;
public:
    typedef typename dep_manager::dependency dependency;
    typedef Value value;

private:
    typename config::value_manager m_vmanager;
    typename config::allocator     m_allocator;
    dep_manager                    m_dep_manager;

public:
    scoped_dependency_manager():
        m_dep_manager(m_vmanager, m_allocator) {
    }

    dependency * mk_empty() {
        return m_dep_manager.mk_empty();
    }
    
    dependency * mk_leaf(value const & v) {
        return m_dep_manager.mk_leaf(v); 
    }
    
    dependency * mk_join(dependency * d1, dependency * d2) {
        return m_dep_manager.mk_join(d1, d2);
    }

    bool contains(dependency * d, value const & v) {
        return m_dep_manager.contains(d, v); 
    }

    void linearize(dependency * d, vector<value, false> & vs) {
        return m_dep_manager.linearize(d, vs);
    }    
    
    void reset() {
        m_allocator.reset();
    }
    
    void push_scope() {
        m_allocator.push_scope();
    }

    void pop_scope(unsigned num_scopes) {
        m_allocator.pop_scope(num_scopes);
    }
};

// Implement old dependency manager used by interval and groebner 
typedef scoped_dependency_manager<void*>             v_dependency_manager;
typedef scoped_dependency_manager<void*>::dependency v_dependency;
typedef scoped_dependency_manager<unsigned>             u_dependency_manager;
typedef scoped_dependency_manager<unsigned>::dependency u_dependency;


