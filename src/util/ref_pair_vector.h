/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ref_pair_vector.h

Abstract:

    Vector of pairs of smart pointers.

Author:

    Leonardo de Moura (leonardo) 2008-01-04.

Revision History:

--*/
#pragma once

#include "util/vector.h"
#include "util/obj_ref.h"
#include "util/ref_vector.h"

/**
   \brief Vector of smart pointers.
   Ref must provided the methods
   - void dec_ref(T * obj)
   - void inc_ref(T * obj)
*/
template<typename T, typename Ref>
class ref_pair_vector_core : public Ref {
protected:
    svector<std::pair<T*,T*>> m_nodes;
    typedef std::pair<T*,T*> elem_t;
    
    void inc_ref(T * o) { Ref::inc_ref(o); }
    void dec_ref(T * o) { Ref::dec_ref(o); }
    void inc_ref(elem_t const& p) { inc_ref(p.first); inc_ref(p.second); }
    void dec_ref(elem_t const& p) { dec_ref(p.first); dec_ref(p.second); }

    void dec_range_ref(elem_t const * begin, elem_t const * end) {
        for (auto it = begin; it < end; ++it)
            dec_ref(*it);
    }

public:
    typedef T * data_t;

    ref_pair_vector_core(Ref const & r = Ref()):Ref(r) {}

    ~ref_pair_vector_core() {
        dec_range_ref(m_nodes.begin(), m_nodes.end());
    }

    void reset() {
        dec_range_ref(m_nodes.begin(), m_nodes.end());
        m_nodes.reset();
    }

    void finalize() {
        dec_range_ref(m_nodes.begin(), m_nodes.end());
        m_nodes.finalize();
    }

    void resize(unsigned sz) {
        if (sz < m_nodes.size())
            dec_range_ref(m_nodes.begin() + sz, m_nodes.end());
        m_nodes.resize(sz);
    }

    void resize(unsigned sz, elem_t d) {
        if (sz < m_nodes.size()) {
            dec_range_ref(m_nodes.begin() + sz, m_nodes.end());
            m_nodes.shrink(sz); 
        }
        else {
            for (unsigned i = m_nodes.size(); i < sz; i++)
                push_back(d);
        }
    }

    void reserve(unsigned sz) {
        if (sz <= m_nodes.size())
            return;
        m_nodes.resize(sz);
    }

    void shrink(unsigned sz) {
        SASSERT(sz <= m_nodes.size());
        dec_range_ref(m_nodes.begin() + sz, m_nodes.end());
        m_nodes.shrink(sz);
    }

    ref_pair_vector_core& push_back(elem_t n) {
        inc_ref(n);
        m_nodes.push_back(n);
        return *this;
    }

    ref_pair_vector_core& push_back(T * a, T* b) {
        inc_ref(a);
        inc_ref(b);
        m_nodes.push_back(elem_t(a, b));
        return *this;
    }

    template <typename M>
    ref_pair_vector_core& push_back(obj_ref<T,M> && n) {
        m_nodes.push_back(n.get());
        n.steal();
        return *this;
    }

    void pop_back() {
        SASSERT(!m_nodes.empty());
        auto n = m_nodes.back();
        m_nodes.pop_back();
        dec_ref(n);
    }

    elem_t const& back() const { return m_nodes.back(); }

    unsigned size() const { return m_nodes.size(); }

    bool empty() const { return m_nodes.empty(); }

    elem_t const& get(unsigned idx) const { return m_nodes[idx]; }

    elem_t const * data() const { return m_nodes.begin(); }
    
    typedef elem_t const* iterator;

    iterator begin() const { return m_nodes.begin(); }
    iterator end() const { return begin() + size(); }
    
    elem_t operator[](unsigned idx) const {
        return m_nodes[idx];
    }

    void append(ref_pair_vector_core const & other) {
        for (unsigned i = 0; i < other.size(); ++i)
            push_back(other[i]);
    }

    void swap(unsigned idx1, unsigned idx2) {
        std::swap(m_nodes[idx1], m_nodes[idx2]);
    }

    void reverse() {
        unsigned sz = size();
        for (unsigned i = 0; i < sz/2; ++i) {
            std::swap(m_nodes[i], m_nodes[sz-i-1]);
        }
    }
};



/**
   \brief Vector of smart pointers.
   TManager must provide the functions:
   - void dec_ref(T * obj)
   - void inc_ref(T * obj)
*/
template<typename T, typename TManager>
class ref_pair_vector : public ref_pair_vector_core<T, ref_manager_wrapper<T, TManager> > {
    typedef ref_pair_vector_core<T, ref_manager_wrapper<T, TManager> > super;

public:
    typedef std::pair<T*,T*> elem_t;

    ref_pair_vector(TManager & m):
        super(ref_manager_wrapper<T, TManager>(m)) {
    }
    
    ref_pair_vector(ref_pair_vector const & other): 
        super(ref_manager_wrapper<T, TManager>(other.m_manager)) {
        this->append(other);
    }

    ref_pair_vector(ref_pair_vector && other) : super(std::move(other)) {}

    ref_pair_vector(TManager & m, unsigned sz, elem_t const * data):
        super(ref_manager_wrapper<T, TManager>(m)) {
        this->append(sz, data);
    }
    
    TManager & get_manager() const {
        return this->m_manager;
    }
    
    TManager & m() const { 
        return get_manager();
    }

    void swap(ref_pair_vector & other) {
        SASSERT(&(this->m_manager) == &(other.m_manager));
        this->m_nodes.swap(other.m_nodes);
    }
    
    class element_ref {
        elem_t &       m_ref;
        TManager &  m_manager;
    public:
        element_ref(elem_t & ref, TManager & m):
            m_ref(ref),
            m_manager(m) {
        }

        element_ref & operator=(elem_t n) {
            m_manager.inc_ref(n.first);
            m_manager.inc_ref(n.second);
            m_manager.dec_ref(m_ref.first);
            m_manager.dec_ref(m_ref.second);
            m_ref = n;
            return *this;
        }

        element_ref & operator=(element_ref& n) {
            *this = n.get();
            return *this;
        }

        template <typename W, typename M>
        element_ref & operator=(obj_ref<W,M> && n) {
            m_manager.dec_ref(m_ref);
            m_ref = n.steal();
            return *this;
        }

        elem_t get() const {
            return m_ref;
        }

        elem_t operator->() const { 
            return m_ref; 
        }
        
        T const & operator*() const {
            SASSERT(m_ref);
            return *m_ref;
        }
        
        bool operator==(elem_t n) const {
            return m_ref == n;
        }
    };

    elem_t operator[](unsigned idx) const { return super::operator[](idx); }

    element_ref operator[](unsigned idx) {
        return element_ref(this->m_nodes[idx], this->m_manager);
    }

    void set(unsigned idx, elem_t n) { super::set(idx, n); }
    
    // prevent abuse:
    ref_pair_vector & operator=(ref_pair_vector const & other) = delete;

    bool operator==(ref_pair_vector const& other) const {
        if (other.size() != this->size()) return false;
        for (unsigned i = this->size(); i-- > 0; ) {
            if (other[i] != (*this)[i]) return false;
        }
        return true;
    }

    bool operator!=(ref_pair_vector const& other) const {
        return !(*this == other);
    }


};



