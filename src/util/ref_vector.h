/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ref_vector.h

Abstract:

    Vector of smart pointers.

Author:

    Leonardo de Moura (leonardo) 2008-01-04.

Revision History:

--*/
#ifndef REF_VECTOR_H_
#define REF_VECTOR_H_

#include"vector.h"
#include"obj_ref.h"

/**
   \brief Vector of smart pointers.
   Ref must provided the methods
   - void dec_ref(T * obj)
   - void inc_ref(T * obj)
*/
template<typename T, typename Ref>
class ref_vector_core : public Ref {
protected:
    ptr_vector<T> m_nodes;
    
    void inc_ref(T * o) { Ref::inc_ref(o); }
    void dec_ref(T * o) { Ref::dec_ref(o); }

    void dec_range_ref(T * const * begin, T * const * end) {
        for (T * const * it = begin; it < end; ++it)
            dec_ref(*it);
    }

public:
    typedef T * data;

    ref_vector_core(Ref const & r = Ref()):Ref(r) {}
    
    ~ref_vector_core() {
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
        m_nodes.resize(sz, 0);
    }

    void resize(unsigned sz, T * d) {
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
        m_nodes.resize(sz, 0);
    }

    void shrink(unsigned sz) {
        SASSERT(sz <= m_nodes.size());
        dec_range_ref(m_nodes.begin() + sz, m_nodes.end());
        m_nodes.shrink(sz);
    }

    ref_vector_core& push_back(T * n) {
        inc_ref(n);
        m_nodes.push_back(n);
        return *this;
    }

    void pop_back() {
        SASSERT(!m_nodes.empty());
        T * n = m_nodes.back();
        m_nodes.pop_back();
        dec_ref(n);
    }

    T * back() const { return m_nodes.back(); }

    unsigned size() const { return m_nodes.size(); }

    bool empty() const { return m_nodes.empty(); }

    T * get(unsigned idx) const { return m_nodes[idx]; }

    T * get(unsigned idx, T * d) const { return m_nodes.get(idx, d); }

    T * const * c_ptr() const { return m_nodes.begin(); }

    typedef T* const* iterator;

    T ** c_ptr() { return m_nodes.begin(); }

    iterator begin() const { return m_nodes.begin(); }
    iterator end() const { return begin() + size(); }

    void set(unsigned idx, T * n) {
        inc_ref(n);
        dec_ref(m_nodes[idx]);
        m_nodes[idx] = n;
    }

    void erase(unsigned idx) {
        T * curr = m_nodes[idx];
        m_nodes.erase(m_nodes.begin() + idx);
        dec_ref(curr);
    }

    void erase(T * elem) {
        unsigned sz = size();
        for (unsigned idx = 0; idx < sz; idx++) {
            if (m_nodes[idx] == elem) {
                erase(idx);
                return;
            }
        }
    }

    bool contains(T * elem) const {
        unsigned sz = size();
        for (unsigned idx = 0; idx < sz; idx++)
            if (m_nodes[idx] == elem)
                return true;
        return false;
    }
    
    T * operator[](unsigned idx) const {
        return m_nodes[idx];
    }

    void append(ref_vector_core const & other) {
        for (unsigned i = 0; i < other.size(); ++i)
            push_back(other[i]);
    }

    void append(unsigned sz, T * const * data) {
        for(unsigned i = 0; i < sz; ++i)
            push_back(data[i]);
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

template<typename T, typename TManager>
class ref_manager_wrapper {
protected:
    TManager & m_manager;
public:
    ref_manager_wrapper(TManager & m):m_manager(m) {}
    void inc_ref(T * n) { m_manager.inc_ref(n); }
    void dec_ref(T * n) { m_manager.dec_ref(n); }
};


/**
   \brief Vector of smart pointers.
   TManager must provide the functions:
   - void dec_ref(T * obj)
   - void inc_ref(T * obj)
*/
template<typename T, typename TManager>
class ref_vector : public ref_vector_core<T, ref_manager_wrapper<T, TManager> > {
    typedef ref_vector_core<T, ref_manager_wrapper<T, TManager> > super;
public:
    ref_vector(TManager & m):
        super(ref_manager_wrapper<T, TManager>(m)) {
    }
    
    ref_vector(ref_vector const & other): 
        super(ref_manager_wrapper<T, TManager>(other.m_manager)) {
        this->append(other);
    }

    ref_vector(TManager & m, unsigned sz, T * const * data):
        super(ref_manager_wrapper<T, TManager>(m)) {
        this->append(sz, data);
    }
    
    TManager & get_manager() const {
        return this->m_manager;
    }
    
    TManager & m() const { 
        return get_manager();
    }

    void swap(ref_vector & other) {
        SASSERT(&(this->m_manager) == &(other.m_manager));
        this->m_nodes.swap(other.m_nodes);
    }
    
    class element_ref {
        T * &       m_ref;
        TManager &  m_manager;
    public:
        element_ref(T * & ref, TManager & m):
            m_ref(ref),
            m_manager(m) {
        }

        element_ref & operator=(T * n) {
            SASSERT(n);
            m_manager.inc_ref(n);
            m_manager.dec_ref(m_ref);
            m_ref = n;
            return *this;
        }

        element_ref & operator=(element_ref& n) {
            *this = n.get();
            return *this;
        }

        T * get() const {
            return m_ref;
        }

        T * operator->() const { 
            return m_ref; 
        }
        
        T const & operator*() const {
            SASSERT(m_ref);
            return *m_ref;
        }
        
        bool operator==(T * n) const {
            return m_ref == n;
        }
    };

    T * operator[](unsigned idx) const { return super::operator[](idx); }

    element_ref operator[](unsigned idx) {
        return element_ref(this->m_nodes[idx], this->m_manager);
    }

    void set(unsigned idx, T * n) { super::set(idx, n); }

    // enable abuse:
    ref_vector & set(ref_vector const& other) {
        if (this != &other) {
            this->reset();
            this->append(other);
        }
        return *this;
    }
    
private:
    // prevent abuse:
    ref_vector & operator=(ref_vector const & other);
};

template<typename T>
class ref_unmanaged_wrapper {
public:
    static void inc_ref(T * n) { if (n) n->inc_ref(); }
    static void dec_ref(T * n) { if (n) n->dec_ref(); }
};

/**
   \brief Vector of unmanaged references.
*/
template<typename T> 
class sref_vector : public ref_vector_core<T, ref_unmanaged_wrapper<T> > {
};

/**
   \brief Hash utilities on ref_vector pointers.
*/

template<typename T, typename TM>
struct ref_vector_ptr_hash {

    typedef ref_vector<T,TM> RefV;

    struct hash_proc {
        unsigned operator()(RefV* v, unsigned idx) const {
            return (*v)[idx]->get_id();
        }
    };

    unsigned operator()(RefV* v) const {
        if (!v) {
            return 0;
        }
        unsigned sz = v->size();
        if (sz == 0) {
            return 0;
        }
        return get_composite_hash(v, sz, default_kind_hash_proc<RefV*>(), hash_proc());
    }
};

template<typename T, typename TM>
struct ref_vector_ptr_eq {
    typedef ref_vector<T, TM> RefV;

    bool operator()(RefV* v1, RefV* v2) const {
        if (!v1 && !v2) {
            return true;
        }
        if ((!v1 && v2) || (v1 && !v2)) {
            return false;
        }
        if (v1->size() != v2->size()) {
            return false;
        }
        for (unsigned i = 0; i < v1->size(); ++i) {
            if ((*v1)[i].get() != (*v2)[i].get()) {
                return false;
            }
        }
        return true;
    }
};


#endif /* REF_VECTOR_H_ */
