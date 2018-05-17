/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    vector.h

Abstract:
    Dynamic array implementation. 
    Remarks:

    - Empty arrays consume only sizeof(T *) bytes.

    - There is the option of disabling the destructor invocation for elements stored in the vector.
    This is useful for vectors of int.

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

--*/
#ifndef VECTOR_H_
#define VECTOR_H_

#include "util/debug.h"
#include<algorithm>
#include<type_traits>
#include<memory.h>
#include "util/memory_manager.h"
#include "util/hash.h"
#include "util/z3_exception.h"

// disable warning for constant 'if' expressions.
// these are used heavily in templates.
#ifdef _MSC_VER
#pragma warning(disable:4127)
#endif

template<typename T, bool CallDestructors=true, typename SZ = unsigned>
class vector {
#define SIZE_IDX     -1
#define CAPACITY_IDX -2
    T * m_data;

    void destroy_elements() {
        iterator it = begin();
        iterator e  = end();
        for (; it != e; ++it) {
            it->~T();
        }
    }

    void free_memory() { 
        memory::deallocate(reinterpret_cast<char*>(reinterpret_cast<SZ*>(m_data) - 2));
    }

    void expand_vector() {
        if (m_data == nullptr) {
            SZ capacity = 2;
            SZ * mem    = reinterpret_cast<SZ*>(memory::allocate(sizeof(T) * capacity + sizeof(SZ) * 2));
            *mem              = capacity; 
            mem++;
            *mem              = 0;        
            mem++;
            m_data            = reinterpret_cast<T *>(mem);
        }
        else {
            SASSERT(capacity() > 0);
            SZ old_capacity = reinterpret_cast<SZ *>(m_data)[CAPACITY_IDX];
            SZ old_capacity_T = sizeof(T) * old_capacity + sizeof(SZ) * 2;
            SZ new_capacity = (3 * old_capacity + 1) >> 1;
            SZ new_capacity_T = sizeof(T) * new_capacity + sizeof(SZ) * 2;
            if (new_capacity <= old_capacity || new_capacity_T <= old_capacity_T) {
                throw default_exception("Overflow encountered when expanding vector");
            }
            SZ *mem, *old_mem = reinterpret_cast<SZ*>(m_data) - 2;
#if defined(__GNUC__) && !defined(__clang__) && __GNUC__ < 5
            if (__has_trivial_copy(T)) {
#else
            if (std::is_trivially_copyable<T>::value) {
#endif
                mem = (SZ*)memory::reallocate(old_mem, new_capacity_T);
                m_data = reinterpret_cast<T *>(mem + 2);
            } else {
                mem = (SZ*)memory::allocate(new_capacity_T);
                auto old_data = m_data;
                auto old_size = size();
                mem[1] = old_size;
                m_data  = reinterpret_cast<T *>(mem + 2);
                for (unsigned i = 0; i < old_size; ++i) {
                    new (&m_data[i]) T(std::move(old_data[i]));
                    old_data[i].~T();
                }
                memory::deallocate(old_mem);
            }
            *mem = new_capacity;
        }
    }

    void copy_core(vector const & source) {
        SZ size      = source.size();
        SZ capacity  = source.capacity();
        SZ * mem     = reinterpret_cast<SZ*>(memory::allocate(sizeof(T) * capacity + sizeof(SZ) * 2));
        *mem = capacity; 
        mem++;
        *mem = size; 
        mem++;
        m_data             = reinterpret_cast<T *>(mem);
        const_iterator it  = source.begin();
        iterator it2       = begin();
        SASSERT(it2 == m_data);
        const_iterator e   = source.end();
        for (; it != e; ++it, ++it2) {
            new (it2) T(*it); 
        }
    }

    void destroy() {
        if (m_data) { 
            if (CallDestructors) {
                destroy_elements(); 
            }
            free_memory(); 
        } 
    }

public:
    typedef T data;
    typedef T * iterator;
    typedef const T * const_iterator;

    vector():
        m_data(nullptr) {
    }

    vector(SZ s) {
        if (s == 0) {
            m_data = nullptr;
            return;
        }
        SZ * mem = reinterpret_cast<SZ*>(memory::allocate(sizeof(T) * s + sizeof(SZ) * 2));
        *mem = s; 
        mem++;
        *mem = s; 
        mem++;
        m_data = reinterpret_cast<T *>(mem);
        // initialize elements
        iterator it = begin();
        iterator e  = end();
        for (; it != e; ++it) {
            new (it) T(); 
        }
    }

    vector(SZ s, T const & elem):
        m_data(nullptr) {
        resize(s, elem);
    }

    vector(vector const & source):
        m_data(nullptr) {
        if (source.m_data) {
            copy_core(source);
        }
        SASSERT(size() == source.size());
    }

    vector(vector&& other) : m_data(nullptr) {
        std::swap(m_data, other.m_data);
    }

    vector(SZ s, T const * data):
        m_data(nullptr) {
        for (SZ i = 0; i < s; i++) {
            push_back(data[i]);
        }
    }

 
    ~vector() { 
        destroy();
    } 

    void finalize() {
        destroy();
        m_data = nullptr;
    }

    bool operator==(vector const & other) const {
        if (this == &other) {
            return true;
        }
        if (size() != other.size())
            return false;
        for (unsigned i = 0; i < size(); i++) {
            if ((*this)[i] != other[i])
                return false;
        }
        return true;
    }

    bool operator!=(vector const & other) const {
        return !(*this == other);
    }

    
    vector & operator=(vector const & source) {
        if (this == &source) {
            return *this;
        }
        destroy();
        if (source.m_data) {
            copy_core(source);
        }
        else {
            m_data = nullptr;
        }
        return *this;
    }

    vector & operator=(vector && source) {
        if (this == &source) {
            return *this;
        }
        destroy();
        m_data = nullptr;
        std::swap(m_data, source.m_data);
        return *this;
    }

    void reset() { 
        if (m_data) {
            if (CallDestructors) {
                destroy_elements();
            }
            reinterpret_cast<SZ *>(m_data)[SIZE_IDX] = 0;
        }
    }

    void clear() { reset(); }

    bool empty() const { 
        return m_data == nullptr || reinterpret_cast<SZ *>(m_data)[SIZE_IDX] == 0;
    }

    SZ size() const { 
        if (m_data == nullptr) {
            return 0;  
        }
        return reinterpret_cast<SZ *>(m_data)[SIZE_IDX]; 
    }

    SZ capacity() const { 
        if (m_data == nullptr) {
            return 0;
        }
        return reinterpret_cast<SZ *>(m_data)[CAPACITY_IDX]; 
    }

    iterator begin() { 
        return m_data; 
    }

    iterator end() { 
        return m_data + size();
    }

    const_iterator begin() const { 
        return m_data; 
    }

    const_iterator end() const { 
        return m_data + size(); 
    }

    class reverse_iterator {
        T* v;
    public:
        reverse_iterator(T* v):v(v) {}
        
        T operator*() { return *v; }
        reverse_iterator operator++(int) {
            reverse_iterator tmp = *this;
            --v;
            return tmp;
        }
        reverse_iterator& operator++() {
            --v;
            return *this;
        }

        bool operator==(reverse_iterator const& other) const {
            return other.v == v;
        }
        bool operator!=(reverse_iterator const& other) const {
            return other.v != v;
        }
    };

    reverse_iterator rbegin() { return reverse_iterator(end() - 1); }
    reverse_iterator rend() { return reverse_iterator(begin() - 1); }

    void set_end(iterator it) {
        if (m_data) {
            SZ new_sz = static_cast<SZ>(it - m_data);
            if (CallDestructors) {
                iterator e = end();
                for(; it != e; ++it) {
                    it->~T();
                }
            }
            reinterpret_cast<SZ *>(m_data)[SIZE_IDX] = new_sz;
        }
        else {
            SASSERT(it == 0);
        }
    }

    T & operator[](SZ idx) { 
        SASSERT(idx < size()); 
        return m_data[idx]; 
    }

    T const & operator[](SZ idx) const { 
        SASSERT(idx < size()); 
        return m_data[idx];
    }

    T & get(SZ idx) { 
        SASSERT(idx < size()); 
        return m_data[idx]; 
    }

    T const & get(SZ idx) const { 
        SASSERT(idx < size()); 
        return m_data[idx];
    }

    void set(SZ idx, T const & val) { 
        SASSERT(idx < size()); 
        m_data[idx] = val;
    }

    void set(SZ idx, T && val) {
        SASSERT(idx < size());
        m_data[idx] = std::move(val);
    }

    T & back() { 
        SASSERT(!empty()); 
        return operator[](size() - 1); 
    }

    T const & back() const { 
        SASSERT(!empty()); 
        return operator[](size() - 1); 
    }

    void pop_back() { 
        SASSERT(!empty()); 
        if (CallDestructors) {
            back().~T(); 
        }
        reinterpret_cast<SZ *>(m_data)[SIZE_IDX]--; 
    }

    void push_back(T const & elem) {
        if (m_data == nullptr || reinterpret_cast<SZ *>(m_data)[SIZE_IDX] == reinterpret_cast<SZ *>(m_data)[CAPACITY_IDX]) {
            expand_vector();
        }
        new (m_data + reinterpret_cast<SZ *>(m_data)[SIZE_IDX]) T(elem); 
        reinterpret_cast<SZ *>(m_data)[SIZE_IDX]++;
    }

    void push_back(T && elem) {
        if (m_data == nullptr || reinterpret_cast<SZ *>(m_data)[SIZE_IDX] == reinterpret_cast<SZ *>(m_data)[CAPACITY_IDX]) {
            expand_vector();
        }
        new (m_data + reinterpret_cast<SZ *>(m_data)[SIZE_IDX]) T(std::move(elem));
        reinterpret_cast<SZ *>(m_data)[SIZE_IDX]++;
    }

    void insert(T const & elem) {
        push_back(elem);
    }

    void erase(iterator pos) {
        SASSERT(pos >= begin() && pos < end());
        iterator prev = pos;
        ++pos;
        iterator e    = end();
        for(; pos != e; ++pos, ++prev) {
            *prev = *pos;
        }
        reinterpret_cast<SZ *>(m_data)[SIZE_IDX]--;
    }

    void erase(T const & elem) {
        iterator it = std::find(begin(), end(), elem);
        if (it != end()) {
            erase(it);
        }
    }

    void shrink(SZ s) {
        if (m_data) {
            SASSERT(s <= reinterpret_cast<SZ *>(m_data)[SIZE_IDX]);
            if (CallDestructors) {
                iterator it = m_data + s;
                iterator e  = end();
                for(; it != e; ++it) {
                    it->~T();
                }
            }
            reinterpret_cast<SZ *>(m_data)[SIZE_IDX] = s;
        }
        else {
            SASSERT(s == 0);
        }
    }

    template<typename Args>
    void resize(SZ s, Args args...) {
        SZ sz = size();
        if (s <= sz) { shrink(s); return; }
        while (s > capacity()) {
            expand_vector();
        }
        SASSERT(m_data != 0);
        reinterpret_cast<SZ *>(m_data)[SIZE_IDX] = s;
        iterator it  = m_data + sz;
        iterator end = m_data + s;
        for (; it != end; ++it) {
            new (it) T(std::forward<Args>(args));
        }
    }

    void resize(SZ s) {
        SZ sz = size();
        if (s <= sz) { shrink(s); return; }
        while (s > capacity()) {
            expand_vector();
        }
        SASSERT(m_data != 0);
        reinterpret_cast<SZ *>(m_data)[SIZE_IDX] = s;
        iterator it  = m_data + sz;
        iterator end = m_data + s;
        for (; it != end; ++it) {
            new (it) T();
        }
    }

    void append(vector<T, CallDestructors> const & other) {
        for(SZ i = 0; i < other.size(); ++i) {
            push_back(other[i]);
        }
    }

    void append(SZ sz, T const * data) {
        for(SZ i = 0; i < sz; ++i) {
            push_back(data[i]);
        }
    }

    T * c_ptr() const {
        return m_data;
    }

    void swap(vector & other) {
        std::swap(m_data, other.m_data);
    }

    void reverse() {
        SZ sz = size();
        for (SZ i = 0; i < sz/2; ++i) {
            std::swap(m_data[i], m_data[sz-i-1]);
        }
    }

    void fill(T const & elem) {
        iterator i = begin();
        iterator e = end();
        for (; i != e; ++i) {
            *i = elem;
        }
    }

    void fill(unsigned sz, T const & elem) {
        resize(sz);
        fill(elem);
    }

    bool contains(T const & elem) const {
        const_iterator it  = begin();
        const_iterator e = end();
        for (; it != e; ++it) {
            if (*it == elem) {
                return true;
            }
        }
        return false;
    }

    // set pos idx with elem. If idx >= size, then expand using default.
    void setx(SZ idx, T const & elem, T const & d) {
        if (idx >= size()) {
            resize(idx+1, d);
        }
        m_data[idx] = elem;
    }

    // return element at position idx, if idx >= size, then return default
    T const & get(SZ idx, T const & d) const {
        if (idx >= size()) {
            return d;
        }
        return m_data[idx];
    }

    void reserve(SZ s, T const & d) {
        if (s > size())
            resize(s, d);
    }

    void reserve(SZ s) {
        if (s > size())
            resize(s);
    }
};

template<typename T>
class ptr_vector : public vector<T *, false> {
public:
    ptr_vector():vector<T *, false>() {}
    ptr_vector(unsigned s):vector<T *, false>(s) {}
    ptr_vector(unsigned s, T * elem):vector<T *, false>(s, elem) {}
    ptr_vector(ptr_vector const & source):vector<T *, false>(source) {}
    ptr_vector(ptr_vector && other) : vector<T*, false>(std::move(other)) {}
    ptr_vector(unsigned s, T * const * data):vector<T *, false>(s, const_cast<T**>(data)) {}
    ptr_vector & operator=(ptr_vector const & source) {
        vector<T *, false>::operator=(source);
        return *this;
    }
};

template<typename T, typename SZ = unsigned>
class svector : public vector<T, false, SZ> {
public:
    svector():vector<T, false, SZ>() {}
    svector(SZ s):vector<T, false, SZ>(s) {}
    svector(SZ s, T const & elem):vector<T, false, SZ>(s, elem) {}
    svector(svector const & source):vector<T, false, SZ>(source) {}
    svector(svector && other) : vector<T, false, SZ>(std::move(other)) {}
    svector(SZ s, T const * data):vector<T, false, SZ>(s, data) {}
    svector & operator=(svector const & source) {
        vector<T, false, SZ>::operator=(source);
        return *this;
    }
};

typedef svector<int> int_vector;
typedef svector<unsigned> unsigned_vector;
typedef svector<char> char_vector;
typedef svector<signed char> signed_char_vector;
typedef svector<double> double_vector;

inline std::ostream& operator<<(std::ostream& out, unsigned_vector const& v) {
    for (unsigned u : v) out << u << " ";
    return out;
}

template<typename Hash, typename Vec>
struct vector_hash_tpl {
    Hash m_hash;
    typedef Vec data;

    unsigned operator()(data const& v, unsigned idx) const { return m_hash(v[idx]); }

    vector_hash_tpl(Hash const& h = Hash()):m_hash(h) {}

    unsigned operator()(data const& v) const {
        if (v.empty()) {
            return 778;
        }
        return get_composite_hash<data, default_kind_hash_proc<data>, vector_hash_tpl>(v, v.size());
    }
};

template<typename Hash>
struct vector_hash : public vector_hash_tpl<Hash, vector<typename Hash::data> > {};

template<typename Hash>
struct svector_hash : public vector_hash_tpl<Hash, svector<typename Hash::data> > {};

#endif /* VECTOR_H_ */
