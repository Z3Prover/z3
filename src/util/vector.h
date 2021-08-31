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
    Daniel Schemmel 2019-2-23

Revision History:


--*/
#pragma once

#include "util/debug.h"
#include <algorithm>
#include <functional>
#include <memory>
#include <type_traits>
#include "util/memory_manager.h"
#include "util/hash.h"
#include "util/z3_exception.h"

// disable warning for constant 'if' expressions.
// these are used heavily in templates.
#ifdef _MSC_VER
#pragma warning(disable:4127)
#endif


#if 0

// portability guide to std::vector.
// memory allocator should be based on memory_allocator<T>
// 
// template<typename T>
// struct memory_allocator {
//     typedef  T value_type;
//     etc (interface seems to change between C++17, 20 versions)
// };
//

// Note:
// polynomial.h contains declaration
// typedef svector<numeral>                        numeral_vector;
// it is crucial that it uses svector and not vector. The destructors on elements of the numeral vector are handled outside.
// Numeral gets instantiated by mpz and mpz does not support copy constructors.
// porting svector to vector is therefore blocked on the semantics of svector being 
// copy-constructor free.
// 

#include <vector>

template<typename T, bool CallDestructors=true, typename SZ = unsigned>
class vector : public std::vector<T> {
public:
    typedef T data_t;
    typedef typename std::vector<T>::iterator iterator;

    vector() {}
    vector(SZ s) {
        // TODO resize(s, T());
    }
    vector(SZ s, T const& e) {
        // TODO resize(s, e);
    }

    vector(SZ s, T const* e) {
        // TODO
    }

    void reset() { clear(); }
    void finalize() { clear(); }
    void reserve(SZ s, T const & d) {
        if (s > size())
            resize(s, d);
    }
    void reserve(SZ s) {
        
    }

    void setx(SZ idx, T const & elem, T const & d) {
        if (idx >= size()) 
            resize(idx+1, d);
        (*this)[idx] = elem;
    }

    T const & get(SZ idx, T const & d) const {
        if (idx >= size()) {
            return d;
        }
        return (*this)[idx];
    }

    void insert(T const & elem) {
        push_back(elem);
    }
    
    void erase(iterator pos) {
        // TODO
    }

    void erase(T const& e) {
        // TODO
    }
    void fill(T const & elem) {
        for (auto& e : *this)
            e = elem;
    }

    void fill(unsigned sz, T const & elem) {
        resize(sz);
        fill(elem);
    }

    void shrink(SZ s) {
        resize(s);
    }
    void reverse() {
        SZ sz = size();
        for (SZ i = 0; i < sz/2; ++i) {
            std::swap((*this)[i], (*this)[sz-i-1]);
        }
    }

    void append(vector<T, CallDestructors> const & other) {
        for(SZ i = 0; i < other.size(); ++i) {
            push_back(other[i]);
        }
    }

    void append(unsigned n,  T const* elems) {
        // TODO
    }

    bool contains(T const & elem) const {
        for (auto const& e : *this)
            if (e == elem)
                return true;
        return false;
    }

    
}; 


#else

template<typename T, bool CallDestructors=true, typename SZ = unsigned>
class vector {
#define SIZE_IDX     -1
#define CAPACITY_IDX -2
    T * m_data = nullptr;

    void destroy_elements() {
        std::destroy_n(m_data, size());
    }

    void free_memory() { 
        memory::deallocate(reinterpret_cast<char*>(reinterpret_cast<SZ*>(m_data) - 2));
    }

    void expand_vector() {
        // ensure that the data is sufficiently aligned
        // better fail to compile than produce code that may crash
        static_assert((sizeof(SZ) * 2) % alignof(T) == 0);

        if (m_data == nullptr) {
            SZ capacity = 2;
            SZ * mem    = reinterpret_cast<SZ*>(memory::allocate(sizeof(T) * capacity + sizeof(SZ) * 2));
            *mem        = capacity;
            mem++;
            *mem        = 0;
            mem++;
            m_data      = reinterpret_cast<T *>(mem);
        }
        else {
            static_assert(std::is_nothrow_move_constructible<T>::value);
            SASSERT(capacity() > 0);
            SZ old_capacity = reinterpret_cast<SZ *>(m_data)[CAPACITY_IDX];
            SZ old_capacity_T = sizeof(T) * old_capacity + sizeof(SZ) * 2;
            SZ new_capacity = (3 * old_capacity + 1) >> 1;
            SZ new_capacity_T = sizeof(T) * new_capacity + sizeof(SZ) * 2;
            if (new_capacity <= old_capacity || new_capacity_T <= old_capacity_T) {
                throw default_exception("Overflow encountered when expanding vector");
            }
            SZ *mem, *old_mem = reinterpret_cast<SZ*>(m_data) - 2;
            if (std::is_trivially_copyable<T>::value) {
                mem = (SZ*)memory::reallocate(old_mem, new_capacity_T);
                m_data = reinterpret_cast<T *>(mem + 2);
            } else {
                mem = (SZ*)memory::allocate(new_capacity_T);
                auto old_size = size();
                mem[1] = old_size;
                auto new_data = reinterpret_cast<T *>(mem + 2);
                std::uninitialized_move_n(m_data, old_size, new_data);
                destroy();
                m_data = new_data;
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
        m_data = reinterpret_cast<T *>(mem);
        std::uninitialized_copy(source.begin(), source.end(), begin());
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
    typedef T data_t;
    typedef T * iterator;
    typedef const T * const_iterator;

    vector() = default;

    vector(SZ s) {
        init(s);
    }

    void init(SZ s) {
        SASSERT(m_data == nullptr);
        if (s == 0) {
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

    vector(SZ s, T const & elem) {
        resize(s, elem);
    }

    vector(vector const & source) {
        if (source.m_data) {
            copy_core(source);
        }
        SASSERT(size() == source.size());
    }

    vector(vector&& other) noexcept {
        std::swap(m_data, other.m_data);
    }

    vector(SZ s, T const * data) {
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

    bool containsp(std::function<bool(T)>& predicate) const {
        for (auto const& t : *this)
            if (predicate(t)) 
                return true;
        return false;
    }

    /**
     * retain elements that satisfy predicate. aka 'where'.
     */
    vector filter_pure(std::function<bool(T)>& predicate) const {
        vector result;
        for (auto& t : *this)
            if (predicate(t)) 
                result.push_back(t);
        return result;
    }

    vector& filter_update(std::function<bool(T)>& predicate) {
        unsigned j = 0;
        for (auto& t : *this)
            if (predicate(t)) 
                set(j++, t);
        shrink(j);
        return *this;
    }

    /**
     * update elements using f, aka 'select'
     */
    template <typename S>
    vector<S> map_pure(std::function<S(T)>& f) const {
        vector<S> result;
        for (auto& t : *this)
            result.push_back(f(t));
        return result;
    }

    vector& map_update(std::function<T(T)>& f) {
        unsigned j = 0;
        for (auto& t : *this)
            set(j++, f(t));
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

    vector& push_back(T const & elem) {
        if (m_data == nullptr || reinterpret_cast<SZ *>(m_data)[SIZE_IDX] == reinterpret_cast<SZ *>(m_data)[CAPACITY_IDX]) {
            expand_vector();
        }
        new (m_data + reinterpret_cast<SZ *>(m_data)[SIZE_IDX]) T(elem); 
        reinterpret_cast<SZ *>(m_data)[SIZE_IDX]++;
        return *this;
    }

    template <typename ...Args> 
    vector& push_back(T const& elem, T elem2, Args ... elems) {
        push_back(elem);
        push_back(elem2, elems ...);
        return *this;
    }

    vector& push_back(T && elem) {
        if (m_data == nullptr || reinterpret_cast<SZ *>(m_data)[SIZE_IDX] == reinterpret_cast<SZ *>(m_data)[CAPACITY_IDX]) {
            expand_vector();
        }
        new (m_data + reinterpret_cast<SZ *>(m_data)[SIZE_IDX]) T(std::move(elem));
        reinterpret_cast<SZ *>(m_data)[SIZE_IDX]++;
        return *this;
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
            *prev = std::move(*pos);
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

    void init(vector<T, CallDestructors> const& other) {
        if (this == &other)
            return;
        reset();
        append(other);
    }

    void init(SZ sz, T const* data) {
        reset();
        append(sz, data);
    }

    T * data() const {
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

    struct scoped_stack {
        vector& s;
        unsigned sz;
        scoped_stack(vector& s):s(s), sz(s.size()) {}
        ~scoped_stack() { s.shrink(sz); }
    };

};

#endif

template<typename T>
class ptr_vector : public vector<T *, false> {
public:
    ptr_vector():vector<T *, false>() {}
    ptr_vector(unsigned s):vector<T *, false>(s) {}
    ptr_vector(unsigned s, T * elem):vector<T *, false>(s, elem) {}
    ptr_vector(unsigned s, T * const * data):vector<T *, false>(s, const_cast<T**>(data)) {}
};

template<typename T, typename SZ = unsigned>
class svector : public vector<T, false, SZ> {
public:
    svector():vector<T, false, SZ>() {}
    svector(SZ s):vector<T, false, SZ>(s) {}
    svector(SZ s, T const & elem):vector<T, false, SZ>(s, elem) {}
    svector(SZ s, T const * data):vector<T, false, SZ>(s, data) {}
};



using int_vector         = svector<int>;
using unsigned_vector    = svector<unsigned>;
using char_vector        = svector<char>;
using signed_char_vector = svector<signed char>;
using double_vector      = svector<double>;
using bool_vector        = svector<bool>;

template<typename T>
inline std::ostream& operator<<(std::ostream& out, svector<T> const& v) {
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
struct vector_hash : public vector_hash_tpl<Hash, vector<typename Hash::data_t> > {};

template<typename Hash>
struct svector_hash : public vector_hash_tpl<Hash, svector<typename Hash::data_t> > {};


template<typename T>
inline std::ostream& operator<<(std::ostream& out, vector<T> const& v) {
    bool first = true;
    for (auto const& t : v) {
        if (first) first = false; else out << " ";
        out << t;
    }
    return out;
 }
