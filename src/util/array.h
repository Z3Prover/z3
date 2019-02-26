/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    array.h

Abstract:

    Fixed size arrays

Author:

    Leonardo de Moura (leonardo) 2011-01-26.

Revision History:

--*/
#ifndef ARRAY_H_
#define ARRAY_H_

template<typename T, bool CallDestructors=true>
class array {
public:
    // Return the space needed to store an array of size sz.
    static size_t space(size_t sz) { return sizeof(T)*sz + sizeof(size_t); }
    
private:
#define ARRAY_SIZE_IDX     -1
    T * m_data;
    void destroy_elements() {
        iterator it = begin();
        iterator e  = end();
        for (; it != e; ++it) {
            it->~T();
        }
    }

    char * raw_ptr() const { return reinterpret_cast<char*>(reinterpret_cast<size_t*>(m_data) - 1); }

    array & operator=(array const & source);

    void set_data(void * mem, unsigned sz) {
        size_t * _mem = static_cast<size_t*>(mem);
        *_mem = sz; 
        _mem ++;
        m_data = reinterpret_cast<T*>(_mem);
    }

    template<typename Allocator>
    void allocate(Allocator & a, unsigned sz) {
        size_t * mem  = reinterpret_cast<size_t*>(a.allocate(space(sz)));
        set_data(mem, sz);
    }

    void init(T const & v) {
        iterator it = begin();
        iterator e  = end();
        for (; it != e; ++it) {
            new (it) T(v);
        }
    }
    
    void init(T const * vs) {
        iterator it = begin();
        iterator e  = end();
        for (; it != e; ++it, ++vs) {
            new (it) T(*vs); 
        }
    }

public:
    typedef T data;
    typedef T * iterator;
    typedef const T * const_iterator;

    array():m_data(nullptr) {}

    /**
       \brief Store the array in the given chunk of memory (mem).
       This chunck should be big enough to store space(sz) bytes.
    */
    array(void * mem, unsigned sz, T const * vs) {
        DEBUG_CODE(m_data = 0;);
        set(mem, sz, vs);
    }

    // WARNING: the memory allocated will not be automatically freed.
    array(void * mem, unsigned sz, bool init_mem) {
        DEBUG_CODE(m_data = 0;);
        set_data(mem, sz);
        if (init_mem)
            init();
    }

    // WARNING: the memory allocated will not be automatically freed.
    template<typename Allocator>
    array(Allocator & a, unsigned sz, T const * vs) {
        DEBUG_CODE(m_data = 0;);
        set(a, sz, vs);
    }

    // WARNING: the memory allocated will not be automatically freed.
    template<typename Allocator>
    array(Allocator & a, unsigned sz, bool init_mem) {
        DEBUG_CODE(m_data = 0;);
        allocate(a, sz);
        if (init_mem)
            init();
    }
    
    // WARNING: this does not free the memory used to store the array.
    // You must free it yourself, or use finalize.
    ~array() {
        if (m_data && CallDestructors)
            destroy_elements();
    }

    // Free the memory used to store the array.
    template<typename Allocator>
    void finalize(Allocator & a) {
        if (m_data) {
            if (CallDestructors)
                destroy_elements();
            a.deallocate(space(size()), raw_ptr());
            m_data = nullptr;
        }
    }

    void set(void * mem, unsigned sz, T const * vs) {
        SASSERT(m_data == 0);
        set_data(mem, sz);
        init(vs);
    }
    
    template<typename Allocator>
    void set(Allocator & a, unsigned sz, T const * vs) {
        SASSERT(m_data == 0);
        allocate(a, sz);
        init(vs);
    }

    template<typename Allocator>
    void set(Allocator & a, unsigned sz, T const & v = T()) {
        SASSERT(m_data == 0);
        allocate(a, sz);
        init(v);
    }

    unsigned size() const { 
        if (m_data == nullptr) {
            return 0;  
        }
        return static_cast<unsigned>(reinterpret_cast<size_t *>(m_data)[ARRAY_SIZE_IDX]); 
    }
    
    bool empty() const { return m_data == nullptr; }

    T & operator[](unsigned idx) { 
        SASSERT(idx < size()); 
        return m_data[idx]; 
    }

    T const & operator[](unsigned idx) const { 
        SASSERT(idx < size()); 
        return m_data[idx];
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

    T const * c_ptr() const { return m_data; }
    T * c_ptr() { return m_data; }

    void swap(array & other) {
        std::swap(m_data, other.m_data);
    }

};

template<typename T>
class ptr_array : public array<T *, false> {
public:
    ptr_array() {}
    ptr_array(void * mem, unsigned sz, T * const * vs):array<T*, false>(mem, sz, vs) {}
    template<typename Allocator>
    ptr_array(Allocator & a, unsigned sz, T * const * vs):array<T*, false>(a, sz, vs) {}
    ptr_array(void * mem, unsigned sz, bool init_mem):array<T*, false>(mem, sz, init_mem) {}
    template<typename Allocator>
    ptr_array(Allocator & a, unsigned sz, bool init_mem):array<T*, false>(a, sz, init_mem) {}
};

template<typename T>
class sarray : public array<T, false> {
public:
    sarray() {}
    sarray(void * mem, unsigned sz, T const * vs):array<T, false>(mem, sz, vs) {}
    template<typename Allocator>
    sarray(Allocator & a, unsigned sz, T const * vs):array<T, false>(a, sz, vs) {}
    sarray(void * mem, unsigned sz, bool init_mem):array<T, false>(mem, sz, init_mem) {}
    template<typename Allocator>
    sarray(Allocator & a, unsigned sz, bool init_mem):array<T, false>(a, sz, init_mem) {}
};

#endif
