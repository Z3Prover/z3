/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    util.h

Abstract:

    Useful functions & macros

Author:

    Leonardo de Moura (leonardo) 2006-09-11.

Revision History:

--*/
#ifndef UTIL_H_
#define UTIL_H_

#include "util/debug.h"
#include "util/memory_manager.h"
#include "util/z3_omp.h"
#include<iostream>
#include<climits>
#include<limits>
#include<stdint.h>

#ifndef SIZE_MAX
#define SIZE_MAX std::numeric_limits<std::size_t>::max()
#endif


static_assert(sizeof(uint64_t) == 8, "64 bits please");

static_assert(sizeof(int64_t) == 8, "64 bits");

#ifndef INT64_MIN
#define INT64_MIN static_cast<int64_t>(0x8000000000000000ull)
#endif
#ifndef INT64_MAX
#define INT64_MAX static_cast<int64_t>(0x7fffffffffffffffull)
#endif                              
#ifndef UINT64_MAX
#define UINT64_MAX 0xffffffffffffffffull
#endif

#ifdef _WINDOWS
#define SSCANF sscanf_s
// #define SPRINTF sprintf_s
#define SPRINTF_D(_buffer_, _i_) sprintf_s(_buffer_, Z3_ARRAYSIZE(_buffer_), "%d", _i_)
#define SPRINTF_U(_buffer_, _u_) sprintf_s(_buffer_, Z3_ARRAYSIZE(_buffer_), "%u", _u_)
#define _Exit exit
#else
#define SSCANF sscanf
// #define SPRINTF sprintf
#define SPRINTF_D(_buffer_, _i_) sprintf(_buffer_, "%d", _i_)
#define SPRINTF_U(_buffer_, _u_) sprintf(_buffer_, "%u", _u_)
#endif



#define VEC2PTR(_x_) ((_x_).size() ? &(_x_)[0] : 0)

#ifdef _MSC_VER
# define STD_CALL __cdecl
#else
# define STD_CALL
#endif

#ifdef __fallthrough
# define Z3_fallthrough __fallthrough
#elif defined(__has_cpp_attribute)
# if __has_cpp_attribute(clang::fallthrough)
#  define Z3_fallthrough [[clang::fallthrough]]
# else
#  define Z3_fallthrough
# endif
#else
# define Z3_fallthrough
#endif

inline bool is_power_of_two(unsigned v) { return !(v & (v - 1)) && v; }

/**
   \brief Return the next power of two that is greater than or equal to v.
   
   \warning This function returns 0 for v == 0.
*/
inline unsigned next_power_of_two(unsigned v) {
    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;
    return v;
}

/**
   \brief Return the position of the most significant bit.
*/
unsigned log2(unsigned v);
unsigned uint64_log2(uint64_t v);

static_assert(sizeof(unsigned) == 4, "unsigned are 32 bits");

// Return the number of 1 bits in v.
static inline unsigned get_num_1bits(unsigned v) {
#ifdef __GNUC__
    return __builtin_popcount(v);
#else
#ifdef Z3DEBUG
    unsigned c;
    unsigned v1 = v;
    for (c = 0; v1; c++) {
        v1 &= v1 - 1; 
    }
#endif
    v = v - ((v >> 1) & 0x55555555);                    
    v = (v & 0x33333333) + ((v >> 2) & 0x33333333);     
    unsigned r = (((v + (v >> 4)) & 0xF0F0F0F) * 0x1010101) >> 24; 
    SASSERT(c == r);
    return r;
#endif
}

// Remark: on gcc, the operators << and >> do not produce zero when the second argument >= 64.
// So, I'm using the following two definitions to fix the problem
static inline uint64_t shift_right(uint64_t x, uint64_t y) {
    return y < 64ull ? (x >> y) : 0ull;
}

static inline uint64_t shift_left(uint64_t x, uint64_t y) {
    return y < 64ull ? (x << y) : 0ull;
}

template<class T, size_t N> char (*ArraySizer(T (&)[N]))[N]; 
// For determining the length of an array. See ARRAYSIZE() macro. This function is never actually called.

#define Z3_ARRAYSIZE(a) sizeof(*ArraySizer(a))

template<typename IT>
void display(std::ostream & out, const IT & begin, const IT & end, const char * sep, bool & first) {
    for(IT it = begin; it != end; ++it) {
    if (first) {
        first = false;
    }
    else {
        out << sep;
    }
    out << *it;
    }
}

template<typename IT>
void display(std::ostream & out, const IT & begin, const IT & end, const char * sep = " ") {
    bool first = true;
    display(out, begin, end, sep, first);
}

template<typename T>
struct delete_proc {
    void operator()(T * ptr) { 
    if (ptr) {
        dealloc(ptr);
    }
    }
};

void set_verbosity_level(unsigned lvl);
unsigned get_verbosity_level();
std::ostream& verbose_stream();
void set_verbose_stream(std::ostream& str);
#ifdef _NO_OMP_
# define is_threaded() false
#else
bool is_threaded();
#endif

  
#define IF_VERBOSE(LVL, CODE) {                                 \
    if (get_verbosity_level() >= LVL) {                         \
        if (is_threaded()) {                                    \
            LOCK_CODE(CODE);                                    \
        }                                                       \
        else {                                                  \
            CODE;                                               \
        }                                                       \
    } } ((void) 0)              

#ifdef _MSC_VER
#define DO_PRAGMA(x) __pragma(x)
#define PRAGMA_LOCK __pragma(omp critical (verbose_lock))
#else
#define DO_PRAGMA(x) _Pragma(#x)
#define PRAGMA_LOCK _Pragma("omp critical (verbose_lock)")
#endif

#ifdef _NO_OMP_
#define LOCK_CODE(CODE) CODE;
#else
#define LOCK_CODE(CODE)                         \
    {                                           \
        PRAGMA_LOCK   \
            {                                   \
                CODE;                           \
            }                                   \
    }                      
#endif

template<typename T>
struct default_eq {
    typedef T data;
    bool operator()(const T & e1, const T & e2) const {
        return e1 == e2;
    }
};

template<typename T>
struct ptr_eq {
    typedef T * data;
    bool operator()(T * a1, T * a2) const { 
        return a1 == a2;
    }
};

template<typename T>
struct deref_eq {
    typedef T * data;
    bool operator()(T * a1, T * a2) const { 
        return *a1 == *a2;
    }
};

template<typename T>
class scoped_ptr {
    T * m_ptr;
public:
    scoped_ptr(T * ptr=nullptr):
        m_ptr(ptr) {
    }

    ~scoped_ptr() {
        dealloc(m_ptr);
    }

    T * operator->() const { 
        return m_ptr; 
    }

    T * get() const { 
        return m_ptr; 
    }

    operator bool() const { 
        return m_ptr != nullptr;
    }
    
    const T & operator*() const {
        return *m_ptr;
    }

    T & operator*() {
        return *m_ptr;
    }

    scoped_ptr & operator=(T * n) {
        if (m_ptr != n) {
            dealloc(m_ptr);
            m_ptr = n;
        }
        return *this;
    }

    T * detach() {
        T* tmp = m_ptr;
        m_ptr = nullptr;
        return tmp;
    }

    void swap(scoped_ptr & p) {
        std::swap(m_ptr, p.m_ptr);
    }
};

template<typename T1, typename T2>
inline std::ostream & operator<<(std::ostream & out, std::pair<T1, T2> const & p) {
    out << "(" << p.first << ", " << p.second << ")";
    return out;
}

template<typename IT>
bool has_duplicates(const IT & begin, const IT & end) {
    for (IT it1 = begin; it1 != end; ++it1) {
        IT it2 = it1;
        ++it2;
        for (; it2 != end; ++it2) {
            if (*it1 == *it2) {
                return true;
            }
        }
    }
    return false;
}

#ifndef _WINDOWS
#ifndef __declspec
#define __declspec(X)
#endif
#endif

template<typename T>
class flet {
    T & m_ref;
    T   m_old_value;
public:
    flet(T & ref, const T & new_value):
        m_ref(ref),
        m_old_value(ref) {
        m_ref = new_value;
    }
    ~flet() {
        m_ref = m_old_value;
    }
};

template<typename T>
bool compare_arrays(const T * array1, const T * array2, unsigned size) {
    for (unsigned i = 0; i < size; i++) {
        if (!(array1[i] == array2[i])) {
            return false;
        }
    }
    return true;
}

template<typename T>
void force_ptr_array_size(T & v, unsigned sz) {
    if (sz > v.size()) {
        v.resize(sz);
    }
}

class random_gen {
    unsigned m_data;
public:
    random_gen(unsigned seed = 0):
        m_data(seed) {
    }

    void set_seed(unsigned s) { m_data = s; }

    int operator()() {
        return ((m_data = m_data * 214013L + 2531011L) >> 16) & 0x7fff; 
    }

    unsigned operator()(unsigned u) {
        unsigned r = static_cast<unsigned>((*this)());
        return r % u;
    }
    
    static int max_value() {
        return 0x7fff;
    }
};

template<typename T>
void shuffle(unsigned sz, T * array, random_gen & gen) {
    int n = sz;
    while (--n > 0) {
        int k = gen() % (n + 1);
        std::swap(array[n], array[k]);
    }
}

#ifdef _EXTERNAL_RELEASE
#define INTERNAL_CODE(CODE) ((void) 0)
#else
#define INTERNAL_CODE(CODE) { CODE } ((void) 0)
#endif

void fatal_error(int error_code);

void set_fatal_error_handler(void (*pfn)(int error_code));


/**
   \brief Iterator for the [0..sz[0]) X [0..sz[1]) X ... X [0..sz[n-1]).
   it contains the current value.
   Return true if there is a next element, and store the next element in it.
*/
bool product_iterator_next(unsigned n, unsigned const * sz, unsigned * it);

/**
   \brief Macro for avoiding error messages.
*/
#define TRUSTME(cond) if (!cond) { UNREACHABLE(); fatal_error(0); exit(0); }

class escaped {
    char const * m_str;
    bool         m_trim_nl; // if true -> eliminate '\n' in the end of m_str.
    unsigned     m_indent;
    char const * end() const;
public:
    escaped(char const * str, bool trim_nl = false, unsigned indent = 0):m_str(str), m_trim_nl(trim_nl), m_indent(indent) {}
    void display(std::ostream & out) const;
};

inline std::ostream & operator<<(std::ostream & out, escaped const & s) { s.display(out); return out; }

inline size_t megabytes_to_bytes(unsigned mb) {
    if (mb == UINT_MAX)
        return SIZE_MAX;
    unsigned long long b = static_cast<unsigned long long>(mb) * 1024ull * 1024ull;
    size_t r = static_cast<size_t>(b);
    if (r != b)  // overflow
        r = SIZE_MAX;    
    return r;
}


#endif /* UTIL_H_ */

