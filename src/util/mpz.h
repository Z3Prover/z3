/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    mpz.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-06-17.

Revision History:

--*/
#pragma once

#include<string>
#include "util/mutex.h"
#include "util/util.h"
#include "util/small_object_allocator.h"
#include "util/trace.h"
#include "util/scoped_numeral.h"
#include "util/scoped_numeral_vector.h"
#include "util/mpn.h"

unsigned u_gcd(unsigned u, unsigned v);
uint64_t u64_gcd(uint64_t u, uint64_t v);

#ifdef _MP_GMP
typedef unsigned digit_t;
#endif

#ifdef _MSC_VER
#pragma warning(disable : 4200)
#endif

template<bool SYNCH> class mpz_manager;
template<bool SYNCH> class mpq_manager;

#if !defined(_MP_GMP) && !defined(_MP_MSBIGNUM) && !defined(_MP_INTERNAL)
#ifdef _WINDOWS
#define _MP_INTERNAL
#else
#define _MP_GMP
#endif
#endif

#if defined(_MP_MSBIGNUM)
typedef size_t digit_t;
#elif defined(_MP_INTERNAL)
typedef unsigned int digit_t;
#endif

#ifndef _MP_GMP
class mpz_cell {
    unsigned  m_size;
    unsigned  m_capacity;
    digit_t   m_digits[0];
    friend class mpz_manager<true>;
    friend class mpz_manager<false>;
    friend class mpz_stack;
};
#else
#include<gmp.h>
#endif

/**
   \brief Multi-precision integer.
   
   If m_kind == mpz_small, it is a small number and the value is stored in m_val.
   If m_kind == mpz_large,   the value is stored in m_ptr and m_ptr != nullptr.
                           m_val contains the sign (-1 negative, 1 positive)   
                           under winodws, m_ptr points to a mpz_cell that store the value. 
*/

enum mpz_kind { mpz_small = 0, mpz_large = 1};
enum mpz_owner { mpz_self = 0, mpz_ext = 1};

class mpz {
#ifndef _MP_GMP
    typedef mpz_cell mpz_type;
#else
    typedef mpz_t mpz_type;
#endif
    int        m_val; 
    unsigned   m_kind:1;
    unsigned   m_owner:1;
    mpz_type * m_ptr;
    friend class mpz_manager<true>;
    friend class mpz_manager<false>;
    friend class mpq_manager<true>;
    friend class mpq_manager<false>;
    friend class mpq;
    friend class mpbq;
    friend class mpbq_manager;
    friend class mpz_stack;
public:
    mpz(int v):m_val(v), m_kind(mpz_small), m_owner(mpz_self), m_ptr(nullptr) {}
    mpz():m_val(0), m_kind(mpz_small), m_owner(mpz_self), m_ptr(nullptr) {}
    mpz(mpz_type* ptr): m_val(0), m_kind(mpz_small), m_owner(mpz_ext), m_ptr(ptr) { SASSERT(ptr);}
    mpz(mpz && other) noexcept : m_val(other.m_val), m_kind(other.m_kind), m_owner(other.m_owner), m_ptr(nullptr) {
        std::swap(m_ptr, other.m_ptr);
    }

    mpz& operator=(mpz const& other) = delete;
    mpz& operator=(mpz &&other) noexcept {
        swap(other);
        return *this;
    }

    void swap(mpz & other) { 
        std::swap(m_val, other.m_val);
        std::swap(m_ptr, other.m_ptr);
        unsigned o = m_owner; m_owner = other.m_owner; other.m_owner = o;
        unsigned k = m_kind; m_kind = other.m_kind; other.m_kind = k;
    }
};

#ifndef _MP_GMP
class mpz_stack : public mpz {
    static const unsigned capacity = 8;
    unsigned char m_bytes[sizeof(mpz_cell) + sizeof(digit_t) * capacity];
public:
    mpz_stack():mpz(reinterpret_cast<mpz_cell*>(m_bytes)) {
        m_ptr->m_capacity = capacity;
    }
};
#else
class mpz_stack : public mpz {};
#endif

inline void swap(mpz & m1, mpz & m2) { m1.swap(m2); }

template<bool SYNCH = true>
class mpz_manager {
    mutable small_object_allocator  m_allocator;
#ifndef SINGLE_THREAD
    mutable std::recursive_mutex    m_lock;
#define MPZ_BEGIN_CRITICAL() if (SYNCH) m_lock.lock()
#define MPZ_END_CRITICAL()   if (SYNCH) m_lock.unlock()
#else
#define MPZ_BEGIN_CRITICAL() {}
#define MPZ_END_CRITICAL()   {}
#endif
    mutable mpn_manager             m_mpn_manager;

#ifndef _MP_GMP
    unsigned                m_init_cell_capacity;
    mpz                     m_int_min;
    
    static unsigned cell_size(unsigned capacity) { 
        return sizeof(mpz_cell) + sizeof(digit_t) * capacity; 
    }

    mpz_cell * allocate(unsigned capacity);
    
    // make sure that n is a big number and has capacity equal to at least c.
    void allocate_if_needed(mpz & n, unsigned c) {
        if (m_init_cell_capacity > c) c = m_init_cell_capacity;
        if (n.m_ptr == nullptr || capacity(n) < c) {
            deallocate(n);
            n.m_val             = 1;
            n.m_kind            = mpz_large;
            n.m_owner           = mpz_self;
            n.m_ptr             = allocate(c);
        }
        else {
            n.m_kind = mpz_large;
        }
    }

    void deallocate(bool is_heap, mpz_cell * ptr);
    
    // Expand capacity of a while preserving its content.
    void ensure_capacity(mpz & a, unsigned sz);

    void normalize(mpz & a);

    void clear(mpz& n) { reset(n); }

    /**
       \brief Set \c a with the value stored at src, and the given sign.
       \c sz is an overapproximation of the size of the number stored at \c src.
    */
    void set(mpz_cell& src, mpz & a, int sign, unsigned sz); 


#else
    // GMP code
    mutable mpz_t     m_tmp, m_tmp2;
    mutable mpz_t     m_two32;
    mpz_t  *  m_arg[2];
    mutable mpz_t     m_uint64_max;
    mutable mpz_t     m_int64_max;
    mutable mpz_t     m_int64_min;

    mpz_t * allocate() {        
        mpz_t * cell;
#ifdef SINGLE_THREAD
        cell = reinterpret_cast<mpz_t*>(m_allocator.allocate(sizeof(mpz_t)));        
#else
        if (SYNCH) {
            cell = reinterpret_cast<mpz_t*>(memory::allocate(sizeof(mpz_t)));
        }
        else {
            cell = reinterpret_cast<mpz_t*>(m_allocator.allocate(sizeof(mpz_t)));        
        }
#endif
        mpz_init(*cell);
        return cell;
    }

    void deallocate(bool is_heap, mpz_t * ptr) { 
        mpz_clear(*ptr); 
        if (is_heap) {
#ifdef SINGLE_THREAD
            m_allocator.deallocate(sizeof(mpz_t), ptr); 
#else
            if (SYNCH) {
                memory::deallocate(ptr);
            }
            else {
                m_allocator.deallocate(sizeof(mpz_t), ptr); 
            }
#endif
        }
    }

    void clear(mpz& n) { if (n.m_ptr) { mpz_clear(*n.m_ptr); }}
#endif

    void deallocate(mpz& n) {
        if (n.m_ptr) {
            deallocate(n.m_owner == mpz_self, n.m_ptr);
            n.m_ptr = nullptr;
            n.m_kind = mpz_small;
        }
    }

    mpz                     m_two64;


    static int64_t i64(mpz const & a) { return static_cast<int64_t>(a.m_val); }

    void set_big_i64(mpz & c, int64_t v);

    void set_i64(mpz & c, int64_t v) {
        if (v >= INT_MIN && v <= INT_MAX) {
            c.m_val = static_cast<int>(v); 
            c.m_kind = mpz_small;
        }
        else {
            set_big_i64(c, v);
        }
    }

    void set_big_ui64(mpz & c, uint64_t v);


#ifndef _MP_GMP

    static unsigned capacity(mpz const & c) { return c.m_ptr->m_capacity; }

    static unsigned size(mpz const & c) { return c.m_ptr->m_size; }

    static digit_t * digits(mpz const & c) { return c.m_ptr->m_digits; }

    // Return true if the absolute value fits in a UINT64
    static bool is_abs_uint64(mpz const & a) {
        if (is_small(a))
            return true;
        if (sizeof(digit_t) == sizeof(uint64_t))
            return size(a) <= 1;
        else
            return size(a) <= 2;
    }
    
    // CAST the absolute value into a UINT64
    static uint64_t big_abs_to_uint64(mpz const & a) {
        SASSERT(is_abs_uint64(a));
        SASSERT(!is_small(a));
        if (a.m_ptr->m_size == 1)
            return digits(a)[0];
        if (sizeof(digit_t) == sizeof(uint64_t))
            // 64-bit machine
            return digits(a)[0];
        else 
            // 32-bit machine
            return ((static_cast<uint64_t>(digits(a)[1]) << 32) | (static_cast<uint64_t>(digits(a)[0])));
    }

    class sign_cell {
        static const unsigned capacity = 2;
        unsigned char m_bytes[sizeof(mpz_cell) + sizeof(digit_t) * capacity];
        mpz m_local;
        mpz const& m_a;
        int m_sign;
        mpz_cell* m_cell;
    public:
        sign_cell(mpz_manager& m, mpz const& a);
        int             sign() { return m_sign; }
        mpz_cell const* cell() { return m_cell; }
    };

    void get_sign_cell(mpz const & a, int & sign, mpz_cell * & cell, mpz_cell* reserve) {
        if (is_small(a)) {
            if (a.m_val == INT_MIN) {
                sign = -1;
                cell = m_int_min.m_ptr;
            }
            else {
                cell = reserve;
                cell->m_size = 1;
                if (a.m_val < 0) {
                    sign = -1;
                    cell->m_digits[0] = -a.m_val;
                }
                else {
                    sign = 1;
                    cell->m_digits[0] = a.m_val;
                }
            }
        }
        else {
            sign = a.m_val;
            cell = a.m_ptr;
        }
    }

#else
    // GMP code

    class ensure_mpz_t {
        mpz_t m_local;
        mpz_t* m_result;
    public:
        ensure_mpz_t(mpz const& a);
        ~ensure_mpz_t();
        mpz_t& operator()() { return *m_result; }
    };
    
    void mk_big(mpz & a) {
        if (a.m_ptr == nullptr) {
            a.m_val = 0;
            a.m_ptr = allocate();
            a.m_owner = mpz_self;
        }
        a.m_kind = mpz_large;
    }


#endif 

#ifndef _MP_GMP
    template<bool SUB>
    void big_add_sub(mpz const & a, mpz const & b, mpz & c);
#endif

    void big_add(mpz const & a, mpz const & b, mpz & c);

    void big_sub(mpz const & a, mpz const & b, mpz & c);

    void big_mul(mpz const & a, mpz const & b, mpz & c);

    void big_set(mpz & target, mpz const & source);

#ifndef _MP_GMP

#define QUOT_ONLY 0
#define REM_ONLY  1
#define QUOT_AND_REM 2
#define qr_mode int
    
    template<qr_mode MODE>
    void quot_rem_core(mpz const & a, mpz const & b, mpz & q, mpz & r);
#endif

    void big_div_rem(mpz const & a, mpz const & b, mpz & q, mpz & r);

    void big_div(mpz const & a, mpz const & b, mpz & c);

    void big_rem(mpz const & a, mpz const & b, mpz & c);

    int big_compare(mpz const & a, mpz const & b);

public:
    unsigned size_info(mpz const & a);
    struct sz_lt;

    static bool precise() { return true; }
    static bool field() { return false; }

    typedef mpz numeral;

    mpz_manager();

    ~mpz_manager();

    static bool is_small(mpz const & a) { return a.m_kind == mpz_small; }

    static mpz mk_z(int val) { return mpz(val); }
    
    void del(mpz & a) { del(this, a); }

    static void del(mpz_manager* m, mpz & a);
    
    void add(mpz const & a, mpz const & b, mpz & c);

    void sub(mpz const & a, mpz const & b, mpz & c);
    
    void inc(mpz & a) { add(a, mpz(1), a); }

    void dec(mpz & a) { add(a, mpz(-1), a); }

    void mul(mpz const & a, mpz const & b, mpz & c);

    // d <- a + b*c
    void addmul(mpz const & a, mpz const & b, mpz const & c, mpz & d);

    // d <- a - b*c
    void submul(mpz const & a, mpz const & b, mpz const & c, mpz & d);

    void machine_div_rem(mpz const & a, mpz const & b, mpz & q, mpz & r);

    void machine_div(mpz const & a, mpz const & b, mpz & c);

    void rem(mpz const & a, mpz const & b, mpz & c);

    void div_gcd(mpz const & a, mpz const & b, mpz & c);

    void div(mpz const & a, mpz const & b, mpz & c);

    void mod(mpz const & a, mpz const & b, mpz & c);

    void neg(mpz & a);

    void abs(mpz & a);

    static bool is_pos(mpz const & a) { return sign(a) > 0; }

    static bool is_neg(mpz const & a) { return sign(a) < 0; }
    
    static bool is_zero(mpz const & a) { return sign(a) == 0; }

    static int sign(mpz const & a) {
#ifndef _MP_GMP
        return a.m_val;
#else
        if (is_small(a))
            return a.m_val;
        else
            return mpz_sgn(*a.m_ptr);
#endif
    }
    
    static bool is_nonpos(mpz const & a) { return !is_pos(a); }

    static bool is_nonneg(mpz const & a) { return !is_neg(a); }

    bool eq(mpz const & a, mpz const & b) {
        if (is_small(a) && is_small(b)) {
            return a.m_val == b.m_val;
        }
        else {
            return big_compare(a, b) == 0;
        }
    }

    bool lt(mpz const& a, int b) {
        if (is_small(a)) {
            return a.m_val < b;
        }
        else {
            return lt(a, mpz(b));
        }
    }

    bool lt(mpz const & a, mpz const & b) {
        if (is_small(a) && is_small(b)) {
            return a.m_val < b.m_val;
        }
        else {
            return big_compare(a, b) < 0;
        }
    }

    bool neq(mpz const & a, mpz const & b) { return !eq(a, b); }

    bool gt(mpz const & a, mpz const & b) { return lt(b, a); }

    bool ge(mpz const & a, mpz const & b) { return !lt(a, b); }

    bool le(mpz const & a, mpz const & b) { return !lt(b, a); }

    void gcd(mpz const & a, mpz const & b, mpz & c);
    
    void gcd(unsigned sz, mpz const * as, mpz & g);
    
    /**
       \brief Extended Euclid:
       r1*a + r2*b = g
    */
    void gcd(mpz const & r1, mpz const & r2, mpz & a, mpz & b, mpz & g);

    void lcm(mpz const & a, mpz const & b, mpz & c);

    /**
      \brief Return true if a | b
    */
    bool divides(mpz const & a, mpz const & b);

    // not a field
    void inv(mpz & a) {
        SASSERT(false);
    }

    void bitwise_or(mpz const & a, mpz const & b, mpz & c);

    void bitwise_and(mpz const & a, mpz const & b, mpz & c);

    void bitwise_xor(mpz const & a, mpz const & b, mpz & c);

    void bitwise_not(unsigned sz, mpz const & a, mpz & c);

    void set(mpz & target, mpz const & source) {
        if (is_small(source)) {
            target.m_val = source.m_val;
            target.m_kind = mpz_small;
        }
        else {
            big_set(target, source);
        }
    }

    void set(mpz & a, int val) {
        a.m_val = val;
        a.m_kind = mpz_small;
    }

    void set(mpz & a, unsigned val) {
        if (val <= INT_MAX)
            set(a, static_cast<int>(val));
        else
            set(a, static_cast<int64_t>(static_cast<uint64_t>(val)));
    }

    void set(mpz & a, char const * val);

    void set(mpz & a, int64_t val) {
        set_i64(a, val);
    }

    void set(mpz & a, uint64_t val) {
        if (val < INT_MAX) {
            a.m_val = static_cast<int>(val);
            a.m_kind = mpz_small;
        }
        else {
            set_big_ui64(a, val);
        }
    }

    void set_digits(mpz & target, unsigned sz, digit_t const * digits);

    mpz dup(const mpz & source) {
        mpz temp;
        set(temp, source);
        return temp;
    }

    // deallocates any memory.
    void reset(mpz & a);

    void swap(mpz & a, mpz & b) {
        std::swap(a.m_val, b.m_val);
        std::swap(a.m_ptr, b.m_ptr);
        auto o = a.m_owner; a.m_owner = b.m_owner; b.m_owner = o;
        auto k = a.m_kind; a.m_kind = b.m_kind; b.m_kind = k;
    }

    bool is_uint64(mpz const & a) const;

    bool is_int64(mpz const & a) const;

    uint64_t get_uint64(mpz const & a) const;

    int64_t get_int64(mpz const & a) const;

    bool is_uint(mpz const & a) const { return is_uint64(a) && get_uint64(a) < UINT_MAX; }
    
    unsigned get_uint(mpz const & a) const { SASSERT(is_uint(a)); return static_cast<unsigned>(get_uint64(a)); }

    bool is_int(mpz const & a) const { return is_int64(a) && INT_MIN < get_int64(a) && get_int64(a) < INT_MAX; }
    
    int get_int(mpz const & a) const { SASSERT(is_int(a)); return static_cast<int>(get_int64(a)); }

    double get_double(mpz const & a) const;

    std::string to_string(mpz const & a) const; 

    void display(std::ostream & out, mpz const & a) const;

    /**
       \brief Display mpz number in SMT 2.0 format.
       If decimal == true, then ".0" is appended.
    */
    void display_smt2(std::ostream & out, mpz const & a, bool decimal) const;

    /**
       \brief Displays the num_bits least significant bits of a mpz number in hexadecimal format.
       num_bits must be divisible by 4.
    */
    void display_hex(std::ostream & out, mpz const & a, unsigned num_bits) const;

    /**
       \brief Displays the num_bits least significant bits of a mpz number in binary format.
    */
    void display_bin(std::ostream & out, mpz const & a, unsigned num_bits) const;


    static unsigned hash(mpz const & a);

    static bool is_one(mpz const & a) {
#ifndef _MP_GMP
        return is_small(a) && a.m_val == 1;
#else
        if (is_small(a))
            return a.m_val == 1;
        return mpz_cmp_si(*a.m_ptr, 1) == 0;
#endif
    }

    static bool is_minus_one(mpz const & a) {
#ifndef _MP_GMP
        return is_small(a) && a.m_val == -1;
#else
        if (is_small(a))
            return a.m_val == -1;
        return mpz_cmp_si(*a.m_ptr, -1) == 0;
#endif
    }

    void power(mpz const & a, unsigned p, mpz & b);

    bool is_power_of_two(mpz const & a); 

    bool is_power_of_two(mpz const & a, unsigned & shift);
    
    void machine_div2k(mpz & a, unsigned k);

    void machine_div2k(mpz const & a, unsigned k, mpz & r) { set(r, a); machine_div2k(r, k); }
    
    void mul2k(mpz & a, unsigned k);

    void mul2k(mpz const & a, unsigned k, mpz & r) { set(r, a); mul2k(r, k); }

    /**
       \brief Return largest k s.t. n is a multiple of 2^k
    */
    unsigned power_of_two_multiple(mpz const & n);

    /**
       \brief Return the position of the most significant bit.
       Return 0 if the number is negative
    */
    unsigned log2(mpz const & n);

    /**
       \brief log2(-n)
       Return 0 if the number is nonegative
    */
    unsigned mlog2(mpz const & n);

    /**
       \brief Return the bit-size of n. This method is mainly used for collecting statistics.
    */
    unsigned bitsize(mpz const & n);
    
    /**
       \brief Return true if the number is a perfect square, and 
       store the square root in 'root'.
       If the number n is positive and the result is false, then
       root will contain the smallest integer r such that r*r > n.
    */
    bool is_perfect_square(mpz const & a, mpz & root);
    
    /**
       \brief Return the biggest k s.t. 2^k <= a.
       
       \remark Return 0 if a is not positive.
    */
    unsigned prev_power_of_two(mpz const & a) { return log2(a); }
    
    /**
       \brief Return true if a^{1/n} is an integer, and store the result in a.
       Otherwise return false, and update a with the smallest
       integer r such that r*r > n.
       
       \remark This method assumes that if n is even, then a is nonegative
    */
    bool root(mpz & a, unsigned n);
    bool root(mpz const & a, unsigned n, mpz & r) { set(r, a); return root(r, n); }

    bool is_even(mpz const & a) {
        if (is_small(a))
            return !(a.m_val & 0x1);
#ifndef _MP_GMP
        return !(0x1 & digits(a)[0]);
#else
        return mpz_even_p(*a.m_ptr);
#endif        
    }

    bool is_odd(mpz const & n) { return !is_even(n); }
    
    // Store the digits of n into digits, and return the sign.
    bool decompose(mpz const & n, svector<digit_t> & digits);

    bool get_bit(mpz const& a, unsigned bit);

};

#ifndef SINGLE_THREAD
typedef mpz_manager<true> synch_mpz_manager;
#else
typedef mpz_manager<false> synch_mpz_manager;
#endif
typedef mpz_manager<false> unsynch_mpz_manager;

typedef _scoped_numeral<unsynch_mpz_manager> scoped_mpz;
typedef _scoped_numeral<synch_mpz_manager> scoped_synch_mpz;
typedef _scoped_numeral_vector<unsynch_mpz_manager> scoped_mpz_vector;
