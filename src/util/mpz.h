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
#ifndef MPZ_H_
#define MPZ_H_

#include<limits.h>
#include<string>
#include"util.h"
#include"small_object_allocator.h"
#include"trace.h"
#include"scoped_numeral.h"
#include"scoped_numeral_vector.h"
#include"z3_omp.h"
#include"mpn.h"

unsigned u_gcd(unsigned u, unsigned v);
uint64 u64_gcd(uint64 u, uint64 v);

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
};
#else
#include<gmp.h>
#endif

/**
   \brief Multi-precision integer.
   
   If m_ptr == 0, the it is a small number and the value is stored at m_val.
   Otherwise, m_val contains the sign (-1 negative, 1 positive), and m_ptr points to a mpz_cell that
   store the value. <<< This last statement is true only in Windows.
*/
class mpz {
    int        m_val; 
#ifndef _MP_GMP
    mpz_cell * m_ptr;
#else
    mpz_t * m_ptr;
#endif
    friend class mpz_manager<true>;
    friend class mpz_manager<false>;
    friend class mpq_manager<true>;
    friend class mpq_manager<false>;
    friend class mpq;
    friend class mpbq;
    friend class mpbq_manager;
    mpz & operator=(mpz const & other) { UNREACHABLE(); return *this; }
public:
    mpz(int v):m_val(v), m_ptr(0) {}
    mpz():m_val(0), m_ptr(0) {}
    void swap(mpz & other) { 
        std::swap(m_val, other.m_val);
        std::swap(m_ptr, other.m_ptr);
    }
};

inline void swap(mpz & m1, mpz & m2) { m1.swap(m2); }

template<bool SYNCH = true>
class mpz_manager {
    small_object_allocator  m_allocator;
    omp_nest_lock_t         m_lock;
#define MPZ_BEGIN_CRITICAL() if (SYNCH) omp_set_nest_lock(&m_lock);
#define MPZ_END_CRITICAL()   if (SYNCH) omp_unset_nest_lock(&m_lock);
    mpn_manager             m_mpn_manager;

#ifndef _MP_GMP
    unsigned                m_init_cell_capacity;
    mpz_cell *              m_tmp[2];
    mpz_cell *              m_arg[2];
    mpz                     m_int_min;
    
    static unsigned cell_size(unsigned capacity) { return sizeof(mpz_cell) + sizeof(digit_t) * capacity; }

    mpz_cell * allocate(unsigned capacity) {
        SASSERT(capacity >= m_init_cell_capacity);
        mpz_cell * cell  = reinterpret_cast<mpz_cell *>(m_allocator.allocate(cell_size(capacity)));
        cell->m_capacity = capacity;
        return cell;
    }
    
    // make sure that n is a big number and has capacity equal to at least c.
    void allocate_if_needed(mpz & n, unsigned c) {
        if (c < m_init_cell_capacity)
            c = m_init_cell_capacity;
        if (is_small(n)) {
            n.m_val             = 1;
            n.m_ptr             = allocate(c);
            n.m_ptr->m_capacity = c;
        }
        else if (capacity(n) < c) {
            deallocate(n.m_ptr);
            n.m_val             = 1;
            n.m_ptr             = allocate(c);
            n.m_ptr->m_capacity = c;
        }
    }

    void deallocate(mpz_cell * ptr) { 
        m_allocator.deallocate(cell_size(ptr->m_capacity), ptr); 
    }

    /**
      \brief Make sure that m_tmp[IDX] can hold the given number of digits
    */
    template<int IDX>
    void ensure_tmp_capacity(unsigned capacity) {
        if (m_tmp[IDX]->m_capacity >= capacity)
            return;
        deallocate(m_tmp[IDX]);
        unsigned new_capacity = (3 * capacity + 1) >> 1;
        m_tmp[IDX] = allocate(new_capacity);
        SASSERT(m_tmp[IDX]->m_capacity >= capacity);
    }
    
    // Expand capacity of a while preserving its content.
    void ensure_capacity(mpz & a, unsigned sz);

    void normalize(mpz & a);
#else
    // GMP code
    mpz_t     m_tmp, m_tmp2;
    mpz_t     m_two32;
    mpz_t  *  m_arg[2];
    mpz_t     m_uint64_max;
    mpz_t     m_int64_max;
    mpz_t     m_int64_min;

    mpz_t * allocate() {
        mpz_t * cell = reinterpret_cast<mpz_t*>(m_allocator.allocate(sizeof(mpz_t)));
        mpz_init(*cell);
        return cell;
    }

    void deallocate(mpz_t * ptr) { mpz_clear(*ptr); m_allocator.deallocate(sizeof(mpz_t), ptr); }
#endif
    mpz                     m_two64;

    /**
       \brief Set \c a with the value stored at m_tmp[IDX], and the given sign.
       \c sz is an overapproximation of the the size of the number stored at \c tmp.
    */
    template<int IDX>
    void set(mpz & a, int sign, unsigned sz);

    static int64 i64(mpz const & a) { return static_cast<int64>(a.m_val); }

    void set_big_i64(mpz & c, int64 v);

    void set_i64(mpz & c, int64 v) { 
        if (v >= INT_MIN && v <= INT_MAX) {
            del(c);
            c.m_val = static_cast<int>(v); 
        }
        else {
            MPZ_BEGIN_CRITICAL();
            set_big_i64(c, v);
            MPZ_END_CRITICAL();
        }
    }

    void set_big_ui64(mpz & c, uint64 v);

#ifndef _MP_GMP
    static unsigned capacity(mpz const & c) { return c.m_ptr->m_capacity; }

    static unsigned size(mpz const & c) { return c.m_ptr->m_size; }

    static digit_t * digits(mpz const & c) { return c.m_ptr->m_digits; }

    // Return true if the absolute value fits in a UINT64
    static bool is_abs_uint64(mpz const & a) {
        if (is_small(a))
            return true;
        if (sizeof(digit_t) == sizeof(uint64))
            return size(a) <= 1;
        else
            return size(a) <= 2;
    }
    
    // CAST the absolute value into a UINT64
    static uint64 big_abs_to_uint64(mpz const & a) {
        SASSERT(is_abs_uint64(a));
        SASSERT(!is_small(a));
        if (a.m_ptr->m_size == 1)
            return digits(a)[0];
        if (sizeof(digit_t) == sizeof(uint64))
            // 64-bit machine
            return digits(a)[0];
        else 
            // 32-bit machine
            return ((static_cast<uint64>(digits(a)[1]) << 32) | (static_cast<uint64>(digits(a)[0])));
    }

    template<int IDX>
    void get_sign_cell(mpz const & a, int & sign, mpz_cell * & cell) {
        if (is_small(a)) {
            if (a.m_val == INT_MIN) {
                sign = -1;
                cell = m_int_min.m_ptr;
            }
            else {
                cell = m_arg[IDX];
                SASSERT(cell->m_size == 1);
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

    template<int IDX>
    void get_arg(mpz const & a, mpz_t * & result) {
        if (is_small(a)) {
            result = m_arg[IDX];
            mpz_set_si(*result, a.m_val);
        }
        else {
            result = a.m_ptr;
        }
    }
    
    void mk_big(mpz & a) {
        if (a.m_ptr == 0) {
            a.m_val = 0;
            a.m_ptr = allocate();
        }
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
    
    unsigned size_info(mpz const & a);
    struct sz_lt;

public:
    static bool precise() { return true; }
    static bool field() { return false; }

    typedef mpz numeral;

    mpz_manager();

    ~mpz_manager();

    static bool is_small(mpz const & a) { return a.m_ptr == 0; }

    static mpz mk_z(int val) { return mpz(val); }
    
    void del(mpz & a) { 
        if (a.m_ptr != 0) {
            MPZ_BEGIN_CRITICAL();
            deallocate(a.m_ptr); 
            MPZ_END_CRITICAL();
            a.m_ptr = 0; 
        } 
    }
    
    void add(mpz const & a, mpz const & b, mpz & c) {
        STRACE("mpz", tout << "[mpz] " << to_string(a) << " + " << to_string(b) << " == ";); 
        if (is_small(a) && is_small(b)) {
            set_i64(c, i64(a) + i64(b));
        }
        else {
            MPZ_BEGIN_CRITICAL();
            big_add(a, b, c);
            MPZ_END_CRITICAL();
        }
        STRACE("mpz", tout << to_string(c) << "\n";);
    }

    void sub(mpz const & a, mpz const & b, mpz & c) {
        STRACE("mpz", tout << "[mpz] " << to_string(a) << " - " << to_string(b) << " == ";); 
        if (is_small(a) && is_small(b)) {
            set_i64(c, i64(a) - i64(b));
        }
        else {
            MPZ_BEGIN_CRITICAL();
            big_sub(a, b, c);
            MPZ_END_CRITICAL();
        }
        STRACE("mpz", tout << to_string(c) << "\n";);
    }
    
    void inc(mpz & a) { add(a, mpz(1), a); }

    void dec(mpz & a) { add(a, mpz(-1), a); }

    void mul(mpz const & a, mpz const & b, mpz & c) {
        STRACE("mpz", tout << "[mpz] " << to_string(a) << " * " << to_string(b) << " == ";); 
        if (is_small(a) && is_small(b)) {
            set_i64(c, i64(a) * i64(b));
        }
        else {
            MPZ_BEGIN_CRITICAL();
            big_mul(a, b, c);
            MPZ_END_CRITICAL();
        }
        STRACE("mpz", tout << to_string(c) << "\n";);
    }

    // d <- a + b*c
    void addmul(mpz const & a, mpz const & b, mpz const & c, mpz & d) {
        if (is_one(b)) {
            add(a, c, d);
        }
        else if (is_minus_one(b)) {
            sub(a, c, d);
        }
        else {
            mpz tmp;
            mul(b,c,tmp);
            add(a,tmp,d);
            del(tmp);
        }
    }


    // d <- a - b*c
    void submul(mpz const & a, mpz const & b, mpz const & c, mpz & d) {
        if (is_one(b)) {
            sub(a, c, d);
        }
        else if (is_minus_one(b)) {
            add(a, c, d);
        }
        else {
            mpz tmp;
            mul(b,c,tmp);
            sub(a,tmp,d);
            del(tmp);
        }
    }


    void machine_div_rem(mpz const & a, mpz const & b, mpz & q, mpz & r) {
        STRACE("mpz", tout << "[mpz-ext] divrem(" << to_string(a) << ",  " << to_string(b) << ") == ";); 
        if (is_small(a) && is_small(b)) {
            int64 _a = i64(a);
            int64 _b = i64(b);
            set_i64(q, _a / _b);
            set_i64(r, _a % _b);
        }
        else {
            MPZ_BEGIN_CRITICAL();
            big_div_rem(a, b, q, r);
            MPZ_END_CRITICAL();
        }
        STRACE("mpz", tout << "(" << to_string(q) << ", " << to_string(r) << ")\n";);
    }

    void machine_div(mpz const & a, mpz const & b, mpz & c) {
        STRACE("mpz", tout << "[mpz-ext] machine-div(" << to_string(a) << ",  " << to_string(b) << ") == ";); 
        if (is_small(a) && is_small(b)) {
            set_i64(c, i64(a) / i64(b));
        }
        else {
            MPZ_BEGIN_CRITICAL();
            big_div(a, b, c);
            MPZ_END_CRITICAL();
        }
        STRACE("mpz", tout << to_string(c) << "\n";);
    }

    void rem(mpz const & a, mpz const & b, mpz & c) {
        STRACE("mpz", tout << "[mpz-ext] rem(" << to_string(a) << ",  " << to_string(b) << ") == ";); 
        if (is_small(a) && is_small(b)) {
            set_i64(c, i64(a) % i64(b));
        }
        else {
            MPZ_BEGIN_CRITICAL();
            big_rem(a, b, c);
            MPZ_END_CRITICAL();
        }
        STRACE("mpz", tout << to_string(c) << "\n";);
    }

    void div(mpz const & a, mpz const & b, mpz & c) {
        STRACE("mpz", tout << "[mpz-ext] div(" << to_string(a) << ",  " << to_string(b) << ") == ";); 
        if (is_neg(a)) {
            mpz tmp;
            machine_div_rem(a, b, c, tmp);
            if (!is_zero(tmp)) {
                if (is_neg(b))
                    add(c, mk_z(1), c);
                else
                    sub(c, mk_z(1), c);
            }
            del(tmp);
        }
        else {
            machine_div(a, b, c);
        }
        STRACE("mpz", tout << to_string(c) << "\n";);
    }

    void mod(mpz const & a, mpz const & b, mpz & c) {
        STRACE("mpz", tout << "[mpz-ext] mod(" << to_string(a) << ",  " << to_string(b) << ") == ";); 
        rem(a, b, c);
        if (is_neg(c)) {
            if (is_pos(b))
                add(c, b, c);
            else
                sub(c, b, c);
        }
        STRACE("mpz", tout << to_string(c) << "\n";);
    }

    void neg(mpz & a) {
        STRACE("mpz", tout << "[mpz] 0 - " << to_string(a) << " == ";); 
        if (is_small(a) && a.m_val == INT_MIN) {
            // neg(INT_MIN) is not a small int
            MPZ_BEGIN_CRITICAL();
            set_big_i64(a, - static_cast<long long>(INT_MIN)); 
            MPZ_END_CRITICAL();
            return;
        }
#ifndef _MP_GMP
        a.m_val = -a.m_val;
#else
        if (is_small(a)) {
            a.m_val = -a.m_val;
        }
        else {
            mpz_neg(*a.m_ptr, *a.m_ptr);
        }
#endif
        STRACE("mpz", tout << to_string(a) << "\n";); 
    }

    void abs(mpz & a) {
        if (is_small(a)) {
            if (a.m_val < 0) {
                if (a.m_val == INT_MIN) {
                    // abs(INT_MIN) is not a small int
                    MPZ_BEGIN_CRITICAL();
                    set_big_i64(a, - static_cast<long long>(INT_MIN)); 
                    MPZ_END_CRITICAL();
                }
                else
                    a.m_val = -a.m_val;
            }
        }
        else {
#ifndef _MP_GMP
            a.m_val = 1;
#else
            mpz_abs(*a.m_ptr, *a.m_ptr);
#endif
        }
    }

    static bool is_pos(mpz const & a) { 
#ifndef _MP_GMP
        return a.m_val > 0; 
#else
        if (is_small(a))
            return a.m_val > 0;
        else
            return mpz_sgn(*a.m_ptr) > 0;
#endif
    }

    static bool is_neg(mpz const & a) { 
#ifndef _MP_GMP
        return a.m_val < 0; 
#else
        if (is_small(a))
            return a.m_val < 0;
        else
            return mpz_sgn(*a.m_ptr) < 0;
#endif
    }
    
    static bool is_zero(mpz const & a) { 
#ifndef _MP_GMP
        return a.m_val == 0; 
#else
        if (is_small(a))
            return a.m_val == 0;
        else
            return mpz_sgn(*a.m_ptr) == 0;
#endif
    }

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
            MPZ_BEGIN_CRITICAL();
            bool res = big_compare(a, b) == 0;
            MPZ_END_CRITICAL();
            return res;
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
            MPZ_BEGIN_CRITICAL();
            bool res = big_compare(a, b) < 0;
            MPZ_END_CRITICAL();
            return res;
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
            del(target);
            target.m_val = source.m_val;
        }
        else {
            MPZ_BEGIN_CRITICAL();
            big_set(target, source);
            MPZ_END_CRITICAL();
        }
    }

    void set(mpz & a, int val) {
        del(a);
        a.m_val = val;
    }

    void set(mpz & a, unsigned val) {
        if (val <= INT_MAX)
            set(a, static_cast<int>(val));
        else
            set(a, static_cast<int64>(static_cast<uint64>(val)));
    }

    void set(mpz & a, char const * val);

    void set(mpz & a, int64 val) {
        set_i64(a, val);
    }

    void set(mpz & a, uint64 val) {
        if (val < INT_MAX) {
            del(a);
            a.m_val = static_cast<int>(val);
        }
        else {
            MPZ_BEGIN_CRITICAL();
            set_big_ui64(a, val);
            MPZ_END_CRITICAL();
        }
    }

    void set(mpz & target, unsigned sz, digit_t const * digits);

    void reset(mpz & a) {
        del(a);
        a.m_val = 0;
    }

    void swap(mpz & a, mpz & b) {
        std::swap(a.m_val, b.m_val);
        std::swap(a.m_ptr, b.m_ptr);
    }

    bool is_uint64(mpz const & a) const;

    bool is_int64(mpz const & a) const;

    uint64 get_uint64(mpz const & a) const;

    int64 get_int64(mpz const & a) const;

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
};

typedef mpz_manager<true> synch_mpz_manager;
typedef mpz_manager<false> unsynch_mpz_manager;

typedef _scoped_numeral<unsynch_mpz_manager> scoped_mpz;
typedef _scoped_numeral<synch_mpz_manager> scoped_synch_mpz;
typedef _scoped_numeral_vector<unsynch_mpz_manager> scoped_mpz_vector;

#endif /* MPZ_H_ */

