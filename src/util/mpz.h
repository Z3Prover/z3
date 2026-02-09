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
unsigned trailing_zeros(uint64_t);
unsigned trailing_zeros(uint32_t);


#ifdef _MP_GMP
typedef unsigned digit_t;
#endif

#ifdef _MSC_VER
#pragma warning(disable : 4200)
#endif

template<bool SYNCH> class mpz_manager;
template<bool SYNCH> class mpq_manager;

#if !defined(_MP_GMP) && !defined(_MP_INTERNAL)
#ifdef _WINDOWS
#define _MP_INTERNAL
#else
#define _MP_GMP
#endif
#endif

#ifndef _MP_GMP
typedef unsigned int digit_t;
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

   m_value encodes either a small integer (if the least significant bit is 1)
   or a pointer to a mpz_cell structure (if the least significant bit is 0).
   The last 3 bits of pointers are always 0 due to alignment, so we use them
   to store additional information:
        - bit 0: small/large info (0 = small, 1 = large)
        - bit 1: sign bit (0 = non-negative, 1 = negative)
        - bit 2: owner info (0 = owned, 1 = external)
*/

class mpz {
#ifndef _MP_GMP
    typedef mpz_cell mpz_type;
#else
    typedef mpz_t mpz_type;
#endif
private:
    uintptr_t m_value = 0;

    static constexpr uintptr_t LARGE_BIT = 0x1;
    static constexpr uintptr_t SIGN_BIT  = 0x2;
    static constexpr uintptr_t OWNER_BIT = 0x4;
    static constexpr uintptr_t MPZ_PTR_MASK  = ~static_cast<uintptr_t>(0x7);

    // Small integers are stored shifted left by 1, so we have (sizeof(uintptr_t)*8 - 1) bits available
    // This gives us:
    //   - On 32-bit platforms: 31 bits, range [-2^30, 2^30-1]
    //   - On 64-bit platforms: 63 bits, range [-2^62, 2^62-1]
    static constexpr int SMALL_BITS = sizeof(uintptr_t) * 8 - 1;
    
    // Maximum and minimum values that can be stored as small integers
    // Use unsigned arithmetic to avoid undefined behavior on left shift
    static constexpr int64_t SMALL_INT_MAX = (static_cast<uint64_t>(1) << (SMALL_BITS - 1)) - 1;
    static constexpr int64_t SMALL_INT_MIN = -(static_cast<int64_t>(static_cast<uint64_t>(1) << (SMALL_BITS - 1)));

    static bool fits_in_small(int64_t v) {
        return v >= SMALL_INT_MIN && v <= SMALL_INT_MAX;
    }

    static bool fits_in_small(uint64_t v) {
        return v <= static_cast<uint64_t>(SMALL_INT_MAX);
    }

    static bool fits_in_small(int v) {
        return fits_in_small(static_cast<int64_t>(v));
    }

    static bool fits_in_small(unsigned int v) {
        return fits_in_small(static_cast<uint64_t>(v));
    }

    mpz_type * ptr() const {
        SASSERT(!is_small());
        return reinterpret_cast<mpz_type*>(m_value & MPZ_PTR_MASK);
    }

    void set_ptr(mpz_type* p, bool is_negative, bool is_external) {
        SASSERT(is_small());
        SASSERT((reinterpret_cast<uintptr_t>(p) & 0x7) == 0); // Check alignment
        m_value = reinterpret_cast<uintptr_t>(p) | LARGE_BIT;
        if (is_negative)
            m_value |= SIGN_BIT;
        if (is_external)
            m_value |= OWNER_BIT;
    }

    int get_sign() const {
        SASSERT(!is_small());
        return (m_value & SIGN_BIT) ? -1 : 1;
    }

    void set_sign(int s) {
        SASSERT(!is_small());
        if (s < 0)
            m_value |= SIGN_BIT;
        else
            m_value &= ~SIGN_BIT;
    }

    bool is_external() const {
        SASSERT(!is_small());
        return (m_value & OWNER_BIT) != 0;
    }

protected:
    friend class mpz_manager<true>;
    friend class mpz_manager<false>;
    friend class mpq_manager<true>;
    friend class mpq_manager<false>;
    friend class mpq;
    friend class mpbq;
    friend class mpbq_manager;
    friend class mpz_stack;
public:
    mpz(int v = 0) noexcept : m_value(static_cast<uintptr_t>(static_cast<intptr_t>(v)) << 1) {
        // On 32-bit platforms, INT_MIN doesn't fit in 31 bits. This constructor should only be used
        // with values that fit, or the caller should use set_big_i64.
        SASSERT(fits_in_small(v));
    }
    
    mpz(mpz_type* ptr) noexcept {
        SASSERT(ptr);
        set_ptr(ptr, false, true); // external pointer, non-negative
    }
    
    mpz(mpz && other) noexcept : m_value(other.m_value) {
        other.m_value = 0; // reset other to small
    }

    mpz& operator=(mpz const& other) = delete;
    
    mpz& operator=(mpz &&other) noexcept {
        std::swap(m_value, other.m_value);
        return *this;
    }

    void set(int v) {
        SASSERT(is_small());
        m_value = static_cast<uintptr_t>(static_cast<intptr_t>(v)) << 1;
    }

    void set64(int64_t v) {
        SASSERT(fits_in_small(v));
        m_value = static_cast<uintptr_t>(static_cast<intptr_t>(v)) << 1;
    }

    void swap(mpz & other) noexcept {
        std::swap(m_value, other.m_value);
    }

    inline bool is_small() const { 
        return (m_value & LARGE_BIT) == 0; 
    }

    inline int value() const { 
        SASSERT(is_small());
        // Decode small integer: shift right by 1 (arithmetic shift to preserve sign)
        // Note: On 64-bit platforms, this may truncate if the value doesn't fit in int
        return static_cast<int>(static_cast<intptr_t>(m_value) >> 1);
    }

    inline int64_t value64() const { 
        SASSERT(is_small());
        // Decode small integer: shift right by 1 (arithmetic shift to preserve sign)
        return static_cast<int64_t>(static_cast<intptr_t>(m_value) >> 1);
    }

    inline int sign() const { 
        SASSERT(!is_small()); 
        return get_sign();
    }
};

#ifndef _MP_GMP
class mpz_stack : public mpz {
    static const unsigned capacity = 8;
    alignas(8) unsigned char m_bytes[sizeof(mpz_cell) + sizeof(digit_t) * capacity];
public:
    mpz_stack():mpz(reinterpret_cast<mpz_cell*>(m_bytes)) {
        ptr()->m_capacity = capacity;
    }
};
#else
class mpz_stack : public mpz {};
#endif

inline void swap(mpz & m1, mpz & m2) noexcept { m1.swap(m2); }

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
    // 64-bit machine?
    static const unsigned m_init_cell_capacity = sizeof(digit_t) == sizeof(uint64_t) ? 4 : 6;
    mpz                   m_int_min;
    
    static unsigned cell_size(unsigned capacity) { 
        return sizeof(mpz_cell) + sizeof(digit_t) * capacity; 
    }

    mpz_cell * allocate(unsigned capacity);
    
    // make sure that n is a big number and has capacity equal to at least c.
    void allocate_if_needed(mpz & n, unsigned c) {
        if (m_init_cell_capacity > c) c = m_init_cell_capacity;
        if (n.is_small() || n.ptr() == nullptr || capacity(n) < c) {
            deallocate(n);
            n.set_ptr(allocate(c), false, false); // positive, owned
        }
        // else already has enough capacity, keep as large
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
        if (SYNCH) {
            cell = reinterpret_cast<mpz_t*>(memory::allocate(sizeof(mpz_t)));
        }
        else {
            cell = reinterpret_cast<mpz_t*>(m_allocator.allocate(sizeof(mpz_t)));        
        }
        mpz_init(*cell);
        return cell;
    }

    void deallocate(bool is_heap, mpz_t * ptr) { 
        mpz_clear(*ptr); 
        if (is_heap) {
            if (SYNCH) {
                memory::deallocate(ptr);
            }
            else {
                m_allocator.deallocate(sizeof(mpz_t), ptr); 
            }
        }
    }

    void clear(mpz& n) { if (!n.is_small() && n.ptr()) { mpz_clear(*n.ptr()); }}
#endif

    void deallocate(mpz& n) {
        if (!n.is_small()) {
            auto* p = n.ptr();
            if (p) {
                deallocate(!n.is_external(), p);
                n.m_value = 0; // reset to small
            }
        }
    }

    mpz                     m_two64;


    static int64_t i64(mpz const & a) { return a.value64(); }

    void set_big_i64(mpz & c, int64_t v);

    void set_i64(mpz & c, int64_t v) {
        if (mpz::fits_in_small(v) && is_small(c)) {
            c.set64(v);
        }
        else {
            set_big_i64(c, v);
        }
    }

    void set_big_ui64(mpz & c, uint64_t v);


#ifndef _MP_GMP

    static unsigned capacity(mpz const & c) {
        SASSERT(!c.is_small());
        return c.ptr()->m_capacity;
    }

    static unsigned size(mpz const & c) {
        SASSERT(!c.is_small());
        return c.ptr()->m_size;
    }

    static digit_t * digits(mpz const & c) {
        SASSERT(!c.is_small());
        return c.ptr()->m_digits;
    }

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
        if (a.ptr()->m_size == 1)
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
            int64_t val = a.value64();
            cell = reserve;
            if (val < 0) {
                sign = -1;
                uint64_t abs_val = static_cast<uint64_t>(-val);
                if (sizeof(digit_t) == sizeof(uint64_t)) {
                    cell->m_size = 1;
                    cell->m_digits[0] = static_cast<digit_t>(abs_val);
                }
                else {
                    cell->m_digits[0] = static_cast<unsigned>(abs_val);
                    cell->m_digits[1] = static_cast<unsigned>(abs_val >> 32);
                    cell->m_size = (abs_val >> 32) == 0 ? 1 : 2;
                }
            }
            else {
                sign = 1;
                if (sizeof(digit_t) == sizeof(uint64_t)) {
                    cell->m_size = 1;
                    cell->m_digits[0] = static_cast<digit_t>(val);
                }
                else {
                    cell->m_digits[0] = static_cast<unsigned>(val);
                    cell->m_digits[1] = static_cast<unsigned>(val >> 32);
                    cell->m_size = (val >> 32) == 0 ? 1 : 2;
                }
            }
        }
        else {
            sign = a.sign();
            cell = a.ptr();
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
        if (a.is_small()) {
            a.set_ptr(allocate(), false, false); // positive, owned
        }
        // else already large with valid pointer
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
    static unsigned size_info(mpz const & a);
    struct sz_lt;

    static bool precise() { return true; }
    static bool field() { return false; }

    typedef mpz numeral;

    mpz_manager();

    ~mpz_manager();

    static bool is_small(mpz const & a) { return a.is_small(); }

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

    mpz mod2k(mpz const & a, unsigned k);

    void neg(mpz & a);

    void abs(mpz & a);

    static bool is_pos(mpz const & a) { return sign(a) > 0; }

    static bool is_neg(mpz const & a) { return sign(a) < 0; }
    
    static bool is_zero(mpz const & a) { return sign(a) == 0; }

    static int sign(mpz const & a) {
        if (is_small(a)) {
            int v = a.value();
            return (v > 0) - (v < 0); // Returns -1, 0, or 1
        }
        else
#ifndef _MP_GMP
            return a.sign();
#else
            return mpz_sgn(*a.ptr());
#endif
    }
    
    static bool is_nonpos(mpz const & a) { return !is_pos(a); }

    static bool is_nonneg(mpz const & a) { return !is_neg(a); }

    bool eq(mpz const & a, mpz const & b) {
        if (is_small(a) && is_small(b)) {
            return a.value() == b.value();
        }
        else {
            return big_compare(a, b) == 0;
        }
    }

    bool lt(mpz const& a, int b) {
        if (is_small(a)) {
            return a.value() < b;
        }
        else {
            return lt(a, mpz(b));
        }
    }

    bool lt(mpz const & a, mpz const & b) {
        if (is_small(a) && is_small(b)) {
            return a.value() < b.value();
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
            target.set(source.value());
        }
        else {
            big_set(target, source);
        }
    }

    void set(mpz & a, int val) {
        // On 32-bit platforms, int can be outside small range
        if (mpz::fits_in_small(val) && is_small(a)) {
            a.set(val);
        }
        else {
            set_i64(a, val);
        }
    }

    void set(mpz & a, unsigned val) {
        if (mpz::fits_in_small(val) && is_small(a)) {
            a.set(static_cast<int>(val));
        }
        else {
            set_i64(a, static_cast<int64_t>(val));
        }
    }

    void set(mpz & a, char const * val);

    void set(mpz & a, int64_t val) {
        set_i64(a, val);
    }

    void set(mpz & a, uint64_t val) {
        if (mpz::fits_in_small(val) && is_small(a)) {
            a.set64(static_cast<int64_t>(val));
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

    void swap(mpz & a, mpz & b) noexcept {
        a.swap(b);
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
        return is_small(a) && a.value() == 1;
#else
        if (is_small(a))
            return a.value() == 1;
        return mpz_cmp_si(*a.ptr(), 1) == 0;
#endif
    }

    static bool is_minus_one(mpz const & a) {
#ifndef _MP_GMP
        return is_small(a) && a.value() == -1;
#else
        if (is_small(a))
            return a.value() == -1;
        return mpz_cmp_si(*a.ptr(), -1) == 0;
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
       \brief Return the smallest k s.t. a <= 2^k.

       \remark Return 0 if a is not positive.
    */
    unsigned next_power_of_two(mpz const & a);
    
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
            return !(a.value() & 0x1);
#ifndef _MP_GMP
        return !(0x1 & digits(a)[0]);
#else
        return mpz_even_p(*a.ptr());
#endif        
    }

    bool is_odd(mpz const & n) { return !is_even(n); }
    
    // Store the digits of n into digits, and return the sign.
    bool decompose(mpz const & n, svector<digit_t> & digits);

    bool get_bit(mpz const& a, unsigned bit);

    digit_t get_least_significant(mpz const& a);

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
