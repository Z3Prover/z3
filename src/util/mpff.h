/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mpff.h

Abstract:

    Multi precision fast floating point numbers.
    The implementation is not compliant with the IEEE standard.
    For an IEEE compliant implementation, see mpf.h

    There are only two rounding modes: towards plus or minus inf.
    
Author:

    Leonardo de Moura (leonardo) 2012-09-12

Revision History:

--*/
#pragma once

#include "util/id_gen.h"
#include "util/util.h"
#include "util/vector.h"
#include "util/z3_exception.h"
#include "util/scoped_numeral.h"
#include "util/scoped_numeral_vector.h"
#include "util/mpn.h"

class mpff_manager;

class mpff {
    friend class mpff_manager;
    unsigned m_sign:1;
    unsigned m_sig_idx:31; // position where the significand is stored in the mpff_manager.
    int      m_exponent;
public:
    mpff():
        m_sign(0),
        m_sig_idx(0),
        m_exponent(0) {
    }
    
    void swap(mpff & other) { 
        unsigned sign    = m_sign;    m_sign    = other.m_sign;    other.m_sign = sign;
        unsigned sig_idx = m_sig_idx; m_sig_idx = other.m_sig_idx; other.m_sig_idx = sig_idx;
        std::swap(m_exponent, other.m_exponent); 
    }
};

inline void swap(mpff & m1, mpff & m2) { m1.swap(m2); }

class mpz;
class mpq;
template<bool SYNCH> class mpz_manager;
template<bool SYNCH> class mpq_manager;
#ifndef SINGLE_THREAD
typedef mpz_manager<true>  synch_mpz_manager;
typedef mpq_manager<true>  synch_mpq_manager;
#else
typedef mpz_manager<false>  synch_mpz_manager;
typedef mpq_manager<false>  synch_mpq_manager;
#endif
typedef mpz_manager<false> unsynch_mpz_manager;
typedef mpq_manager<false> unsynch_mpq_manager;

class mpff_manager {
    // Some restrictions on mpff numbers
    // 
    // - The exponent is always a machine integer. The main point is that 2^(2^31) is a huge number, 
    //   we will not even be able to convert the mpff into mpq. Formulas that need this kind of huge number 
    //   are usually out-of-reach for Z3. 
    // 
    // - The significand size is measured in words of 32-bit. The number of words is always even.
    //   This decision makes sure that the size (in bits) of mpff numbers is always a multiple of 64.
    //   Thus mpff objs can be easily packed in 64-bit machines.
    //
    // - The smallest mpff numeral has 128-bits total. mpff structure has always 64-bits.
    //   The minimal size for the significand is 64-bits.
    //
    // - All mpff numerals in a given manager use the same number of words for storing the significand.
    //   This is different from the mpf_manager where the same manager can be used to manipulate floating point numbers
    //   of different precision.
    // 
    // - In the encoding used for mpff numbers, the most significand bit of the most significand word is always 1.
    //   The only exception is the number zero.
    //   For example, assuming we are using 64-bits for the significand, the number 1 is encoded as
    //         (sign = 0, significand = 0x800..0, exponent = -63)
    //   Note that, in this representation, the smallest positive integer is:
    //         (sign = 0, significand = 0x800..0, exponent = INT_MIN)
    //   instead of 
    //         (sign = 0, significand = 0x000..1, exponent = INT_MIN)
    // 
    // Remarks:
    //
    // - All values of type int, unsigned, int64_t and uint64_t can be precisely represented as mpff numerals.
    //
    // - Hardware float and double values (corresponding to rationals) can also be precisely represented as mpff numerals.
    //   That is, NaN, +oo and -oo are not supported by this module.
    //
    // - An exception (mpff_manager::exception) is thrown if overflow occurs. This can happen because the exponent is
    //   represented as a machine integer.
    //
    // - There are only two rounding modes: towards plus infinity and towards minus infinity.
    //   The rounding mode can be dynamically modified.
    // 
    // - The mpff numerals are stored in a dynamic array.
    //   Type mpff is just an index (unsigned) into this array.
    
    unsigned          m_precision;      //!< Number of words in the significand. Must be an even number.
    unsigned          m_precision_bits; //!< Number of bits in the significand.  Must be 32*m_precision.
    mutable unsigned_vector   m_significands;   //!< Array containing all significands.
    unsigned          m_capacity;       //!< Number of significands that can be stored in m_significands.
    bool              m_to_plus_inf;    //!< If True, then round to plus infinity, otherwise to minus infinity
    id_gen            m_id_gen;
    static const unsigned MPFF_NUM_BUFFERS = 4;
    svector<unsigned> m_buffers[MPFF_NUM_BUFFERS];      
    svector<unsigned> m_set_buffer;
    mpff              m_one;
    mpn_manager       m_mpn_manager;

    unsigned * sig(mpff const & n) const { return m_significands.data() + (n.m_sig_idx * m_precision); }
    
    void ensure_capacity(unsigned sig_idx) {
        while (sig_idx >= m_capacity) 
            expand();
    }
    
    void expand();

    void allocate_if_needed(mpff & n) {
        if (n.m_sig_idx == 0)
            allocate(n);
    }

    void allocate(mpff & n);

    // copy n to buffer idx.
    void to_buffer(unsigned idx, mpff const & n) const;
    // copy n to buffer idx and add m_precision zeros.
    void to_buffer_ext(unsigned idx, mpff const & n) const;
    // copy (and shift by m_precision_bits) n to buffer idx 
    void to_buffer_shifting(unsigned idx, mpff const & n) const;

    void inc_significand(unsigned * s, int64_t & exp);
    void inc_significand(mpff & a);
    void dec_significand(mpff & a);
    bool min_significand(mpff const & a) const;
    void set_min_significand(mpff & a);
    void set_max_significand(mpff & a);
    void set_big_exponent(mpff & a, int64_t e);
    void set_exponent(mpff & a, int64_t e) {
        if (e > INT_MAX || e < INT_MIN) 
            set_big_exponent(a, e);
        else
            a.m_exponent = static_cast<int>(e);
    }

    template<bool SYNCH>
    void set_core(mpff & n, mpz_manager<SYNCH> & m, mpz const & v);

    template<bool SYNCH>
    void set_core(mpff & n, mpq_manager<SYNCH> & m, mpq const & v);

    template<bool SYNCH>
    void to_mpz_core(mpff const & n, mpz_manager<SYNCH> & m, mpz & t);

    template<bool SYNCH>
    void to_mpq_core(mpff const & n, mpq_manager<SYNCH> & m, mpq & t);

    template<bool SYNCH>
    void significand_core(mpff const & n, mpz_manager<SYNCH> & m, mpz & r);

    void add_sub(bool is_sub, mpff const & a, mpff const & b, mpff & c);
    
public:
    typedef mpff numeral;
    static bool precise() { return false; }
    static bool field() { return true; }

    class exception : public z3_exception {
        char const * msg() const override { return "multi-precision floating point (mpff) exception"; }
    };
    
    class overflow_exception : public exception {
        char const * msg() const override { return "multi-precision floating point (mpff) overflow"; }
    };

    class div0_exception : public exception {
        char const * msg() const override { return "multi-precision floating point (mpff) division by zero"; }
    };
    
    mpff_manager(unsigned prec = 2, unsigned initial_capacity = 1024);
    ~mpff_manager();

    void round_to_plus_inf() { m_to_plus_inf = true; }
    void round_to_minus_inf() { m_to_plus_inf = false; }
    void set_rounding(bool to_plus_inf) { m_to_plus_inf = to_plus_inf; }
    bool rounding_to_plus_inf() const { return m_to_plus_inf; }

    /**
       \brief Return the exponent of n.
    */
    static int exponent(mpff const & n) { return n.m_exponent; }
    
    /**
       \brief Update the exponent of n.

       \remark It is a NOOP if n is zero.
    */
    void set_exponent(mpff & n, int exp) { if (is_zero(n)) return; n.m_exponent = exp; SASSERT(check(n)); }

    /**
       \brief Return the significand as a mpz numeral.
    */
    void significand(mpff const & n, unsynch_mpz_manager & m, mpz & r);
#ifndef SINGLE_THREAD
    void significand(mpff const & n, synch_mpz_manager & m, mpz & r);
#endif

    /**
       \brief Return true if n is negative
    */
    static bool sign(mpff const & n) { return is_neg(n); }

    /**
       \brief Set n to zero.
    */
    void reset(mpff & n);

    /**
       \brief Return true if n is an integer.
    */
    bool is_int(mpff const & n) const;
    
    /**
       \brief Return true if n is zero.
    */
    static bool is_zero(mpff const & n) { return n.m_sig_idx == 0; }

    /**
       \brief Return true if n is positive.
    */
    static bool is_pos(mpff const & n) { return n.m_sign == 0 && !is_zero(n); }

    /**
       \brief Return true if n is negative.
    */
    static bool is_neg(mpff const & n) { return n.m_sign != 0; }

    /**
       \brief Return true if n is non positive.
    */
    static bool is_nonpos(mpff const & n) { return !is_pos(n); }
    
    /**
       \brief Return true if n is non negative.
    */
    static bool is_nonneg(mpff const & n) { return !is_neg(n); }

    /**
       \brief Return true if the absolute value of n is 1.
     */
    bool is_abs_one(mpff const & n) const;
    
    /**
       \brief Return true if n is one.
    */
    bool is_one(mpff const & n) const { return is_pos(n) && is_abs_one(n); }

    /**
       \brief Return true if n is minus one.
    */
    bool is_minus_one(mpff const & n) const { return is_neg(n) && is_abs_one(n); }

    /**
       \brief Return true if n is two.
    */
    bool is_two(mpff const & n) const;

    /**
       \brief Return true if \c a is the smallest representable negative number.
    */
    bool is_minus_epsilon(mpff const & a) const;

    /**
       \brief Return true if \c a is the smallest representable positive number.
     */
    bool is_plus_epsilon(mpff const & a) const;

    /**
       \brief Return true if \c a is an integer and fits in an int64_t machine integer.
    */
    bool is_int64(mpff const & a) const;

    /**
       \brief Return true if \c a is a non-negative integer and fits in an int64_t machine integer.
    */
    bool is_uint64(mpff const & a) const;
    
    /**
       \brief Delete the resources associated with n.
    */
    void del(mpff & n);
    
    /**
       \brief a <- -a
    */
    static void neg(mpff & a) { if (!is_zero(a)) a.m_sign = !a.m_sign; }

    /**
       \brief a <- |a|
    */
    static void abs(mpff & a) { a.m_sign = 0; }

    static void swap(mpff & a, mpff & b) { a.swap(b); }

    /**
       \brief c <- a + b
    */
    void add(mpff const & a, mpff const & b, mpff & c);

    /**
       \brief c <- a - b
    */
    void sub(mpff const & a, mpff const & b, mpff & c);

    /**
       \brief a <- a + 1
    */
    void inc(mpff & a) { add(a, m_one, a); }

    /**
       \brief a <- a - 1
    */
    void dec(mpff & a) { sub(a, m_one, a); }

    /**
       \brief c <- a * b
    */
    void mul(mpff const & a, mpff const & b, mpff & c);

    /**
       \brief c <- a / b
       
       \pre !is_zero(b)
    */
    void div(mpff const & a, mpff const & b, mpff & c);

    /**
       \brief a <- 1/a

       \pre !is_zero(a);
    */
    void inv(mpff & a) { div(m_one, a, a); }
    void inv(mpff const & a, mpff & b) { set(b, a); inv(b); }

    /**
       \brief b <- a^k
    */
    void power(mpff const & a, unsigned k, mpff & b);

    /**
       \brief Return true if \c a is a power of 2. That is, a is equal to 2^k for some k >= 0.
    */
    bool is_power_of_two(mpff const & a, unsigned & k) const;
    bool is_power_of_two(mpff const & a) const;
    
    bool eq(mpff const & a, mpff const & b) const;
    bool neq(mpff const & a, mpff const & b) const { return !eq(a, b); }
    bool lt(mpff const & a, mpff const & b) const;
    bool gt(mpff const & a, mpff const & b) const { return lt(b, a); }
    bool le(mpff const & a, mpff const & b) const { return !lt(b, a); }
    bool ge(mpff const & a, mpff const & b) const { return !lt(a, b); }
    
    void set(mpff & n, int v);
    void set(mpff & n, unsigned v);
    void set(mpff & n, int64_t v);
    void set(mpff & n, uint64_t v);
    void set(mpff & n, int num, unsigned den);
    void set(mpff & n, int64_t num, uint64_t den);
    void set(mpff & n, mpff const & v);
    void set(mpff & n, unsynch_mpz_manager & m, mpz const & v);
    void set(mpff & n, unsynch_mpq_manager & m, mpq const & v);
#ifndef SINGLE_THREAD
    void set(mpff & n, synch_mpq_manager & m, mpq const & v);
    void set(mpff & n, synch_mpz_manager & m, mpz const & v);
#endif
    void set_plus_epsilon(mpff & n);
    void set_minus_epsilon(mpff & n);
    void set_max(mpff & n);
    void set_min(mpff & n);

    /**
       \brief n <- floor(n)
    */
    void floor(mpff & n);
    void floor(mpff const & n, mpff & o) { set(o, n); floor(o); }

    /**
       \brief n <- ceil(n)
    */
    void ceil(mpff & n);
    void ceil(mpff const & n, mpff & o) { set(o, n); ceil(o); }

    /**
       \brief Update \c a to the next representable float.
       
       Throws an exception if \c a is the maximal representable float.
    */
    void next(mpff & a);
    /**
       \brief Update \c a to the previous representable float.
       
       Throws an exception if \c a is the minimal representable float.
    */
    void prev(mpff & a);
    
    /**
       \brief Convert n into a mpz numeral.
       
       \pre is_int(n)
       
       \remark if exponent(n) is too big, we may run out of memory.
    */
    void to_mpz(mpff const & n, unsynch_mpz_manager & m, mpz & t);

#ifndef SINGLE_THREAD
    /**
       \brief Convert n into a mpz numeral.
       
       \pre is_int(n)

       \remark if exponent(n) is too big, we may run out of memory.
    */
    void to_mpz(mpff const & n, synch_mpz_manager & m, mpz & t);
#endif


    /**
       \brief Convert n into a mpq numeral.

       \remark if exponent(n) is too big, we may run out of memory.
    */
    void to_mpq(mpff const & n, unsynch_mpq_manager & m, mpq & t);

#ifndef SINGLE_THREAD
    /**
       \brief Convert n into a mpq numeral.

       \remark if exponent(n) is too big, we may run out of memory.
    */
    void to_mpq(mpff const & n, synch_mpq_manager & m, mpq & t);
#endif

    /**
       \brief Return n as an int64.

       \pre is_int64(n)
    */
    int64_t get_int64(mpff const & n) const;

    /**
       \brief Return n as an uint64.

       \pre is_uint64(n)
    */
    uint64_t get_uint64(mpff const & n) const;

    /**
       \brief Return the biggest k s.t. 2^k <= a.
       
       \remark Return 0 if a is not positive.
    */
    unsigned prev_power_of_two(mpff const & a);

    void display_raw(std::ostream & out, mpff const & n) const;
    void display(std::ostream & out, mpff const & n) const;
    void display_pp(std::ostream & out, mpff const & n) const { display(out, n); }
    void display_decimal(std::ostream & out, mpff const & n, unsigned prec=32, unsigned max_power=128);
    void display_smt2(std::ostream & out, mpff const & n, bool decimal=true) const;

    std::string to_string(mpff const & a) const;
    std::string to_rational_string(mpff const & a) const;
    
    bool check(mpff const & n) const;
};

typedef _scoped_numeral<mpff_manager> scoped_mpff;
typedef _scoped_numeral_vector<mpff_manager> scoped_mpff_vector;

