/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mpfx.h

Abstract:

    Multi precision fixed point numbers.
    
Author:

    Leonardo de Moura (leonardo) 2012-09-19

Revision History:

--*/
#ifndef _MPFX_H_
#define _MPFX_H_

#include"id_gen.h"
#include"util.h"
#include"vector.h"
#include"z3_exception.h"
#include"scoped_numeral.h"
#include"scoped_numeral_vector.h"
#include"mpn.h"

class mpfx_manager;

class mpfx {
    friend class mpfx_manager;
    unsigned m_sign:1;
    unsigned m_sig_idx:31; // position where the data is stored in the mpfx_manager.
public:
    mpfx():
        m_sign(0),
        m_sig_idx(0) {
    }
    
    void swap(mpfx & other) { 
        unsigned sign    = m_sign;    m_sign    = other.m_sign;    other.m_sign = sign;
        unsigned sig_idx = m_sig_idx; m_sig_idx = other.m_sig_idx; other.m_sig_idx = sig_idx;
    }
};

inline void swap(mpfx & m1, mpfx & m2) { m1.swap(m2); }

class mpz;
class mpq;
template<bool SYNCH> class mpz_manager;
template<bool SYNCH> class mpq_manager;
typedef mpz_manager<true>  synch_mpz_manager;
typedef mpz_manager<false> unsynch_mpz_manager;
typedef mpq_manager<true>  synch_mpq_manager;
typedef mpq_manager<false> unsynch_mpq_manager;

class mpfx_manager {
    // Every mpfx numeral from a given mpfx_manager uses the same number of words
    // to encode the integer and fractional parts.
    // 
    // The number of words used to encode the integer part may be different from the number of words
    // used to encode the fractional part.
    //
    // There are two rounding modes: towards plus infinity, and towards minus infinity.
    //
    // If the result of an operation does not fit in the integer part, then an overflow exception is thrown.
    //
    // If the fractional part uses n words, then the error of every operation is less than 1/2^(32*n).
    // 
    // Machine integer values (int, unsigned, int64, uint64) can be easily converted into mpfx numerals.
    //
    // The result of addition and subtraction operations are always precise. Note that overflows will trigger
    // an exception instead of an incorrect result.
    //
    unsigned          m_int_part_sz;
    unsigned          m_frac_part_sz;
    unsigned          m_total_sz;       //!< == m_int_part_sz + m_frac_part_sz
    unsigned_vector   m_words;          //!< Array containing all words
    unsigned          m_capacity;       //!< Number of mpfx numerals that can be stored in m_words.
    bool              m_to_plus_inf;    //!< If True, then round to plus infinity, otherwise to minus infinity
    id_gen            m_id_gen;
    unsigned_vector   m_buffer0, m_buffer1, m_buffer2;
    unsigned_vector   m_tmp_digits;
    mpfx              m_one;
    mpn_manager       m_mpn_manager;

    unsigned * words(mpfx const & n) const { return m_words.c_ptr() + (n.m_sig_idx * m_total_sz); }
    unsigned sz(unsigned * ws) const;

    void ensure_capacity(unsigned sig_idx) {
        while (sig_idx >= m_capacity) 
            expand();
    }
    
    void expand();
    
    void allocate_if_needed(mpfx & n) {
        if (n.m_sig_idx == 0)
            allocate(n);
    }

    void allocate(mpfx & n);

    void set_epsilon(mpfx & n);

    void add_sub(bool is_sub, mpfx const & a, mpfx const & b, mpfx & c);

    template<bool SYNCH>
    void set_core(mpfx & n, mpz_manager<SYNCH> & m, mpz const & v);

    template<bool SYNCH>
    void set_core(mpfx & n, mpq_manager<SYNCH> & m, mpq const & v);

    template<bool SYNCH>
    void to_mpz_core(mpfx const & n, mpz_manager<SYNCH> & m, mpz & t);

    template<bool SYNCH>
    void to_mpq_core(mpfx const & n, mpq_manager<SYNCH> & m, mpq & t);

public:
    typedef mpfx numeral;
    static bool precise() { return false; }
    static bool field() { return true; }

    class exception : public z3_exception {
        virtual char const * msg() const { return "multi-precision fixed point (mpfx) exception"; }
    };
    
    class overflow_exception : public exception {
        virtual char const * msg() const { return "multi-precision fixed point (mpfx) overflow"; }
    };
    
    class div0_exception : public exception {
        virtual char const * msg() const { return "multi-precision fixed point (mpfx) division by zero"; }
    };

    mpfx_manager(unsigned int_sz = 2, unsigned frac_sz = 1, unsigned initial_capacity = 1024);
    ~mpfx_manager();

    void round_to_plus_inf() { m_to_plus_inf = true; }
    void round_to_minus_inf() { m_to_plus_inf = false; }
    void set_rounding(bool to_plus_inf) { m_to_plus_inf = to_plus_inf; }
    bool rounding_to_plus_inf() const { return m_to_plus_inf; }
    
    /**
       \brief Return true if n is negative
    */
    static bool sign(mpfx const & n) { return is_neg(n); }

    /**
       \brief Set n to zero.
    */
    void reset(mpfx & n);

    /**
       \brief Return true if n is an integer.
    */
    bool is_int(mpfx const & n) const;
    
    /**
       \brief Return true if n is zero.
    */
    static bool is_zero(mpfx const & n) { return n.m_sig_idx == 0; }

    /**
       \brief Return true if n is positive.
    */
    static bool is_pos(mpfx const & n) { return n.m_sign == 0 && !is_zero(n); }

    /**
       \brief Return true if n is negative.
    */
    static bool is_neg(mpfx const & n) { return n.m_sign != 0; }

    /**
       \brief Return true if n is non positive.
    */
    static bool is_nonpos(mpfx const & n) { return !is_pos(n); }
    
    /**
       \brief Return true if n is non negative.
    */
    static bool is_nonneg(mpfx const & n) { return !is_neg(n); }

    /**
       \brief Return true if the absolute value of n is 1.
     */
    bool is_abs_one(mpfx const & n) const;
    
    /**
       \brief Return true if n is one.
    */
    bool is_one(mpfx const & n) const { return is_pos(n) && is_abs_one(n); }

    /**
       \brief Return true if n is minus one.
    */
    bool is_minus_one(mpfx const & n) const { return is_neg(n) && is_abs_one(n); }

    /**
       \brief Return true if \c a is an integer and fits in an int64 machine integer.
    */
    bool is_int64(mpfx const & a) const;

    /**
       \brief Return true if \c a is a non-negative integer and fits in an int64 machine integer.
    */
    bool is_uint64(mpfx const & a) const;
    
    /**
       \brief Delete the resources associated with n.
    */
    void del(mpfx & n);
    
    /**
       \brief a <- -a
    */
    static void neg(mpfx & a) { if (!is_zero(a)) a.m_sign = !a.m_sign; }

    /**
       \brief a <- |a|
    */
    static void abs(mpfx & a) { a.m_sign = 0; }

    static void swap(mpfx & a, mpfx & b) { a.swap(b); }

    /**
       \brief c <- a + b
    */
    void add(mpfx const & a, mpfx const & b, mpfx & c);

    /**
       \brief c <- a - b
    */
    void sub(mpfx const & a, mpfx const & b, mpfx & c);

    /**
       \brief a <- a + 1
    */
    void inc(mpfx & a) { add(a, m_one, a); }

    /**
       \brief a <- a - 1
    */
    void dec(mpfx & a) { sub(a, m_one, a); }

    /**
       \brief c <- a * b
    */
    void mul(mpfx const & a, mpfx const & b, mpfx & c);

    /**
       \brief c <- a / b
       
       \pre !is_zero(b)
    */
    void div(mpfx const & a, mpfx const & b, mpfx & c);

    /**
       \brief a <- 1/a

       \pre !is_zero(a);
    */
    void inv(mpfx & a) { div(m_one, a, a); }
    void inv(mpfx const & a, mpfx & b) { set(b, a); inv(b); }

    /**
       \brief a <- a/2^k
    */
    void div2k(mpfx & a, unsigned k);
    
    /**
       \brief b <- a/2^k
    */
    void div2k(mpfx const & a, unsigned k, mpfx & b) { set(b, a); div2k(b, k); }

    /**
       \brief a <- a/2
    */
    void div2(mpfx & a) { div2k(a, 1); }

    /**
       \brief b <- a/2
    */
    void div2(mpfx const & a, mpfx & b) { div2k(a, 1, b); }

    /**
       \brief b <- a^k
    */
    void power(mpfx const & a, unsigned k, mpfx & b);
    
    /**
       \brief Return true if \c a is a power of 2. That is, a is equal to 2^k for some k >= 0.
    */
    bool is_power_of_two(mpfx const & a, unsigned & k) const;
    bool is_power_of_two(mpfx const & a) const;
    
    bool eq(mpfx const & a, mpfx const & b) const;
    bool neq(mpfx const & a, mpfx const & b) const { return !eq(a, b); }
    bool lt(mpfx const & a, mpfx const & b) const;
    bool gt(mpfx const & a, mpfx const & b) const { return lt(b, a); }
    bool le(mpfx const & a, mpfx const & b) const { return !lt(b, a); }
    bool ge(mpfx const & a, mpfx const & b) const { return !lt(a, b); }

    void set(mpfx & n, int v);
    void set(mpfx & n, unsigned v);
    void set(mpfx & n, int64 v);
    void set(mpfx & n, uint64 v);
    void set(mpfx & n, int num, unsigned den);
    void set(mpfx & n, int64 num, uint64 den);
    void set(mpfx & n, mpfx const & v);
    void set(mpfx & n, unsynch_mpz_manager & m, mpz const & v);
    void set(mpfx & n, synch_mpz_manager & m, mpz const & v); 
    void set(mpfx & n, unsynch_mpq_manager & m, mpq const & v);
    void set(mpfx & n, synch_mpq_manager & m, mpq const & v);

    /** 
        \brief Set n to the smallest representable numeral greater than zero.
    */
    void set_plus_epsilon(mpfx & n);

    /** 
        \brief Set n to the greatest representable numeral less than zero.
    */
    void set_minus_epsilon(mpfx & n);
    
    /**
       \brief n <- floor(n)
    */
    void floor(mpfx & n);
    void floor(mpfx const & n, mpfx & o) { set(o, n); floor(o); }

    /**
       \brief n <- ceil(n)
    */
    void ceil(mpfx & n);
    void ceil(mpfx const & n, mpfx & o) { set(o, n); ceil(o); }

    /**
       \brief Return n as an int64.

       \pre is_int64(n)
    */
    int64 get_int64(mpfx const & n) const;

    /**
       \brief Return n as an uint64.

       \pre is_uint64(n)
    */
    uint64 get_uint64(mpfx const & n) const;

    /**
       \brief Convert n into a mpz numeral.
       
       \pre is_int(n)
    */
    void to_mpz(mpfx const & n, unsynch_mpz_manager & m, mpz & t);

    /**
       \brief Convert n into a mpz numeral.
       
       \pre is_int(n)
    */
    void to_mpz(mpfx const & n, synch_mpz_manager & m, mpz & t);

    /**
       \brief Convert n into a mpq numeral.
    */
    void to_mpq(mpfx const & n, unsynch_mpq_manager & m, mpq & t);

    /**
       \brief Convert n into a mpq numeral.
    */
    void to_mpq(mpfx const & n, synch_mpq_manager & m, mpq & t);

    /**
       \brief Return the biggest k s.t. 2^k <= a.
       
       \remark Return 0 if a is not positive.
    */
    unsigned prev_power_of_two(mpfx const & a);

    void display(std::ostream & out, mpfx const & n) const;
    void display_pp(std::ostream & out, mpfx const & n) const { display(out, n); }
    void display_smt2(std::ostream & out, mpfx const & n) const;
    void display_decimal(std::ostream & out, mpfx const & n, unsigned prec = UINT_MAX) const;
    void display_raw(std::ostream & out, mpfx const & n) const;

    std::string to_string(mpfx const & a) const;
    std::string to_rational_string(mpfx const & a) const;

    bool check(mpfx const & a) const;
};

typedef _scoped_numeral<mpfx_manager> scoped_mpfx;
typedef _scoped_numeral_vector<mpfx_manager> scoped_mpfx_vector;

#endif
