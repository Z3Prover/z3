/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    mpbq.h

Abstract:

    Binary Rational Numbers

    A binary rational is a number of the form a/2^k.
    All integers are binary rationals.
    Binary rational numbers can be implemented more efficiently than rationals.
    Binary rationals form a Ring. 
    They are not closed under division. 
    In Z3, they are used to implement algebraic numbers.
    The root isolation operations only use division by 2.

Author:

    Leonardo de Moura (leonardo) 2011-11-24.

Revision History:

--*/
#ifndef MPBQ_H_
#define MPBQ_H_

#include "util/mpq.h"
#include "util/rational.h"
#include "util/vector.h"

class mpbq {
    mpz      m_num;
    unsigned m_k;    // we don't need mpz here. 2^(2^32-1) is a huge number, we will not even be able to convert the mpbq into an mpq
    friend class mpbq_manager;
public:
    mpbq():m_num(0), m_k(0) {}
    mpbq(int v):m_num(v), m_k(0) {}
    mpbq(int v, unsigned k):m_num(v), m_k(k) {}
    mpz const & numerator() const { return m_num; }
    unsigned k() const { return m_k; }
    void swap(mpbq & other) { m_num.swap(other.m_num); std::swap(m_k, other.m_k); }
};

inline void swap(mpbq & m1, mpbq & m2) { m1.swap(m2); }

typedef svector<mpbq> mpbq_vector;

class mpbq_manager {
    unsynch_mpz_manager & m_manager;
    mpz                   m_tmp;
    mpz                   m_tmp2;
    mpbq                  m_addmul_tmp;
    mpz                   m_select_int_tmp1;
    mpz                   m_select_int_tmp2;
    mpz                   m_select_small_tmp;
    mpbq                  m_select_small_tmp1;
    mpbq                  m_select_small_tmp2;
    mpz                   m_div_tmp1, m_div_tmp2, m_div_tmp3;
    void normalize(mpbq & a);
    bool select_integer(mpbq const & lower, mpbq const & upper, mpz & r);
    bool select_integer(unsynch_mpq_manager & qm, mpq const & lower, mpbq const & upper, mpz & r);
    bool select_integer(unsynch_mpq_manager & qm, mpbq const & lower, mpq const & upper, mpz & r);
    bool select_integer(unsynch_mpq_manager & qm, mpq const & lower, mpq const & upper, mpz & r);

public:
    static bool precise() { return true; }
    static bool field() { return false; }
    typedef mpbq numeral;

    mpbq_manager(unsynch_mpz_manager & m);
    ~mpbq_manager();

    static void swap(mpbq & a, mpbq & b) { a.swap(b); }

    void del(mpbq & a) { m_manager.del(a.m_num); }
    void reset(mpbq & a) { m_manager.reset(a.m_num); a.m_k = 0; }
    void reset(mpbq_vector & v);
    void set(mpbq & a, int n) { m_manager.set(a.m_num, n); a.m_k = 0; }
    void set(mpbq & a, unsigned n) { m_manager.set(a.m_num, n); a.m_k = 0; }
    void set(mpbq & a, int n, unsigned k) { m_manager.set(a.m_num, n); a.m_k = k; normalize(a); }
    void set(mpbq & a, mpz const & n, unsigned k) { m_manager.set(a.m_num, n); a.m_k = k; normalize(a); }
    void set(mpbq & a, mpz const & n) { m_manager.set(a.m_num, n); a.m_k = 0; }
    void set(mpbq & a, mpbq const & b) { m_manager.set(a.m_num, b.m_num); a.m_k = b.m_k; }
    void set(mpbq & a, int64_t n, unsigned k) { m_manager.set(a.m_num, n); a.m_k = k; normalize(a); }

    bool is_int(mpbq const & a) const { return a.m_k == 0; }
    void get_numerator(mpbq const & a, mpz & n) { m_manager.set(n, a.m_num); }
    unsigned get_denominator_power(mpbq const & a) { return a.m_k; }
    
    bool is_zero(mpbq const & a) const { return m_manager.is_zero(a.m_num); }
    bool is_nonzero(mpbq const & a) const { return !is_zero(a); }
    bool is_one(mpbq const & a) const { return a.m_k == 0 && m_manager.is_one(a.m_num); }
    bool is_pos(mpbq const & a) const { return m_manager.is_pos(a.m_num); }
    bool is_neg(mpbq const & a) const { return m_manager.is_neg(a.m_num); }
    bool is_nonpos(mpbq const & a) const { return m_manager.is_nonpos(a.m_num); }
    bool is_nonneg(mpbq const & a) const { return m_manager.is_nonneg(a.m_num); }

    void add(mpbq const & a, mpbq const & b, mpbq & r);
    void add(mpbq const & a, mpz const & b, mpbq & r);
    void sub(mpbq const & a, mpbq const & b, mpbq & r);
    void sub(mpbq const & a, mpz const & b, mpbq & r);
    void mul(mpbq const & a, mpbq const & b, mpbq & r);
    void mul(mpbq const & a, mpz const & b, mpbq & r);
    // r <- a + b*c
    void addmul(mpbq const & a, mpbq const & b, mpbq const & c, mpbq & r) {
        mul(b, c, m_addmul_tmp);
        add(a, m_addmul_tmp, r);
    }
    void addmul(mpbq const & a, mpz const & b, mpbq const & c, mpbq & r) {
        mul(c, b, m_addmul_tmp);
        add(a, m_addmul_tmp, r);
    }
    void neg(mpbq & a) { m_manager.neg(a.m_num); }
    // when dividing by 2, we only need to normalize if m_k was zero.
    void div2(mpbq & a) { bool old_k_zero = (a.m_k == 0); a.m_k++; if (old_k_zero) normalize(a); }
    void div2k(mpbq & a, unsigned k) { bool old_k_zero = (a.m_k == 0); a.m_k += k; if (old_k_zero) normalize(a); }
    void mul2(mpbq & a);
    void mul2k(mpbq & a, unsigned k);
    void power(mpbq & a, unsigned k);
    void power(mpbq const & a, unsigned k, mpbq & b) { set(b, a); power(b, k); }

    /**
       \brief Return true if a^{1/n} is a binary rational, and store the result in a.
       Otherwise, return false and return an lower bound based on the integer root of the 
       numerator and denominator/n
    */
    bool root_lower(mpbq & a, unsigned n);
    bool root_lower(mpbq const & a, unsigned n, mpbq & r) { set(r, a); return root_lower(r, n); }

    /**
       \brief Return true if a^{1/n} is a binary rational, and store the result in a.
       Otherwise, return false and return an upper bound based on the integer root of the 
       numerator and denominator/n
    */
    bool root_upper(mpbq & a, unsigned n);
    bool root_upper(mpbq const & a, unsigned n, mpbq & r) { set(r, a); return root_upper(r, n); }

    bool eq(mpbq const & a, mpbq const & b) { return a.m_k == b.m_k && m_manager.eq(a.m_num, b.m_num); }
    bool lt(mpbq const & a, mpbq const & b);
    bool neq(mpbq const & a, mpbq const & b) { return !eq(a, b); }
    bool gt(mpbq const & a, mpbq const & b) { return lt(b, a); }
    bool ge(mpbq const & a, mpbq const & b) { return le(b, a); }
    bool le(mpbq const & a, mpbq const & b) { return !gt(a, b); }

    bool eq(mpbq const & a, mpq const & b);
    bool lt(mpbq const & a, mpq const & b);
    bool le(mpbq const & a, mpq const & b);
    bool neq(mpbq const & a, mpq const & b) { return !eq(a, b); }
    bool gt(mpbq const & a, mpq const & b) { return !le(a, b); }
    bool ge(mpbq const & a, mpq const & b) { return !lt(a, b); }

    bool eq(mpbq const & a, mpz const & b) { return m_manager.eq(a.m_num, b) && a.m_k == 0; }
    bool lt(mpbq const & a, mpz const & b);
    bool le(mpbq const & a, mpz const & b);
    bool neq(mpbq const & a, mpz const & b) { return !eq(a, b); }
    bool gt(mpbq const & a, mpz const & b) { return !le(a, b); }
    bool ge(mpbq const & a, mpz const & b) { return !lt(a, b); }

    /**
       \brief Return the magnitude of a = b/2^k.
       It is defined as:
        a == 0 -> 0
        a >  0 -> log2(b) - k          Note that  2^{log2(b) - k}       <= a <=  2^{log2(b) - k + 1}
        a <  0 -> mlog2(b) - k + 1     Note that -2^{mlog2(b) - k + 1}  <= a <= -2^{mlog2(b) - k}

        Remark: mlog2(b) = log2(-b)

        Examples:
        
        5/2^3     log2(5)  - 3      = -1
        21/2^2    log2(21) - 2      =  2
        -3/2^4    log2(3)  - 4  + 1 = -2
    */
    int magnitude_lb(mpbq const & a);

    /**
       \brief Similar to magnitude_lb

        a == 0 -> 0
        a >  0 -> log2(b) - k + 1           a <=  2^{log2(b) - k + 1}
        a <  0 -> mlog2(b) - k              a <= -2^{mlog2(b) - k}
    */
    int magnitude_ub(mpbq const & a);
    
    /**
       \brief Return true if a < 1/2^k
    */
    bool lt_1div2k(mpbq const & a, unsigned k);

    std::string to_string(mpbq const & a);

    /**
       \brief Return true if q (= c/d) is a binary rational,
       and store it in bq (as a binary rational).
       Otherwise return false, and set bq to c/2^{k+1} 
       where k = log2(d)
    */
    bool to_mpbq(mpq const & q, mpbq & bq);

    /**
       \brief Given a rational q which cannot be represented as a binary rational,
       and an interval (l, u) s.t. l < q < u. This method stores in u, a u' s.t.
       q < u' < u.
       In the refinement process, the lower bound l may be also refined to l' 
       s.t. l < l' < q
    */
    void refine_upper(mpq const & q, mpbq & l, mpbq & u);
    
    /**
       \brief Similar to refine_upper.
    */
    void refine_lower(mpq const & q, mpbq & l, mpbq & u);

    template<typename mpz_manager>
    void floor(mpz_manager & m, mpbq const & a, mpz & f) {
        if (is_int(a)) {
            m.set(f, a.m_num);
            return;
        }
        bool is_neg_num = is_neg(a);
        m.machine_div2k(a.m_num, a.m_k, f);
        if (is_neg_num)
            m.sub(f, mpz(1), f);
    }

    template<typename mpz_manager>
    void ceil(mpz_manager & m, mpbq const & a, mpz & c) {
        if (is_int(a)) {
            m.set(c, a.m_num);
            return;
        }
        bool is_pos_num = is_pos(a);
        m.machine_div2k(a.m_num, a.m_k, c);
        if (is_pos_num)
            m.add(c, mpz(1), c);
    }

    /**
       \brief Select some number in the interval [lower, upper].
       Return true if succeeded, and false if lower > upper.
       This method tries to minimize the size (in bits) of r.
       For example, it will select an integer in [lower, upper]
       if the interval contains one.
    */
    bool select_small(mpbq const & lower, mpbq const & upper, mpbq & r);
    /**
       \brief Similar to select_small, but assumes lower <= upper
    */
    void select_small_core(mpbq const & lower, mpbq const & upper, mpbq & r);

    // Select some number in the interval (lower, upper]
    void select_small_core(unsynch_mpq_manager & qm, mpq const & lower, mpbq const & upper, mpbq & r);
    // Select some number in the interval [lower, upper)
    void select_small_core(unsynch_mpq_manager & qm, mpbq const & lower, mpq const & upper, mpbq & r);
    // Select some number in the interval (lower, upper)
    void select_small_core(unsynch_mpq_manager & qm, mpq const & lower, mpq const & upper, mpbq & r);


    void display(std::ostream & out, mpbq const & a);
    void display_pp(std::ostream & out, mpbq const & a);
    void display_decimal(std::ostream & out, mpbq const & a, unsigned prec = 8);
    /**
       \brief Display a in decimal while its digits match b digits.
       This function is useful when a and b are representing an interval [a,b] which
       contains an algebraic number
    */
    void display_decimal(std::ostream & out, mpbq const & a, mpbq const & b, unsigned prec);

    void display_smt2(std::ostream & out, mpbq const & a, bool decimal);

    /**
       \brief Approximate n as b/2^k' s.t. k' <= k.
       
       if get_denominator_power(n) <= k, then n is not modified.
       
       if get_denominator_power(n) > k, then
           if to_plus_inf,   old(n) < b/2^k'
           otherwise,        b/2^k' < old(n)
    */
    void approx(mpbq & n, unsigned k, bool to_plus_inf);

    /**
       \brief Approximated division c <- a/b
       
       The result is precise when:
       1) b is a power of two
       2) get_numerator(b) divides get_numerator(a)

       When the result is not precise, |c - a/b| <= 1/2^k
       Actually, we have that
         to_plus_inf       =>  c - a/b <= 1/2^k
         not to_plus_inf   =>  a/b - c <= 1/2^k
    */
    void approx_div(mpbq const & a, mpbq const & b, mpbq & c, unsigned k=32, bool to_plus_inf=false);
};

/**
   \brief Convert a binary rational into a rational
*/
template<typename mpq_manager>
void to_mpq(mpq_manager & m, mpbq const & source, mpq & target) {
    mpq two(2);
    m.power(two, source.k(), target);
    m.inv(target);
    m.mul(source.numerator(), target, target);
}

/**
   \brief Convert a binary rational into a rational.
*/
rational to_rational(mpbq const & m);

typedef _scoped_numeral<mpbq_manager> scoped_mpbq;
typedef _scoped_numeral_vector<mpbq_manager> scoped_mpbq_vector;


#define MPBQ_MK_COMPARISON_CORE(EXTERNAL, INTERNAL, TYPE)       \
inline bool EXTERNAL(scoped_mpbq const & a, TYPE const & b) {   \
    mpbq_manager & m = a.m();                                   \
    scoped_mpbq _b(m);                                          \
    m.set(_b, b);                                               \
    return m.INTERNAL(a, _b);                                   \
}

#define MPBQ_MK_COMPARISON(EXTERNAL, INTERNAL)       \
MPBQ_MK_COMPARISON_CORE(EXTERNAL, INTERNAL, int)     \
MPBQ_MK_COMPARISON_CORE(EXTERNAL, INTERNAL, mpz)     \

MPBQ_MK_COMPARISON(operator==, eq);
MPBQ_MK_COMPARISON(operator!=, neq);
MPBQ_MK_COMPARISON(operator<,  lt);
MPBQ_MK_COMPARISON(operator<=, le);
MPBQ_MK_COMPARISON(operator>,  gt);
MPBQ_MK_COMPARISON(operator>=, ge);

#undef MPBQ_MK_COMPARISON
#undef MPBQ_MK_COMPARISON_CORE

#define MPBQ_MK_BINARY_CORE(EXTERNAL, INTERNAL, TYPE)                   \
inline scoped_mpbq EXTERNAL(scoped_mpbq const & a, TYPE const & b) {    \
    mpbq_manager & m = a.m();                                           \
    scoped_mpbq _b(m);                                                  \
    m.set(_b, b);                                                       \
    scoped_mpbq r(m);                                                   \
    m.INTERNAL(a, _b, r);                                               \
    return r;                                                           \
}

#define MPBQ_MK_BINARY(EXTERNAL, INTERNAL)        \
MPBQ_MK_BINARY_CORE(EXTERNAL, INTERNAL, int)      \
MPBQ_MK_BINARY_CORE(EXTERNAL, INTERNAL, mpz)      \

MPBQ_MK_BINARY(operator+, add)
MPBQ_MK_BINARY(operator-, sub)
MPBQ_MK_BINARY(operator*, mul)

#undef MPBQ_MK_BINARY
#undef MPBQ_MK_BINARY_CORE

#endif
