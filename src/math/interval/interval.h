/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    interval.h

Abstract:

    Goodies/Templates for interval arithmetic

Author:

    Leonardo de Moura (leonardo) 2012-07-19.

Revision History:

--*/
#ifndef INTERVAL_H_
#define INTERVAL_H_

#include"mpq.h"
#include"ext_numeral.h"

/**
   \brief Default configuration for interval manager.
   It is used for documenting the required interface.
*/
class im_default_config {
    unsynch_mpq_manager &       m_manager;
public:
    typedef unsynch_mpq_manager numeral_manager;
    typedef mpq                 numeral;

    // Every configuration object must provide an interval type.
    // The actual fields are irrelevant, the interval manager
    // accesses interval data using the following API.
    struct interval {
        numeral   m_lower;
        numeral   m_upper;
        unsigned  m_lower_open:1;
        unsigned  m_upper_open:1;
        unsigned  m_lower_inf:1;
        unsigned  m_upper_inf:1;
    };

    // Should be NOOPs for precise numeral types.
    // For imprecise types (e.g., floats) it should set the rounding mode.
    void round_to_minus_inf() {}
    void round_to_plus_inf() {}
    void set_rounding(bool to_plus_inf) {}

    // Getters
    numeral const & lower(interval const & a) const { return a.m_lower; }
    numeral const & upper(interval const & a) const { return a.m_upper; }
    numeral & lower(interval & a) { return a.m_lower; }
    numeral & upper(interval & a) { return a.m_upper; }
    bool lower_is_open(interval const & a) const { return a.m_lower_open; }
    bool upper_is_open(interval const & a) const { return a.m_upper_open; }
    bool lower_is_inf(interval const & a) const { return a.m_lower_inf; }
    bool upper_is_inf(interval const & a) const { return a.m_upper_inf; }

    // Setters
    void set_lower(interval & a, numeral const & n) { m_manager.set(a.m_lower, n); }
    void set_upper(interval & a, numeral const & n) { m_manager.set(a.m_upper, n); }
    void set_lower_is_open(interval & a, bool v) { a.m_lower_open = v; }
    void set_upper_is_open(interval & a, bool v) { a.m_upper_open = v; }
    void set_lower_is_inf(interval & a, bool v) { a.m_lower_inf = v; }
    void set_upper_is_inf(interval & a, bool v) { a.m_upper_inf = v; }
    
    // Reference to numeral manager
    numeral_manager & m() const { return m_manager; }

    im_default_config(numeral_manager & m):m_manager(m) {}
};

#define DEP_IN_LOWER1 1
#define DEP_IN_UPPER1 2
#define DEP_IN_LOWER2 4
#define DEP_IN_UPPER2 8

typedef short bound_deps;
inline bool dep_in_lower1(bound_deps d) { return (d & DEP_IN_LOWER1) != 0; }
inline bool dep_in_lower2(bound_deps d) { return (d & DEP_IN_LOWER2) != 0; }
inline bool dep_in_upper1(bound_deps d) { return (d & DEP_IN_UPPER1) != 0; }
inline bool dep_in_upper2(bound_deps d) { return (d & DEP_IN_UPPER2) != 0; }
inline bound_deps dep1_to_dep2(bound_deps d) { 
    SASSERT(!dep_in_lower2(d) && !dep_in_upper2(d));
    bound_deps r = d << 2; 
    SASSERT(dep_in_lower1(d) == dep_in_lower2(r));
    SASSERT(dep_in_upper1(d) == dep_in_upper2(r));
    SASSERT(!dep_in_lower1(r) && !dep_in_upper1(r));
    return r;
}

/**
   \brief Interval dependencies for unary and binary operations on intervals.
   It contains the dependencies for the output lower and upper bounds 
   for the resultant interval.
*/ 
struct interval_deps {
    bound_deps m_lower_deps;
    bound_deps m_upper_deps;
};

template<typename C>
class interval_manager {
public:
    typedef typename C::numeral_manager       numeral_manager;
    typedef typename numeral_manager::numeral numeral;
    typedef typename C::interval              interval;
private:
    C          m_c;
    numeral    m_result_lower;
    numeral    m_result_upper;
    numeral    m_mul_ad;
    numeral    m_mul_bc;
    numeral    m_mul_ac;
    numeral    m_mul_bd;
    numeral    m_one;
    numeral    m_minus_one;
    numeral    m_inv_k;

    unsigned   m_pi_n;
    interval   m_pi_div_2;
    interval   m_pi;
    interval   m_3_pi_div_2;
    interval   m_2_pi;

    volatile bool m_cancel;     
    
    void round_to_minus_inf() { m_c.round_to_minus_inf(); }
    void round_to_plus_inf() { m_c.round_to_plus_inf(); }
    void set_rounding(bool to_plus_inf) { m_c.set_rounding(to_plus_inf); }

    ext_numeral_kind lower_kind(interval const & a) const { return m_c.lower_is_inf(a) ? EN_MINUS_INFINITY : EN_NUMERAL; }
    ext_numeral_kind upper_kind(interval const & a) const { return m_c.upper_is_inf(a) ? EN_PLUS_INFINITY : EN_NUMERAL; }

    void set_lower(interval & a, numeral const & n) { m_c.set_lower(a, n); }
    void set_upper(interval & a, numeral const & n) { m_c.set_upper(a, n); }
    void set_lower_is_open(interval & a, bool v) { m_c.set_lower_is_open(a, v); }
    void set_upper_is_open(interval & a, bool v) { m_c.set_upper_is_open(a, v); }
    void set_lower_is_inf(interval & a, bool v) { m_c.set_lower_is_inf(a, v); }
    void set_upper_is_inf(interval & a, bool v) { m_c.set_upper_is_inf(a, v); }

    void nth_root_slow(numeral const & a, unsigned n, numeral const & p, numeral & lo, numeral & hi);
    void A_div_x_n(numeral const & A, numeral const & x, unsigned n, bool to_plus_inf, numeral & r);
    void rough_approx_nth_root(numeral const & a, unsigned n, numeral & o);
    void approx_nth_root(numeral const & a, unsigned n, numeral const & p, numeral & o);
    void nth_root_pos(numeral const & A, unsigned n, numeral const & p, numeral & lo, numeral & hi);
    void nth_root(numeral const & a, unsigned n, numeral const & p, numeral & lo, numeral & hi);
    
    void pi_series(int x, numeral & r, bool to_plus_inf);
    void fact(unsigned n, numeral & o);
    void sine_series(numeral const & a, unsigned k, bool upper, numeral & o);
    void cosine_series(numeral const & a, unsigned k, bool upper, numeral & o);
    void e_series(unsigned k, bool upper, numeral & o);

    void div_mul(numeral const & k, interval const & a, interval & b, bool inv_k);

    void checkpoint();

public:    
    interval_manager(C const & c);
    ~interval_manager();

    void set_cancel(bool f) { m_cancel = f; }

    numeral_manager & m() const { return m_c.m(); }    

    void del(interval & a);

    numeral const & lower(interval const & a) const { return m_c.lower(a); }
    numeral const & upper(interval const & a) const { return m_c.upper(a); }
    numeral & lower(interval & a) { return m_c.lower(a); }
    numeral & upper(interval & a) { return m_c.upper(a); }
    bool lower_is_open(interval const & a) const { return m_c.lower_is_open(a); }
    bool upper_is_open(interval const & a) const { return m_c.upper_is_open(a); }
    bool lower_is_inf(interval const & a) const { return m_c.lower_is_inf(a); }
    bool upper_is_inf(interval const & a) const { return m_c.upper_is_inf(a); }
    
    bool lower_is_neg(interval const & a) const { return ::is_neg(m(), lower(a), lower_kind(a)); }
    bool lower_is_pos(interval const & a) const { return ::is_pos(m(), lower(a), lower_kind(a)); }
    bool lower_is_zero(interval const & a) const { return ::is_zero(m(), lower(a), lower_kind(a)); }

    bool upper_is_neg(interval const & a) const { return ::is_neg(m(), upper(a), upper_kind(a)); }
    bool upper_is_pos(interval const & a) const { return ::is_pos(m(), upper(a), upper_kind(a)); }
    bool upper_is_zero(interval const & a) const { return ::is_zero(m(), upper(a), upper_kind(a)); }

    bool is_P(interval const & n) const { return lower_is_pos(n) || lower_is_zero(n); }
    bool is_P0(interval const & n) const { return lower_is_zero(n) && !lower_is_open(n); }
    bool is_P1(interval const & n) const { return lower_is_pos(n) || (lower_is_zero(n) && lower_is_open(n)); }
    bool is_N(interval const & n) const { return upper_is_neg(n) || upper_is_zero(n); }
    bool is_N0(interval const & n) const { return upper_is_zero(n) && !upper_is_open(n); }
    bool is_N1(interval const & n) const { return upper_is_neg(n) || (upper_is_zero(n) && upper_is_open(n)); }
    bool is_M(interval const & n) const { return lower_is_neg(n) && upper_is_pos(n); }
    bool is_zero(interval const & n) const { return lower_is_zero(n) && upper_is_zero(n); }

    void set(interval & t, interval const & s);

    bool eq(interval const & a, interval const & b) const;

    /**
       \brief Return true if all values in 'a' are less than all values in 'b'.
    */
    bool before(interval const & a, interval const & b) const;

    /**
       \brief Set lower bound to -oo.
    */
    void reset_lower(interval & a);

    /**
       \brief Set upper bound to +oo.
    */
    void reset_upper(interval & a);

    /**
       \brief Set interval to (-oo, oo)
    */
    void reset(interval & a);

    /**
       \brief Return true if the given interval contains 0.
    */
    bool contains_zero(interval const & n) const;
    
    /**
       \brief Return true if n contains v.
    */
    bool contains(interval const & n, numeral const & v) const;
    
    void display(std::ostream & out, interval const & n) const;
    void display_pp(std::ostream & out, interval const & n) const;

    bool check_invariant(interval const & n) const;

    /**
       \brief b <- -a
    */
    void neg(interval const & a, interval & b, interval_deps & b_deps);
    void neg(interval const & a, interval & b);
    void neg_jst(interval const & a, interval_deps & b_deps);

    /**
       \brief c <- a + b
    */
    void add(interval const & a, interval const & b, interval & c, interval_deps & c_deps);
    void add(interval const & a, interval const & b, interval & c);
    void add_jst(interval const & a, interval const & b, interval_deps & c_deps);

    /**
       \brief c <- a - b
    */
    void sub(interval const & a, interval const & b, interval & c, interval_deps & c_deps);
    void sub(interval const & a, interval const & b, interval & c);
    void sub_jst(interval const & a, interval const & b, interval_deps & c_deps);

    /**
       \brief b <- k * a
    */
    void mul(numeral const & k, interval const & a, interval & b, interval_deps & b_deps);
    void mul(numeral const & k, interval const & a, interval & b) { div_mul(k, a, b, false); }
    void mul_jst(numeral const & k, interval const & a, interval_deps & b_deps);
    /**
       \brief b <- (n/d) * a
    */
    void mul(int n, int d, interval const & a, interval & b);

    /**
       \brief b <- a/k
       
       \remark For imprecise numerals, this is not equivalent to 
       m().inv(k)
       mul(k, a, b)
    
       That is, we must invert k rounding towards +oo or -oo depending whether we
       are computing a lower or upper bound.
    */
    void div(interval const & a, numeral const & k, interval & b, interval_deps & b_deps);
    void div(interval const & a, numeral const & k, interval & b) { div_mul(k, a, b, true); }
    void div_jst(interval const & a, numeral const & k, interval_deps & b_deps) { mul_jst(k, a, b_deps); }

    /**
       \brief c <- a * b
    */
    void mul(interval const & a, interval const & b, interval & c, interval_deps & c_deps);
    void mul(interval const & a, interval const & b, interval & c);
    void mul_jst(interval const & a, interval const & b, interval_deps & c_deps);

    /**
       \brief b <- a^n
    */
    void power(interval const & a, unsigned n, interval & b, interval_deps & b_deps);
    void power(interval const & a, unsigned n, interval & b);
    void power_jst(interval const & a, unsigned n, interval_deps & b_deps);

    /**
       \brief b <- a^(1/n) with precision p.

       \pre if n is even, then a must not contain negative numbers.
    */
    void nth_root(interval const & a, unsigned n, numeral const & p, interval & b, interval_deps & b_deps);
    void nth_root(interval const & a, unsigned n, numeral const & p, interval & b);
    void nth_root_jst(interval const & a, unsigned n, numeral const & p, interval_deps & b_deps);
    
    /**
       \brief Given an equation x^n = y and an interval for y, compute the solution set for x with precision p.
       
       \pre if n is even, then !lower_is_neg(y)
    */
    void xn_eq_y(interval const & y, unsigned n, numeral const & p, interval & x, interval_deps & x_deps);
    void xn_eq_y(interval const & y, unsigned n, numeral const & p, interval & x); 
    void xn_eq_y_jst(interval const & y, unsigned n, numeral const & p, interval_deps & x_deps);
   
    /**
       \brief b <- 1/a
       \pre !contains_zero(a)
    */
    void inv(interval const & a, interval & b, interval_deps & b_deps);
    void inv(interval const & a, interval & b);
    void inv_jst(interval const & a, interval_deps & b_deps);

    /**
       \brief c <- a/b
       \pre !contains_zero(b)
       \pre &a == &c (that is, c should not be an alias for a)
    */
    void div(interval const & a, interval const & b, interval & c, interval_deps & c_deps);
    void div(interval const & a, interval const & b, interval & c);
    void div_jst(interval const & a, interval const & b, interval_deps & c_deps);
    
    /**
       \brief Store in r an interval that contains the number pi.
       The size of the interval is (1/15)*(1/16^n)
    */
    void pi(unsigned n, interval & r);

    /**
       \brief Set the precision of the internal interval representing pi.
    */
    void set_pi_prec(unsigned n);

    /**
       \brief Set the precision of the internal interval representing pi to a precision of at least n.
    */
    void set_pi_at_least_prec(unsigned n);

    void sine(numeral const & a, unsigned k, numeral & lo, numeral & hi);

    void cosine(numeral const & a, unsigned k, numeral & lo, numeral & hi);

    /**
       \brief Store in r the Euler's constant e.
       The size of the interval is 4/(k+1)!
    */
    void e(unsigned k, interval & r);
};

template<typename Manager>
class _scoped_interval {
public:
    typedef typename Manager::interval interval;
private:
    Manager & m_manager;
    interval  m_interval;
public:
    _scoped_interval(Manager & m):m_manager(m) {}
    ~_scoped_interval() { m_manager.del(m_interval); }
    
    Manager & m() const { return m_manager; }

    operator interval const &() const { return m_interval; }
    operator interval&() { return m_interval; }
    interval const & get() const { return m_interval; }
    interval & get() { return m_interval; }
    interval * operator->() {
        return &m_interval;
    }
    interval const * operator->() const {
        return &m_interval;
    }
};

#endif
