/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    interval_def.h

Abstract:

    Goodies/Templates for interval arithmetic

Author:

    Leonardo de Moura (leonardo) 2012-07-19.

Revision History:

--*/
#ifndef INTERVAL_DEF_H_
#define INTERVAL_DEF_H_

#include"interval.h"
#include"debug.h"
#include"trace.h"
#include"scoped_numeral.h"
#include"cooperate.h"

#define DEFAULT_PI_PRECISION 2

// #define TRACE_NTH_ROOT

template<typename C>
interval_manager<C>::interval_manager(reslimit& lim, C const & c): m_limit(lim), m_c(c) { 
    m().set(m_minus_one, -1); 
    m().set(m_one, 1);
    m_pi_n = 0;
}

template<typename C>
interval_manager<C>::~interval_manager() {
    del(m_pi_div_2);
    del(m_pi);
    del(m_3_pi_div_2);
    del(m_2_pi);
    m().del(m_result_lower);
    m().del(m_result_upper);
    m().del(m_mul_ad);
    m().del(m_mul_bc);
    m().del(m_mul_ac);
    m().del(m_mul_bd);
    m().del(m_minus_one);
    m().del(m_one);
    m().del(m_inv_k);
}

template<typename C>
void interval_manager<C>::del(interval & a) {
    m().del(lower(a));
    m().del(upper(a));
}


template<typename C>
void interval_manager<C>::checkpoint() {
    if (!m_limit.inc())
        throw default_exception("canceled");
    cooperate("interval");
}

/*
  Compute the n-th root of a with precision p. The result hi - lo <= p
  lo and hi are lower/upper bounds for the value of the n-th root of a.
  That is, the n-th root is in the interval [lo, hi]

  If n is even, then a is assumed to be nonnegative.

  If numeral_manager is not precise, the procedure does not guarantee the precision p.
*/
template<typename C>
void interval_manager<C>::nth_root_slow(numeral const & a, unsigned n, numeral const & p, numeral & lo, numeral & hi) {
#ifdef TRACE_NTH_ROOT
    static unsigned counter = 0;
    static unsigned loop_counter = 0;
    counter++;
    if (counter % 1000 == 0) 
        std::cerr << "[nth-root] " << counter << " " << loop_counter << " " << ((double)loop_counter)/((double)counter) << std::endl;
#endif

    bool n_is_even = (n % 2 == 0);
    SASSERT(!n_is_even || m().is_nonneg(a));
    if (m().is_zero(a) || m().is_one(a) || (!n_is_even && m().eq(a, m_minus_one))) {
        m().set(lo, a);
        m().set(hi, a);
        return;
    }
    if (m().lt(a, m_minus_one)) {
        m().set(lo, a);
        m().set(hi, -1);
    }
    else if (m().is_neg(a)) {
        m().set(lo, -1);
        m().set(hi, 0);
    }
    else if (m().lt(a, m_one)) {
        m().set(lo, 0);
        m().set(hi, 1);
    }
    else {
        m().set(lo, 1);
        m().set(hi, a);
    }
    SASSERT(m().le(lo, hi));
    _scoped_numeral<numeral_manager> c(m()), cn(m());
    _scoped_numeral<numeral_manager> two(m());
    m().set(two, 2);
    while (true) {
        checkpoint();
#ifdef TRACE_NTH_ROOT
        loop_counter++;
#endif
        m().add(hi, lo, c);
        m().div(c, two, c);
        if (m().precise()) {
            m().power(c, n, cn);
            if (m().gt(cn, a)) {
                m().set(hi, c);
            }
            else if (m().eq(cn, a)) {
                // root is precise
                m().set(lo, c);
                m().set(hi, c);
                return;
            }
            else {
                m().set(lo, c);
            }
        }
        else {
            round_to_minus_inf();
            m().power(c, n, cn);
            if (m().gt(cn, a)) {
                m().set(hi, c);
            }
            else {
                round_to_plus_inf();
                m().power(c, n, cn);
                if (m().lt(cn, a)) {
                    m().set(lo, c);
                }
                else {
                    // can't improve, numeral_manager is not precise enough,
                    // a is between round-to-minus-inf(c^n) and round-to-plus-inf(c^n)
                    return;
                }
            }
        }
        round_to_plus_inf();
        m().sub(hi, lo, c);
        if (m().le(c, p))
            return; // result is precise enough
    }
}

/**
   \brief Store in o a rough approximation of a^1/n.
   
   It uses 2^Floor[Floor(Log2(a))/n]

   \pre is_pos(a)
*/
template<typename C>
void interval_manager<C>::rough_approx_nth_root(numeral const & a, unsigned n, numeral & o) {
    SASSERT(m().is_pos(a));
    SASSERT(n > 0);
    round_to_minus_inf();
    unsigned k = m().prev_power_of_two(a);
    m().set(o, 2);
    m().power(o, k/n, o);
}

/*
  Compute the n-th root of \c a with (suggested) precision p. 
  The only guarantee provided by this method is that a^(1/n) is in [lo, hi].

  If n is even, then a is assumed to be nonnegative.
*/
template<typename C>
void interval_manager<C>::nth_root(numeral const & a, unsigned n, numeral const & p, numeral & lo, numeral & hi) {
    // nth_root_slow(a, n, p, lo, hi);
    // return;
    SASSERT(n > 0);
    SASSERT(n % 2 != 0 || m().is_nonneg(a));
    if (n == 1 || m().is_zero(a) || m().is_one(a) || m().is_minus_one(a)) {
        // easy cases: 1, -1, 0
        m().set(lo, a);
        m().set(hi, a);
        return;
    }
    bool is_neg = m().is_neg(a);
    _scoped_numeral<numeral_manager> A(m());
    m().set(A, a);
    m().abs(A);

    nth_root_pos(A, n, p, lo, hi);
    STRACE("nth_root_trace", 
           tout << "[nth-root] ("; m().display(tout, A); tout << ")^(1/" << n << ") >= "; m().display(tout, lo); tout << "\n"; 
           tout << "[nth-root] ("; m().display(tout, A); tout << ")^(1/" << n << ") <= "; m().display(tout, hi); tout << "\n";);
    if (is_neg) {
        m().swap(lo, hi);
        m().neg(lo);
        m().neg(hi);
    }
}

/**
   r <- A/(x^n)
   
   If to_plus_inf,      then r >= A/(x^n)
   If not to_plus_inf,  then r <= A/(x^n)

*/
template<typename C>
void interval_manager<C>::A_div_x_n(numeral const & A, numeral const & x, unsigned n, bool to_plus_inf, numeral & r) {
    if (n == 1) {
        if (m().precise()) {
            m().div(A, x, r);
        }
        else {
            set_rounding(to_plus_inf);
            m().div(A, x, r);
        }
    }
    else {
        if (m().precise()) {
            m().power(x, n, r);
            m().div(A, r, r);
        }
        else {
            set_rounding(!to_plus_inf);
            m().power(x, n, r);
            set_rounding(to_plus_inf);
            m().div(A, r, r);
        }
    }
}

/**
   \brief Compute an approximation of A^(1/n) using the sequence

   x' = 1/n((n-1)*x + A/(x^(n-1)))

   The computation stops when the difference between current and new x is less than p.
   The procedure may not terminate if m() is not precise and p is very small.
   
*/
template<typename C>
void interval_manager<C>::approx_nth_root(numeral const & A, unsigned n, numeral const & p, numeral & x) {
    SASSERT(m().is_pos(A));
    SASSERT(n > 1);
#ifdef TRACE_NTH_ROOT
    static unsigned counter = 0;
    static unsigned loop_counter = 0;
    counter++;
    if (counter % 1000 == 0) 
        std::cerr << "[nth-root] " << counter << " " << loop_counter << " " << ((double)loop_counter)/((double)counter) << std::endl;
#endif
    
    _scoped_numeral<numeral_manager> x_prime(m()), d(m());
    
    m().set(d, 1);
    if (m().lt(A, d)) 
        m().set(x, A);
    else
        rough_approx_nth_root(A, n, x);
    
    round_to_minus_inf();

    if (n == 2) {
        _scoped_numeral<numeral_manager> two(m());
        m().set(two, 2);
        while (true) {
            checkpoint();
#ifdef TRACE_NTH_ROOT
            loop_counter++;
#endif
            m().div(A, x, x_prime);
            m().add(x, x_prime, x_prime);
            m().div(x_prime, two, x_prime);
            m().sub(x_prime, x, d);
            m().abs(d);
            m().swap(x, x_prime);
            if (m().lt(d, p))
                return;
        }
    }
    else {
        _scoped_numeral<numeral_manager> _n(m()), _n_1(m());
        m().set(_n, n);   // _n contains n
        m().set(_n_1, n);
        m().dec(_n_1);    // _n_1 contains n-1 
        
        while (true) {
            checkpoint();
#ifdef TRACE_NTH_ROOT
            loop_counter++;
#endif
            m().power(x, n-1, x_prime);
            m().div(A, x_prime, x_prime);
            m().mul(_n_1, x, d);
            m().add(d, x_prime, x_prime);
            m().div(x_prime, _n, x_prime);
            m().sub(x_prime, x, d);
            m().abs(d);
            TRACE("nth_root", 
                  tout << "A:       "; m().display(tout, A); tout << "\n";
                  tout << "x:       "; m().display(tout, x); tout << "\n";
                  tout << "x_prime: "; m().display(tout, x_prime); tout << "\n";
                  tout << "d:       "; m().display(tout, d); tout << "\n";
                  );
            m().swap(x, x_prime);
            if (m().lt(d, p))
                return;
        }
    }
}

template<typename C>
void interval_manager<C>::nth_root_pos(numeral const & A, unsigned n, numeral const & p, numeral & lo, numeral & hi) {
    approx_nth_root(A, n, p, hi);
    if (m().precise()) {
        // Assuming hi has a upper bound for A^(n-1)
        // Then, A/(x^(n-1)) must be lower bound
        A_div_x_n(A, hi, n-1, false, lo);
        // Check if we were wrong
        if (m().lt(hi, lo)) {
            // swap if wrong
            m().swap(lo, hi);
        }
    }
    else {
        // Check if hi is really a upper bound for A^(n-1)
        A_div_x_n(A, hi, n-1, true /* lo will be greater than the actual lower bound */, lo);
        TRACE("nth_root_bug", 
              tout << "Assuming upper\n";
              tout << "A: "; m().display(tout, A); tout << "\n";
              tout << "hi: "; m().display(tout, hi); tout << "\n";
              tout << "lo: "; m().display(tout, hi); tout << "\n";);
        if (m().le(lo, hi)) {
            // hi is really the upper bound
            // Must compute lo again but approximating to -oo
            A_div_x_n(A, hi, n-1, false, lo);
        }
        else {
            // hi should be lower bound
            m().swap(lo, hi);
            // check if lo is lower bound
            A_div_x_n(A, lo, n-1, false /* hi will less than the actual upper bound */, hi);
            if (m().le(lo, hi)) {
                // lo is really the lower bound
                // Must compute hi again but approximating to +oo
                A_div_x_n(A, lo, n-1, true, hi);
            }
            else {
                // we don't have anything due to rounding errors
                // Be supper conservative
                // This should not really happen very often.
                _scoped_numeral<numeral_manager> one(m());
                if (m().lt(A, one)) {
                    m().set(lo, 0);
                    m().set(hi, 1);
                }
                else {
                    m().set(lo, 1);
                    m().set(hi, A);
                }
            }
        }
    }
}


/**
   \brief o <- n!
*/
template<typename C>
void interval_manager<C>::fact(unsigned n, numeral & o) {
    _scoped_numeral<numeral_manager> aux(m());
    m().set(o, 1);
    for (unsigned i = 2; i <= n; i++) {
        m().set(aux, static_cast<int>(i));
        m().mul(aux, o, o);
        TRACE("fact_bug", tout << "i: " << i << ", o: " << m().to_rational_string(o) << "\n";);
    }
}

template<typename C>
void interval_manager<C>::sine_series(numeral const & a, unsigned k, bool upper, numeral & o) {
    SASSERT(k % 2 == 1);
    // Compute sine using taylor series up to k
    // x - x^3/3! + x^5/5! - x^7/7! + ... 
    // The result should be greater than or equal to the actual value if upper == true
    // Otherwise it must be less than or equal to the actual value.
    // The argument upper only matter if the numeral_manager is not precise.

    // Taylor series up to k with rounding to 
    _scoped_numeral<numeral_manager> f(m());
    _scoped_numeral<numeral_manager> aux(m());
    m().set(o, a);
    bool sign         = true;
    bool upper_factor = !upper; // since the first sign is negative, we must minimize factor to maximize result
    for (unsigned i = 3; i <= k; i+=2) {
        TRACE("sine_bug", tout << "[begin-loop] o: " << m().to_rational_string(o) << "\ni: " << i << "\n";
              tout << "upper: " << upper << ", upper_factor: " << upper_factor << "\n";
              tout << "o (default): " << m().to_string(o) << "\n";);
        set_rounding(upper_factor); 
        m().power(a, i, f);
        TRACE("sine_bug", tout << "a^i " << m().to_rational_string(f) << "\n";);
        set_rounding(!upper_factor);
        fact(i, aux);
        TRACE("sine_bug", tout << "i! " << m().to_rational_string(aux) << "\n";);
        set_rounding(upper_factor);
        m().div(f, aux, f);
        TRACE("sine_bug", tout << "a^i/i! " << m().to_rational_string(f) << "\n";);
        set_rounding(upper);
        if (sign)
            m().sub(o, f, o);
        else
            m().add(o, f, o);
        TRACE("sine_bug", tout << "o: " << m().to_rational_string(o) << "\n";);
        sign         = !sign;
        upper_factor = !upper_factor;
    }
}

template<typename C>
void interval_manager<C>::sine(numeral const & a, unsigned k, numeral & lo, numeral & hi) {
    TRACE("sine", tout << "sine(a), a: " << m().to_rational_string(a) << "\na: " << m().to_string(a) << "\n";);
    SASSERT(&lo != &hi);
    if (m().is_zero(a)) {
        m().reset(lo);
        m().reset(hi);
        return;
    }
    
    // Compute sine using taylor series
    // x - x^3/3! + x^5/5! - x^7/7! + ...
    //
    // Note that, the coefficient of even terms is 0.
    // So, we force k to be odd to make sure the error is minimized.
    if (k % 2 == 0)
        k++; 
    
    // Taylor series error = |x|^(k+1)/(k+1)!
    _scoped_numeral<numeral_manager> error(m());
    _scoped_numeral<numeral_manager> aux(m());
    round_to_plus_inf();
    m().set(error, a);
    if (m().is_neg(error))
        m().neg(error);
    m().power(error, k+1, error);
    TRACE("sine", tout << "a^(k+1): " << m().to_rational_string(error) << "\nk : " << k << "\n";);
    round_to_minus_inf();
    fact(k+1, aux);
    TRACE("sine", tout << "(k+1)!: " << m().to_rational_string(aux) << "\n";);
    round_to_plus_inf();
    m().div(error, aux, error);
    TRACE("sine", tout << "error: " << m().to_rational_string(error) << "\n";);

    // Taylor series up to k with rounding to -oo 
    sine_series(a, k, false, lo);

    if (m().precise()) {
        m().set(hi, lo);
        m().sub(lo, error, lo);
        if (m().lt(lo, m_minus_one)) {
            m().set(lo, -1);
            m().set(hi, 1);
        }
        else {
            m().add(hi, error, hi);
        }
    }
    else {
        // We must recompute the series with rounding to +oo
        TRACE("sine", tout << "lo before -error: " << m().to_rational_string(lo) << "\n";);
        round_to_minus_inf();
        m().sub(lo, error, lo);
        TRACE("sine", tout << "lo: " << m().to_rational_string(lo) << "\n";);
        if (m().lt(lo, m_minus_one)) {
            m().set(lo, -1);
            m().set(hi, 1);
            return;
        }
        sine_series(a, k, true, hi);
        round_to_plus_inf();
        m().add(hi, error, hi);
        TRACE("sine", tout << "hi: " << m().to_rational_string(hi) << "\n";);
    }
}

template<typename C>
void interval_manager<C>::cosine_series(numeral const & a, unsigned k, bool upper, numeral & o) {
    SASSERT(k % 2 == 0);
    // Compute cosine using taylor series up to k
    // 1 - x^2/2! + x^4/4! - x^6/6! + ...
    // The result should be greater than or equal to the actual value if upper == true
    // Otherwise it must be less than or equal to the actual value.
    // The argument upper only matter if the numeral_manager is not precise.


    // Taylor series up to k with rounding to -oo 
    _scoped_numeral<numeral_manager> f(m());
    _scoped_numeral<numeral_manager> aux(m());
    m().set(o, 1);
    bool sign         = true;
    bool upper_factor = !upper; // since the first sign is negative, we must minimize factor to maximize result
    for (unsigned i = 2; i <= k; i+=2) {
        set_rounding(upper_factor);
        m().power(a, i, f);
        set_rounding(!upper_factor);
        fact(i, aux);
        set_rounding(upper_factor);
        m().div(f, aux, f);
        set_rounding(upper);
        if (sign)
            m().sub(o, f, o);
        else
            m().add(o, f, o);
        sign         = !sign;
        upper_factor = !upper_factor; 
    }
}

template<typename C>
void interval_manager<C>::cosine(numeral const & a, unsigned k, numeral & lo, numeral & hi) {
    TRACE("cosine", tout << "cosine(a): "; m().display_decimal(tout, a, 32); tout << "\n";);
    SASSERT(&lo != &hi);
    if (m().is_zero(a)) {
        m().set(lo, 1);
        m().set(hi, 1);
        return;
    }
    
    // Compute cosine using taylor series
    // 1 - x^2/2! + x^4/4! - x^6/6! + ...
    //
    // Note that, the coefficient of odd terms is 0.
    // So, we force k to be even to make sure the error is minimized.
    if (k % 2 == 1)
        k++; 
    
    // Taylor series error = |x|^(k+1)/(k+1)!
    _scoped_numeral<numeral_manager> error(m());
    _scoped_numeral<numeral_manager> aux(m());
    round_to_plus_inf();
    m().set(error, a);
    if (m().is_neg(error))
        m().neg(error);
    m().power(error, k+1, error);
    round_to_minus_inf();
    fact(k+1, aux);
    round_to_plus_inf();
    m().div(error, aux, error);
    TRACE("sine", tout << "error: "; m().display_decimal(tout, error, 32); tout << "\n";);

    // Taylor series up to k with rounding to -oo 
    cosine_series(a, k, false, lo);
    
    if (m().precise()) {
        m().set(hi, lo);
        m().sub(lo, error, lo);
        if (m().lt(lo, m_minus_one)) {
            m().set(lo, -1);
            m().set(hi, 1);
        }
        else {
            m().add(hi, error, hi);
        }
    }
    else {
        // We must recompute the series with rounding to +oo
        round_to_minus_inf();
        m().sub(lo, error, lo);
        if (m().lt(lo, m_minus_one)) {
            m().set(lo, -1);
            m().set(hi, 1);
            return;
        }
        cosine_series(a, k, true, hi);
        round_to_plus_inf();
        m().add(hi, error, hi);
    }
}

template<typename C>
void interval_manager<C>::reset_lower(interval & a) {
    m().reset(lower(a));
    set_lower_is_open(a, true);
    set_lower_is_inf(a, true);
}

template<typename C>
void interval_manager<C>::reset_upper(interval & a) {
    m().reset(upper(a));
    set_upper_is_open(a, true);
    set_upper_is_inf(a, true);
}

template<typename C>
void interval_manager<C>::reset(interval & a) {
    reset_lower(a);
    reset_upper(a);
}

template<typename C>
bool interval_manager<C>::contains_zero(interval const & n) const {
    return 
        (lower_is_neg(n) || (lower_is_zero(n) && !lower_is_open(n))) &&
        (upper_is_pos(n) || (upper_is_zero(n) && !upper_is_open(n)));
}

    
template<typename C>
bool interval_manager<C>::contains(interval const & n, numeral const & v) const {
    if (!lower_is_inf(n)) {
        if (m().lt(v, lower(n))) return false;
        if (m().eq(v, lower(n)) && lower_is_open(n)) return false;
    }
    if (!upper_is_inf(n)) {
        if (m().gt(v, upper(n))) return false;
        if (m().eq(v, upper(n)) && upper_is_open(n)) return false;
    }
    return true;
}

template<typename C>
void interval_manager<C>::display(std::ostream & out, interval const & n) const {
    out << (lower_is_open(n) ? "(" : "[");
    ::display(out, m(), lower(n), lower_kind(n));
    out << ", ";
    ::display(out, m(), upper(n), upper_kind(n));
    out << (upper_is_open(n) ? ")" : "]");
}

template<typename C>
void interval_manager<C>::display_pp(std::ostream & out, interval const & n) const {
    out << (lower_is_open(n) ? "(" : "[");
    ::display_pp(out, m(), lower(n), lower_kind(n));
    out << ", ";
    ::display_pp(out, m(), upper(n), upper_kind(n));
    out << (upper_is_open(n) ? ")" : "]");
}

template<typename C>
bool interval_manager<C>::check_invariant(interval const & n) const {
    if (::eq(m(), lower(n), lower_kind(n), upper(n), upper_kind(n))) {
        SASSERT(!lower_is_open(n));
        SASSERT(!upper_is_open(n));
    }
    else {
        SASSERT(lt(m(), lower(n), lower_kind(n), upper(n), upper_kind(n)));
    }
    return true;
}

template<typename C>
void interval_manager<C>::set(interval & t, interval const & s) {
    if (&t == &const_cast<interval&>(s))
        return;
    if (lower_is_inf(s)) {
        set_lower_is_inf(t, true);
    }
    else {
        m().set(lower(t), lower(s));
        set_lower_is_inf(t, false);
    }
    if (upper_is_inf(s)) {
        set_upper_is_inf(t, true);
    }
    else {
        m().set(upper(t), upper(s));
        set_upper_is_inf(t, false);
    }
    set_lower_is_open(t, lower_is_open(s));
    set_upper_is_open(t, upper_is_open(s));
    SASSERT(check_invariant(t));
}

template<typename C>
bool interval_manager<C>::eq(interval const & a, interval const & b) const {
    return 
        ::eq(m(), lower(a), lower_kind(a), lower(b), lower_kind(b)) &&
        ::eq(m(), upper(a), upper_kind(a), upper(b), upper_kind(b)) &&
        lower_is_open(a) == lower_is_open(b) &&
        upper_is_open(a) == upper_is_open(b);
}

template<typename C>
bool interval_manager<C>::before(interval const & a, interval const & b) const {
    if (upper_is_inf(a) || lower_is_inf(b))
        return false;
    return m().lt(upper(a), lower(b)) || (upper_is_open(a) && m().eq(upper(a), lower(b)));
}

template<typename C>
void interval_manager<C>::neg_jst(interval const & a, interval_deps & b_deps) {
    if (lower_is_inf(a)) {
        if (upper_is_inf(a)) {
            b_deps.m_lower_deps = 0;
            b_deps.m_upper_deps = 0;
        }
        else {
            b_deps.m_lower_deps = DEP_IN_UPPER1;
            b_deps.m_upper_deps = 0;
        }
    }
    else {
        if (upper_is_inf(a)) {
            b_deps.m_lower_deps = 0;
            b_deps.m_upper_deps = DEP_IN_LOWER1;
        }
        else {
            b_deps.m_lower_deps = DEP_IN_UPPER1;
            b_deps.m_upper_deps = DEP_IN_LOWER1;
        }
    }
}

template<typename C>
void interval_manager<C>::neg(interval const & a, interval & b, interval_deps & b_deps) {
    neg_jst(a, b_deps);
    neg(a, b);
}

template<typename C>
void interval_manager<C>::neg(interval const & a, interval & b) {
    if (lower_is_inf(a)) {
        if (upper_is_inf(a)) {
            reset(b);
        }
        else {
            m().set(lower(b), upper(a));
            m().neg(lower(b));
            set_lower_is_inf(b, false);
            set_lower_is_open(b, upper_is_open(a));

            m().reset(upper(b));
            set_upper_is_inf(b, true);
            set_upper_is_open(b, true);
        }
    }
    else {
        if (upper_is_inf(a)) {
            m().set(upper(b), lower(a));
            m().neg(upper(b));
            set_upper_is_inf(b, false);
            set_upper_is_open(b, lower_is_open(a));

            m().reset(lower(b));
            set_lower_is_inf(b, true);
            set_lower_is_open(b, true);
        }
        else {
            if (&a == &b) {
                m().swap(lower(b), upper(b));
            }
            else {
                m().set(lower(b), upper(a));
                m().set(upper(b), lower(a));
            }
            m().neg(lower(b));
            m().neg(upper(b));
            set_lower_is_inf(b, false);
            set_upper_is_inf(b, false);
            bool l_o = lower_is_open(a);
            bool u_o = upper_is_open(a);
            set_lower_is_open(b, u_o);
            set_upper_is_open(b, l_o);
        }
    }
    SASSERT(check_invariant(b));
}

template<typename C>
void interval_manager<C>::add_jst(interval const & a, interval const & b, interval_deps & c_deps) {
    c_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2;
    c_deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2;
}

template<typename C>
void interval_manager<C>::add(interval const & a, interval const & b, interval & c, interval_deps & c_deps) {
    add_jst(a, b, c_deps);
    add(a, b, c);
}
    
template<typename C>
void interval_manager<C>::add(interval const & a, interval const & b, interval & c) {
    ext_numeral_kind new_l_kind, new_u_kind;
    round_to_minus_inf();
    ::add(m(), lower(a), lower_kind(a), lower(b), lower_kind(b), lower(c), new_l_kind);
    round_to_plus_inf();
    ::add(m(), upper(a), upper_kind(a), upper(b), upper_kind(b), upper(c), new_u_kind);
    set_lower_is_inf(c, new_l_kind == EN_MINUS_INFINITY);
    set_upper_is_inf(c, new_u_kind == EN_PLUS_INFINITY);
    set_lower_is_open(c, lower_is_open(a) || lower_is_open(b));
    set_upper_is_open(c, upper_is_open(a) || upper_is_open(b));
    SASSERT(check_invariant(c));
}

template<typename C>
void interval_manager<C>::sub_jst(interval const & a, interval const & b, interval_deps & c_deps) {
    c_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2;
    c_deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2;
}

template<typename C>
void interval_manager<C>::sub(interval const & a, interval const & b, interval & c, interval_deps & c_deps) {
    sub_jst(a, b, c_deps);
    sub(a, b, c);
}

template<typename C>
void interval_manager<C>::sub(interval const & a, interval const & b, interval & c) {
    ext_numeral_kind new_l_kind, new_u_kind;
    round_to_minus_inf();
    ::sub(m(), lower(a), lower_kind(a), upper(b), upper_kind(b), lower(c), new_l_kind);
    round_to_plus_inf();
    ::sub(m(), upper(a), upper_kind(a), lower(b), lower_kind(b), upper(c), new_u_kind);
    set_lower_is_inf(c, new_l_kind == EN_MINUS_INFINITY);
    set_upper_is_inf(c, new_u_kind == EN_PLUS_INFINITY);
    set_lower_is_open(c, lower_is_open(a) || upper_is_open(b));
    set_upper_is_open(c, upper_is_open(a) || lower_is_open(b));
    SASSERT(check_invariant(c));
}

template<typename C>
void interval_manager<C>::mul_jst(numeral const & k, interval const & a, interval_deps & b_deps) {
    if (m().is_zero(k)) {
        b_deps.m_lower_deps = 0;
        b_deps.m_upper_deps = 0;
   }
    else if (m().is_neg(k)) {
        b_deps.m_lower_deps = DEP_IN_UPPER1;
        b_deps.m_upper_deps = DEP_IN_LOWER1;
    }
    else {
        b_deps.m_lower_deps = DEP_IN_LOWER1;
        b_deps.m_upper_deps = DEP_IN_UPPER1;
    }
}

template<typename C>
void interval_manager<C>::div_mul(numeral const & k, interval const & a, interval & b, bool inv_k) {
    if (m().is_zero(k)) {
        reset(b);
    }
    else {
        numeral const & l = lower(a); ext_numeral_kind l_k = lower_kind(a);
        numeral const & u = upper(a); ext_numeral_kind u_k = upper_kind(a);
        numeral & new_l_val = m_result_lower;
        numeral & new_u_val = m_result_upper;
        ext_numeral_kind new_l_kind, new_u_kind;
        bool l_o = lower_is_open(a);
        bool u_o = upper_is_open(a);
        if (m().is_pos(k)) {
            set_lower_is_open(b, l_o);
            set_upper_is_open(b, u_o);
            if (inv_k) {
                round_to_minus_inf();
                m().inv(k, m_inv_k);
                ::mul(m(), l, l_k, m_inv_k, EN_NUMERAL, new_l_val, new_l_kind);
                
                round_to_plus_inf();
                m().inv(k, m_inv_k);
                ::mul(m(), u, u_k, m_inv_k, EN_NUMERAL, new_u_val, new_u_kind);
            }
            else {
                round_to_minus_inf();
                ::mul(m(), l, l_k, k, EN_NUMERAL, new_l_val, new_l_kind);
                round_to_plus_inf();
                ::mul(m(), u, u_k, k, EN_NUMERAL, new_u_val, new_u_kind);
            }
        }
        else {
            set_lower_is_open(b, u_o);
            set_upper_is_open(b, l_o);
            if (inv_k) {
                round_to_minus_inf();
                m().inv(k, m_inv_k);
                ::mul(m(), u, u_k, m_inv_k, EN_NUMERAL, new_l_val, new_l_kind);

                round_to_plus_inf();
                m().inv(k, m_inv_k);
                ::mul(m(), l, l_k, m_inv_k, EN_NUMERAL, new_u_val, new_u_kind);
            }
            else {
                round_to_minus_inf();
                ::mul(m(), u, u_k, k, EN_NUMERAL, new_l_val, new_l_kind);
                round_to_plus_inf();
                ::mul(m(), l, l_k, k, EN_NUMERAL, new_u_val, new_u_kind);
            }
        }
        m().swap(lower(b), new_l_val);
        m().swap(upper(b), new_u_val);
        set_lower_is_inf(b, new_l_kind == EN_MINUS_INFINITY);
        set_upper_is_inf(b, new_u_kind == EN_PLUS_INFINITY);
    }
}

template<typename C>
void interval_manager<C>::mul(numeral const & k, interval const & a, interval & b, interval_deps & b_deps) {
    mul_jst(k, a, b_deps);
    mul(k, a, b);
}

template<typename C>
void interval_manager<C>::mul(int n, int d, interval const & a, interval & b) {
    _scoped_numeral<numeral_manager> aux(m());
    m().set(aux, n, d);
    mul(aux, a, b);
}

template<typename C>
void interval_manager<C>::div(interval const & a, numeral const & k, interval & b, interval_deps & b_deps) {
    div_jst(a, k, b_deps);
    div(a, k, b);
}

template<typename C>
void interval_manager<C>::mul_jst(interval const & i1, interval const & i2, interval_deps & r_deps) {
    if (is_zero(i1)) {
        r_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        r_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
    }
    else if (is_zero(i2)) {
        r_deps.m_lower_deps = DEP_IN_LOWER2 | DEP_IN_UPPER2;
        r_deps.m_upper_deps = DEP_IN_LOWER2 | DEP_IN_UPPER2;
    }
    else if (is_N(i1)) {
        if (is_N(i2)) {
            // x <= b <= 0, y <= d <= 0 --> b*d <= x*y
            // a <= x <= b <= 0, c <= y <= d <= 0 --> x*y <= a*c  (we can use the fact that x or y is always negative (i.e., b is neg or d is neg))
            r_deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2;
            r_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER1; // we can replace DEP_IN_UPPER1 with DEP_IN_UPPER2
        }
        else if (is_M(i2)) {
            // a <= x <= b <= 0,  y <= d, d > 0 --> a*d <= x*y (uses the fact that b is not positive)
            // a <= x <= b <= 0,  c <= y, c < 0 --> x*y <= a*c (uses the fact that b is not positive)
            r_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2 | DEP_IN_UPPER1;
            r_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER1;
        }
        else {
            // a <= x <= b <= 0, 0 <= c <= y <= d --> a*d <= x*y (uses the fact that x is neg (b is not positive) or y is pos (c is not negative))
            // x <= b <= 0,  0 <= c <= y --> x*y <= b*c
            r_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2 | DEP_IN_UPPER1; // we can replace DEP_IN_UPPER1 with DEP_IN_UPPER2
            r_deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2;
        }
    }
    else if (is_M(i1)) {
        if (is_N(i2)) {
            // b > 0, x <= b,  c <= y <= d <= 0 --> b*c <= x*y (uses the fact that d is not positive)
            // a < 0, a <= x,  c <= y <= d <= 0 --> x*y <= a*c (uses the fact that d is not positive)
            r_deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
            r_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
        }
        else if (is_M(i2)) {
            r_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
            r_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
        }
        else {
            // a < 0, a <= x, 0 <= c <= y <= d --> a*d <= x*y (uses the fact that c is not negative)
            // b > 0, x <= b, 0 <= c <= y <= d --> x*y <= b*d (uses the fact that c is not negative)
            r_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2 | DEP_IN_LOWER2;
            r_deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2 | DEP_IN_LOWER2;
        }
    }
    else {
        SASSERT(is_P(i1));        
        if (is_N(i2)) {
            // 0 <= a <= x <= b,   c <= y <= d <= 0  -->  x*y <= b*c (uses the fact that x is pos (a is not neg) or y is neg (d is not pos))
            // 0 <= a <= x,  y <= d <= 0  --> a*d <= x*y
            r_deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_LOWER1; // we can replace DEP_IN_LOWER1 with DEP_IN_UPPER2
            r_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2;
        }
        else if (is_M(i2)) {
            // 0 <= a <= x <= b,  c <= y --> b*c <= x*y (uses the fact that a is not negative)
            // 0 <= a <= x <= b,  y <= d --> x*y <= b*d (uses the fact that a is not negative)
            r_deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_LOWER1;
            r_deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2 | DEP_IN_LOWER1;
        }
        else {
            SASSERT(is_P(i2));
            // 0 <= a <= x, 0 <= c <= y --> a*c <= x*y 
            // x <= b, y <= d --> x*y <= b*d (uses the fact that x is pos (a is not negative) or y is pos (c is not negative))
            r_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2;
            r_deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2 | DEP_IN_LOWER1; // we can replace DEP_IN_LOWER1 with DEP_IN_LOWER2
        }
    }
}

template<typename C>
void interval_manager<C>::mul(interval const & i1, interval const & i2, interval & r, interval_deps & r_deps) {
    mul_jst(i1, i2, r_deps);
    mul(i1, i2, r);
}

template<typename C>
void interval_manager<C>::mul(interval const & i1, interval const & i2, interval & r) {
#ifdef _TRACE
    static unsigned call_id = 0;
#endif
#if Z3DEBUG || _TRACE
    bool i1_contains_zero = contains_zero(i1);
    bool i2_contains_zero = contains_zero(i2);
#endif
    if (is_zero(i1)) {
        set(r, i1);
        return;
    }
    if (is_zero(i2)) {
        set(r, i2);
        return;
    }

    numeral const & a = lower(i1); ext_numeral_kind a_k = lower_kind(i1);
    numeral const & b = upper(i1); ext_numeral_kind b_k = upper_kind(i1);
    numeral const & c = lower(i2); ext_numeral_kind c_k = lower_kind(i2);
    numeral const & d = upper(i2); ext_numeral_kind d_k = upper_kind(i2);

    bool a_o = lower_is_open(i1);
    bool b_o = upper_is_open(i1);
    bool c_o = lower_is_open(i2);
    bool d_o = upper_is_open(i2);

    numeral & new_l_val = m_result_lower;
    numeral & new_u_val = m_result_upper;
    ext_numeral_kind new_l_kind, new_u_kind;

    if (is_N(i1)) {
        if (is_N(i2)) {
            // x <= b <= 0, y <= d <= 0 --> b*d <= x*y
            // a <= x <= b <= 0, c <= y <= d <= 0 --> x*y <= a*c  (we can use the fact that x or y is always negative (i.e., b is neg or d is neg))
            TRACE("interval_bug", tout << "(N, N) #" << call_id << "\n"; display(tout, i1); tout << "\n"; display(tout, i2); tout << "\n";
                  tout << "a: "; m().display(tout, a); tout << "\n";
                  tout << "b: "; m().display(tout, b); tout << "\n";
                  tout << "c: "; m().display(tout, c); tout << "\n";
                  tout << "d: "; m().display(tout, d); tout << "\n";
                  tout << "is_N0(i1): " << is_N0(i1) << "\n";
                  tout << "is_N0(i2): " << is_N0(i2) << "\n";
                  );
            set_lower_is_open(r, (is_N0(i1) || is_N0(i2)) ? false : (b_o || d_o));
            set_upper_is_open(r, a_o || c_o);
            // if b = 0 (and the interval is closed), then the lower bound is closed

            round_to_minus_inf();
            ::mul(m(), b, b_k, d, d_k, new_l_val, new_l_kind);
            round_to_plus_inf();
            ::mul(m(), a, a_k, c, c_k, new_u_val, new_u_kind);
        }
        else if (is_M(i2)) {
            // a <= x <= b <= 0,  y <= d, d > 0 --> a*d <= x*y (uses the fact that b is not positive)
            // a <= x <= b <= 0,  c <= y, c < 0 --> x*y <= a*c (uses the fact that b is not positive)
            TRACE("interval_bug", tout << "(N, M) #" << call_id << "\n";);

            set_lower_is_open(r, a_o || d_o);
            set_upper_is_open(r, a_o || c_o);

            round_to_minus_inf();
            ::mul(m(), a, a_k, d, d_k, new_l_val, new_l_kind);
            round_to_plus_inf();
            ::mul(m(), a, a_k, c, c_k, new_u_val, new_u_kind);
        }
        else {
            // a <= x <= b <= 0, 0 <= c <= y <= d --> a*d <= x*y (uses the fact that x is neg (b is not positive) or y is pos (c is not negative))
            // x <= b <= 0,  0 <= c <= y --> x*y <= b*c
            TRACE("interval_bug", tout << "(N, P) #" << call_id << "\n";);
            SASSERT(is_P(i2));
            
            // must update upper_is_open first, since value of is_N0(i1) and is_P0(i2) may be affected by update 
            set_upper_is_open(r, (is_N0(i1) || is_P0(i2)) ? false : (b_o || c_o));
            set_lower_is_open(r, a_o || d_o);
            
            round_to_minus_inf();
            ::mul(m(), a, a_k, d, d_k, new_l_val, new_l_kind);
            round_to_plus_inf();
            ::mul(m(), b, b_k, c, c_k, new_u_val, new_u_kind);
        }
    }
    else if (is_M(i1)) {
        if (is_N(i2)) {
            // b > 0, x <= b,  c <= y <= d <= 0 --> b*c <= x*y (uses the fact that d is not positive)
            // a < 0, a <= x,  c <= y <= d <= 0 --> x*y <= a*c (uses the fact that d is not positive)
            TRACE("interval_bug", tout << "(M, N) #" << call_id << "\n";);

            set_lower_is_open(r, b_o || c_o);
            set_upper_is_open(r, a_o || c_o); 

            round_to_minus_inf();
            ::mul(m(), b, b_k, c, c_k, new_l_val, new_l_kind);
            round_to_plus_inf();
            ::mul(m(), a, a_k, c, c_k, new_u_val, new_u_kind);
        }
        else if (is_M(i2)) {
            numeral & ad = m_mul_ad; ext_numeral_kind ad_k;
            numeral & bc = m_mul_bc; ext_numeral_kind bc_k;
            numeral & ac = m_mul_ac; ext_numeral_kind ac_k;
            numeral & bd = m_mul_bd; ext_numeral_kind bd_k;

            bool  ad_o = a_o || d_o;
            bool  bc_o = b_o || c_o;
            bool  ac_o = a_o || c_o;
            bool  bd_o = b_o || d_o;
            
            round_to_minus_inf();
            ::mul(m(), a, a_k, d, d_k, ad, ad_k);
            ::mul(m(), b, b_k, c, c_k, bc, bc_k);
            round_to_plus_inf();
            ::mul(m(), a, a_k, c, c_k, ac, ac_k);
            ::mul(m(), b, b_k, d, d_k, bd, bd_k);

            if (::lt(m(), ad, ad_k, bc, bc_k) || (::eq(m(), ad, ad_k, bc, bc_k) && !ad_o && bc_o)) {
                m().swap(new_l_val, ad);
                new_l_kind = ad_k;
                set_lower_is_open(r, ad_o);
            }
            else {
                m().swap(new_l_val, bc);
                new_l_kind = bc_k;
                set_lower_is_open(r, bc_o);
            }

            
            if (::gt(m(), ac, ac_k, bd, bd_k) || (::eq(m(), ac, ac_k, bd, bd_k) && !ac_o && bd_o)) {
                m().swap(new_u_val, ac);
                new_u_kind = ac_k;
                set_upper_is_open(r, ac_o);
            }
            else {
                m().swap(new_u_val, bd);
                new_u_kind = bd_k;
                set_upper_is_open(r, bd_o);
            }
        }
        else {
            // a < 0, a <= x, 0 <= c <= y <= d --> a*d <= x*y (uses the fact that c is not negative)
            // b > 0, x <= b, 0 <= c <= y <= d --> x*y <= b*d (uses the fact that c is not negative)
            TRACE("interval_bug", tout << "(M, P) #" << call_id << "\n";);
            SASSERT(is_P(i2));

            set_lower_is_open(r, a_o || d_o);
            set_upper_is_open(r, b_o || d_o); 

            round_to_minus_inf();
            ::mul(m(), a, a_k, d, d_k, new_l_val, new_l_kind);
            round_to_plus_inf();
            ::mul(m(), b, b_k, d, d_k, new_u_val, new_u_kind);
        }
    }
    else {
        SASSERT(is_P(i1));        
        if (is_N(i2)) {
            // 0 <= a <= x <= b,   c <= y <= d <= 0  -->  x*y <= b*c (uses the fact that x is pos (a is not neg) or y is neg (d is not pos))
            // 0 <= a <= x,  y <= d <= 0  --> a*d <= x*y
            TRACE("interval_bug", tout << "(P, N) #" << call_id << "\n";);
            
            // must update upper_is_open first, since value of is_P0(i1) and is_N0(i2) may be affected by update 
            set_upper_is_open(r, (is_P0(i1) || is_N0(i2)) ? false : a_o || d_o);
            set_lower_is_open(r, b_o || c_o);

            round_to_minus_inf();
            ::mul(m(), b, b_k, c, c_k, new_l_val, new_l_kind);
            round_to_plus_inf();
            ::mul(m(), a, a_k, d, d_k, new_u_val, new_u_kind);
        }
        else if (is_M(i2)) {
            // 0 <= a <= x <= b,  c <= y --> b*c <= x*y (uses the fact that a is not negative)
            // 0 <= a <= x <= b,  y <= d --> x*y <= b*d (uses the fact that a is not negative)
            TRACE("interval_bug", tout << "(P, M) #" << call_id << "\n";);

            set_lower_is_open(r, b_o || c_o);
            set_upper_is_open(r, b_o || d_o);

            round_to_minus_inf();
            ::mul(m(), b, b_k, c, c_k, new_l_val, new_l_kind);
            round_to_plus_inf();
            ::mul(m(), b, b_k, d, d_k, new_u_val, new_u_kind);
        }
        else {
            SASSERT(is_P(i2));
            // 0 <= a <= x, 0 <= c <= y --> a*c <= x*y 
            // x <= b, y <= d --> x*y <= b*d (uses the fact that x is pos (a is not negative) or y is pos (c is not negative))
            TRACE("interval_bug", tout << "(P, P) #" << call_id << "\n";);

            set_lower_is_open(r, (is_P0(i1) || is_P0(i2)) ? false : a_o || c_o);
            set_upper_is_open(r, b_o || d_o);

            round_to_minus_inf();
            ::mul(m(), a, a_k, c, c_k, new_l_val, new_l_kind);
            round_to_plus_inf();
            ::mul(m(), b, b_k, d, d_k, new_u_val, new_u_kind);
        }
    }

    m().swap(lower(r), new_l_val);
    m().swap(upper(r), new_u_val);
    set_lower_is_inf(r, new_l_kind == EN_MINUS_INFINITY);
    set_upper_is_inf(r, new_u_kind == EN_PLUS_INFINITY);
    SASSERT(!(i1_contains_zero || i2_contains_zero) || contains_zero(r));
    TRACE("interval_bug", tout << "result: "; display(tout, r); tout << "\n";);
#ifdef _TRACE
    call_id++;
#endif
}

template<typename C>
void interval_manager<C>::power_jst(interval const & a, unsigned n, interval_deps & b_deps) {
    if (n == 1) {
        b_deps.m_lower_deps = DEP_IN_LOWER1;
        b_deps.m_upper_deps = DEP_IN_UPPER1;
    }
    else if (n % 2 == 0) {
        if (lower_is_pos(a)) {
            // [l, u]^n = [l^n, u^n] if l > 0
            // 0 < l <= x      --> l^n <= x^n (lower bound guarantees that is positive)
            // 0 < l <= x <= u --> x^n <= u^n (use lower and upper bound -- need the fact that x is positive)
            b_deps.m_lower_deps = DEP_IN_LOWER1;
            if (upper_is_inf(a))
                b_deps.m_upper_deps = 0;
            else
                b_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        }
        else if (upper_is_neg(a)) {
            // [l, u]^n = [u^n, l^n] if u < 0
            // l <= x <= u < 0   -->  x^n <= l^n (use lower and upper bound -- need the fact that x is negative)
            // x <= u < 0        -->  u^n <= x^n 
            b_deps.m_lower_deps = DEP_IN_UPPER1;
            if (lower_is_inf(a))
                b_deps.m_upper_deps = 0;
            else
                b_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        }
        else {
            // [l, u]^n = [0, max{l^n, u^n}] otherwise
            // we need both bounds to justify upper bound
            b_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
            b_deps.m_lower_deps = 0;
        }
    }
    else {
        // Remark: when n is odd x^n is monotonic.
        if (lower_is_inf(a))
            b_deps.m_lower_deps = 0;
        else
            b_deps.m_lower_deps = DEP_IN_LOWER1;
        
        if (upper_is_inf(a))
            b_deps.m_upper_deps = 0;
        else
            b_deps.m_upper_deps = DEP_IN_UPPER1;
    }
}

template<typename C>
void interval_manager<C>::power(interval const & a, unsigned n, interval & b, interval_deps & b_deps) {
    power_jst(a, n, b_deps);
    power(a, n, b);
}

template<typename C>
void interval_manager<C>::power(interval const & a, unsigned n, interval & b) {
#ifdef _TRACE
    static unsigned call_id = 0;
#endif
    if (n == 1) {
        set(b, a);
    }
    else if (n % 2 == 0) {
        if (lower_is_pos(a)) {
            // [l, u]^n = [l^n, u^n] if l > 0
            // 0 < l <= x      --> l^n <= x^n (lower bound guarantees that is positive)
            // 0 < l <= x <= u --> x^n <= u^n (use lower and upper bound -- need the fact that x is positive)
            SASSERT(!lower_is_inf(a));
            round_to_minus_inf();
            m().power(lower(a), n, lower(b));
            set_lower_is_inf(b, false);
            set_lower_is_open(b, lower_is_open(a));

            if (upper_is_inf(a)) {
                reset_upper(b);
            }
            else {
                round_to_plus_inf();
                m().power(upper(a), n, upper(b));
                set_upper_is_inf(b, false);
                set_upper_is_open(b, upper_is_open(a));
            }
        }
        else if (upper_is_neg(a)) {
            // [l, u]^n = [u^n, l^n] if u < 0
            // l <= x <= u < 0   -->  x^n <= l^n (use lower and upper bound -- need the fact that x is negative)
            // x <= u < 0        -->  u^n <= x^n 
            SASSERT(!upper_is_inf(a));
            bool lower_a_open = lower_is_open(a), upper_a_open = upper_is_open(a);
            bool lower_a_inf  = lower_is_inf(a);
            
            m().set(lower(b), lower(a));
            m().set(upper(b), upper(a));
            m().swap(lower(b), upper(b)); // we use a swap because a and b can be aliased
            

            round_to_minus_inf();
            m().power(lower(b), n, lower(b));

            set_lower_is_open(b, upper_a_open);
            set_lower_is_inf(b, false);

            if (lower_a_inf) {
                reset_upper(b);
            }
            else {
                round_to_plus_inf();
                m().power(upper(b), n, upper(b));
                set_upper_is_inf(b, false);
                set_upper_is_open(b, lower_a_open);
            }
        }
        else {
            // [l, u]^n = [0, max{l^n, u^n}] otherwise
            // we need both bounds to justify upper bound
            TRACE("interval_bug", tout << "(M) #" << call_id << "\n"; display(tout, a); tout << "\nn:" << n << "\n";);

            ext_numeral_kind un1_kind = lower_kind(a), un2_kind = upper_kind(a);
            numeral & un1 = m_result_lower;
            numeral & un2 = m_result_upper;
            m().set(un1, lower(a));
            m().set(un2, upper(a));
            round_to_plus_inf();
            ::power(m(), un1, un1_kind, n);
            ::power(m(), un2, un2_kind, n);
            
            if (::gt(m(), un1, un1_kind, un2, un2_kind) || (::eq(m(), un1, un1_kind, un2, un2_kind) && !lower_is_open(a) && upper_is_open(a))) {
                m().swap(upper(b), un1);
                set_upper_is_inf(b, un1_kind == EN_PLUS_INFINITY);
                set_upper_is_open(b, lower_is_open(a));
            }
            else {
                m().swap(upper(b), un2);
                set_upper_is_inf(b, un2_kind == EN_PLUS_INFINITY);
                set_upper_is_open(b, upper_is_open(a));
            }
            
            m().reset(lower(b));
            set_lower_is_inf(b, false);
            set_lower_is_open(b, false);
        }
    }
    else {
        // Remark: when n is odd x^n is monotonic.
        if (lower_is_inf(a)) {
            reset_lower(b);
        }
        else { 
            m().power(lower(a), n, lower(b)); 
            set_lower_is_inf(b, false);
            set_lower_is_open(b, lower_is_open(a));
        }

        if (upper_is_inf(a)) {
            reset_upper(b);
        }
        else {
            m().power(upper(a), n, upper(b));
            set_upper_is_inf(b, false);
            set_upper_is_open(b, upper_is_open(a));
        }
    }
    TRACE("interval_bug", tout << "result: "; display(tout, b); tout << "\n";);
#ifdef _TRACE
    call_id++;
#endif
}


template<typename C>
void interval_manager<C>::nth_root(interval const & a, unsigned n, numeral const & p, interval & b, interval_deps & b_deps) {
    nth_root_jst(a, n, p, b_deps);
    nth_root(a, n, p, b);
}

template<typename C>
void interval_manager<C>::nth_root(interval const & a, unsigned n, numeral const & p, interval & b) {
    SASSERT(n % 2 != 0 || !lower_is_neg(a));
    if (n == 1) {
        set(b, a);
        return;
    }

    if (lower_is_inf(a)) {
        SASSERT(n % 2 != 0); // n must not be even.
        m().reset(lower(b));
        set_lower_is_inf(b, true);
        set_lower_is_open(b, true);
    }
    else {
        numeral & lo = m_result_lower;
        numeral & hi = m_result_upper;
        nth_root(lower(a), n, p, lo, hi);
        set_lower_is_inf(b, false);
        set_lower_is_open(b, lower_is_open(a) && m().eq(lo, hi));
        m().set(lower(b), lo);
    }
    
    if (upper_is_inf(a)) {
        m().reset(upper(b));
        set_upper_is_inf(b, true);
        set_upper_is_open(b, true);
    }
    else {
        numeral & lo = m_result_lower;
        numeral & hi = m_result_upper;
        nth_root(upper(a), n, p, lo, hi);
        set_upper_is_inf(b, false);
        set_upper_is_open(b, upper_is_open(a) && m().eq(lo, hi));
        m().set(upper(b), hi);
    }
    TRACE("interval_nth_root", display(tout, a); tout << " --> "; display(tout, b); tout << "\n";); 
}

template<typename C>
void interval_manager<C>::nth_root_jst(interval const & a, unsigned n, numeral const & p, interval_deps & b_deps) {
    b_deps.m_lower_deps = DEP_IN_LOWER1;
    if (n % 2 == 0)
        b_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
    else
        b_deps.m_upper_deps = DEP_IN_UPPER1;
}

template<typename C>
void interval_manager<C>::xn_eq_y(interval const & y, unsigned n, numeral const & p, interval & x, interval_deps & x_deps) {
    xn_eq_y_jst(y, n, p, x_deps);
    xn_eq_y(y, n, p, x);
}

template<typename C>
void interval_manager<C>::xn_eq_y(interval const & y, unsigned n, numeral const & p, interval & x) {
    SASSERT(n % 2 != 0 || !lower_is_neg(y));
    if (n % 2 == 0) {
        SASSERT(!lower_is_inf(y));
        if (upper_is_inf(y)) {
            reset(x);
        }
        else {
            numeral & lo = m_result_lower;
            numeral & hi = m_result_upper;
            nth_root(upper(y), n, p, lo, hi);
            // result is [-hi, hi]
            // result is open if upper(y) is open and lo == hi
            TRACE("interval_xn_eq_y", tout << "x^n = "; display(tout, y); tout << "\n";
                  tout << "sqrt(y) in "; m().display(tout, lo); tout << " "; m().display(tout, hi); tout << "\n";);
            bool open = upper_is_open(y) && m().eq(lo, hi);
            set_lower_is_inf(x, false);
            set_upper_is_inf(x, false);
            set_lower_is_open(x, open);
            set_upper_is_open(x, open);
            m().set(upper(x), hi);
            round_to_minus_inf();
            m().set(lower(x), hi);
            m().neg(lower(x));
            TRACE("interval_xn_eq_y", tout << "interval for x: "; display(tout, x); tout << "\n";);
        }
    }
    else {
        SASSERT(n % 2 == 1); // n is odd
        nth_root(y, n, p, x);
    }
}

template<typename C>
void interval_manager<C>::xn_eq_y_jst(interval const & y, unsigned n, numeral const & p, interval_deps & x_deps) {
    if (n % 2 == 0) {
        x_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        x_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
    }
    else {
        x_deps.m_lower_deps = DEP_IN_LOWER1;
        x_deps.m_upper_deps = DEP_IN_UPPER1;
    }
}

template<typename C>
void interval_manager<C>::inv_jst(interval const & a, interval_deps & b_deps) {
    SASSERT(!contains_zero(a));
    if (is_P1(a)) {
        b_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
        b_deps.m_upper_deps = DEP_IN_LOWER1;
    }
    else if (is_N1(a)) {
        // x <= u < 0 --> 1/u <= 1/x
        // l <= x <= u < 0 --> 1/l <= 1/x (use lower and upper bounds)
        b_deps.m_lower_deps = DEP_IN_UPPER1;
        b_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER1;
    }
    else {
        UNREACHABLE();
    }
}

template<typename C>
void interval_manager<C>::inv(interval const & a, interval & b, interval_deps & b_deps) {
    inv_jst(a, b_deps);
    inv(a, b);
}

template<typename C>
void interval_manager<C>::inv(interval const & a, interval & b) {
#ifdef _TRACE
    static unsigned call_id = 0;
#endif
    // If the interval [l,u] does not contain 0, then 1/[l,u] = [1/u, 1/l]
    SASSERT(!contains_zero(a));
    TRACE("interval_bug", tout << "(inv) #" << call_id << "\n"; display(tout, a); tout << "\n";);

    numeral & new_l_val = m_result_lower;
    numeral & new_u_val = m_result_upper;
    ext_numeral_kind new_l_kind, new_u_kind;
    
    if (is_P1(a)) {
        // 0 < l <= x --> 1/x <= 1/l
        // 0 < l <= x <= u --> 1/u <= 1/x (use lower and upper bounds)
        
        round_to_minus_inf();
        m().set(new_l_val, upper(a)); new_l_kind = upper_kind(a);
        ::inv(m(), new_l_val, new_l_kind);
        SASSERT(new_l_kind == EN_NUMERAL);
        bool new_l_open = upper_is_open(a);
        
        if (lower_is_zero(a)) {
            SASSERT(lower_is_open(a));
            m().reset(upper(b));
            set_upper_is_inf(b, true);
            set_upper_is_open(b, true);
        }
        else {
            round_to_plus_inf();
            m().set(new_u_val, lower(a)); 
            m().inv(new_u_val);
            m().swap(upper(b), new_u_val);
            set_upper_is_inf(b, false);
            set_upper_is_open(b, lower_is_open(a));
        }
        
        m().swap(lower(b), new_l_val);  
        set_lower_is_inf(b, false); 
        set_lower_is_open(b, new_l_open);
    }
    else if (is_N1(a)) {
        // x <= u < 0 --> 1/u <= 1/x
        // l <= x <= u < 0 --> 1/l <= 1/x (use lower and upper bounds)

        round_to_plus_inf();
        m().set(new_u_val, lower(a)); new_u_kind = lower_kind(a);
        ::inv(m(), new_u_val, new_u_kind);
        SASSERT(new_u_kind == EN_NUMERAL);
        bool new_u_open = lower_is_open(a);

        if (upper_is_zero(a)) {
            SASSERT(upper_is_open(a));
            m().reset(lower(b));
            set_lower_is_open(b, true);
            set_lower_is_inf(b, true);
        }
        else {
            round_to_minus_inf();
            m().set(new_l_val, upper(a));
            m().inv(new_l_val);
            m().swap(lower(b), new_l_val);
            set_lower_is_inf(b, false);
            set_lower_is_open(b, upper_is_open(a));
        }
        
        m().swap(upper(b), new_u_val); 
        set_upper_is_inf(b, false);
        set_upper_is_open(b, new_u_open);
    }
    else {
        UNREACHABLE();
    }
    TRACE("interval_bug", tout << "result: "; display(tout, b); tout << "\n";);
#ifdef _TRACE
    call_id++;
#endif
}

template<typename C>
void interval_manager<C>::div_jst(interval const & i1, interval const & i2, interval_deps & r_deps) {
    SASSERT(!contains_zero(i2));
    if (is_zero(i1)) {
        if (is_P1(i2)) {
            r_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2;
            r_deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2;
        }
        else {
            r_deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2;
            r_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2;
        }
    }
    else {
        if (is_N(i1)) {
            if (is_N1(i2)) {
                // x <= b <= 0,      c <= y <= d < 0 --> b/c <= x/y
                // a <= x <= b <= 0,      y <= d < 0 -->        x/y <= a/d
                r_deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
                r_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2; 
            }
            else {
                // a <= x, a < 0,   0 < c <= y       -->  a/c <= x/y
                // x <= b <= 0,     0 < c <= y <= d  -->         x/y <= b/d
                r_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2; 
                r_deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
            }
        }
        else if (is_M(i1)) {
            if (is_N1(i2)) {
                // 0 < a <= x <= b < 0,  y <= d < 0   --> b/d <= x/y
                // 0 < a <= x <= b < 0,  y <= d < 0   -->        x/y <= a/d
                r_deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2;
                r_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_UPPER2;
            }
            else {
                // 0 < a <= x <= b < 0, 0 < c <= y  --> a/c <= x/y
                // 0 < a <= x <= b < 0, 0 < c <= y  -->        x/y <= b/c
                r_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2;
                r_deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2;
            }
        }
        else {
            SASSERT(is_P(i1));        
            if (is_N1(i2)) {
                // b > 0,    x <= b,   c <= y <= d < 0    -->  b/d <= x/y
                // 0 <= a <= x,        c <= y <= d < 0    -->         x/y  <= a/c
                r_deps.m_lower_deps = DEP_IN_UPPER1 | DEP_IN_UPPER2;
                r_deps.m_upper_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
            }
            else {
                SASSERT(is_P1(i2));
                // 0 <= a <= x,      0 < c <= y <= d    -->   a/d <= x/y
                // b > 0     x <= b, 0 < c <= y         -->          x/y <= b/c
                r_deps.m_lower_deps = DEP_IN_LOWER1 | DEP_IN_LOWER2 | DEP_IN_UPPER2;
                r_deps.m_upper_deps = DEP_IN_UPPER1 | DEP_IN_LOWER2;
            }
        }
    }
}

template<typename C>
void interval_manager<C>::div(interval const & i1, interval const & i2, interval & r, interval_deps & r_deps) {
    div_jst(i1, i2, r_deps);
    div(i1, i2, r);
}

template<typename C>
void interval_manager<C>::div(interval const & i1, interval const & i2, interval & r) {
#ifdef _TRACE
    static unsigned call_id = 0;
#endif
    SASSERT(!contains_zero(i2));
    SASSERT(&i1 != &r);
    
    if (is_zero(i1)) {
        TRACE("interval_bug", tout << "div #" << call_id << "\n"; display(tout, i1); tout << "\n"; display(tout, i2); tout << "\n";);

        // 0/other = 0 if other != 0
        m().reset(lower(r));
        m().reset(upper(r));
        set_lower_is_inf(r, false);
        set_upper_is_inf(r, false);
        set_lower_is_open(r, false);
        set_upper_is_open(r, false);
    }
    else {
        numeral const & a = lower(i1); ext_numeral_kind a_k = lower_kind(i1);
        numeral const & b = upper(i1); ext_numeral_kind b_k = upper_kind(i1);
        numeral const & c = lower(i2); ext_numeral_kind c_k = lower_kind(i2);
        numeral const & d = upper(i2); ext_numeral_kind d_k = upper_kind(i2);
        
        bool a_o = lower_is_open(i1);
        bool b_o = upper_is_open(i1);
        bool c_o = lower_is_open(i2);
        bool d_o = upper_is_open(i2);
        
        numeral & new_l_val = m_result_lower;
        numeral & new_u_val = m_result_upper;
        ext_numeral_kind new_l_kind, new_u_kind;

        TRACE("interval_bug", tout << "div #" << call_id << "\n"; display(tout, i1); tout << "\n"; display(tout, i2); tout << "\n";
              tout << "a: "; m().display(tout, a); tout << "\n";
              tout << "b: "; m().display(tout, b); tout << "\n";
              tout << "c: "; m().display(tout, c); tout << "\n";
              tout << "d: "; m().display(tout, d); tout << "\n";
              );
        
        if (is_N(i1)) {
            if (is_N1(i2)) {
                // x <= b <= 0,      c <= y <= d < 0 --> b/c <= x/y
                // a <= x <= b <= 0,      y <= d < 0 -->        x/y <= a/d
                TRACE("interval_bug", tout << "(N, N) #" << call_id << "\n";);

                set_lower_is_open(r, is_N0(i1) ? false : b_o || c_o);
                set_upper_is_open(r, a_o || d_o);
                
                round_to_minus_inf();
                ::div(m(), b, b_k, c, c_k, new_l_val, new_l_kind);
                if (m().is_zero(d)) {
                    SASSERT(d_o);
                    m().reset(new_u_val);
                    new_u_kind = EN_PLUS_INFINITY;
                }
                else {
                    round_to_plus_inf();
                    ::div(m(), a, a_k, d, d_k, new_u_val, new_u_kind);
                }
            }
            else {
                // a <= x, a < 0,   0 < c <= y       -->  a/c <= x/y
                // x <= b <= 0,     0 < c <= y <= d  -->         x/y <= b/d
                TRACE("interval_bug", tout << "(N, P) #" << call_id << "\n";);
                SASSERT(is_P1(i2));
                
                set_upper_is_open(r, is_N0(i1) ? false : (b_o || d_o));
                set_lower_is_open(r, a_o || c_o);
                
                if (m().is_zero(c)) {
                    SASSERT(c_o);
                    m().reset(new_l_val);
                    new_l_kind = EN_MINUS_INFINITY;
                }
                else {
                    round_to_minus_inf();
                    ::div(m(), a, a_k, c, c_k, new_l_val, new_l_kind);
                }
                round_to_plus_inf();
                ::div(m(), b, b_k, d, d_k, new_u_val, new_u_kind);
            }
        }
        else if (is_M(i1)) {
            if (is_N1(i2)) {
                // 0 < a <= x <= b < 0,  y <= d < 0   --> b/d <= x/y
                // 0 < a <= x <= b < 0,  y <= d < 0   -->        x/y <= a/d
                TRACE("interval_bug", tout << "(M, N) #" << call_id << "\n";);
                
                set_lower_is_open(r, b_o || d_o);
                set_upper_is_open(r, a_o || d_o); 
                
                if (m().is_zero(d)) {
                    SASSERT(d_o);
                    m().reset(new_l_val); m().reset(new_u_val);
                    new_l_kind = EN_MINUS_INFINITY;
                    new_u_kind = EN_PLUS_INFINITY;
                }
                else {
                    round_to_minus_inf();
                    ::div(m(), b, b_k, d, d_k, new_l_val, new_l_kind);
                    round_to_plus_inf();
                    ::div(m(), a, a_k, d, d_k, new_u_val, new_u_kind);
                    TRACE("interval_bug", tout << "new_l_kind: " << new_l_kind << ", new_u_kind: " << new_u_kind << "\n";);
                }
            }
            else {
                // 0 < a <= x <= b < 0, 0 < c <= y  --> a/c <= x/y
                // 0 < a <= x <= b < 0, 0 < c <= y  -->        x/y <= b/c

                TRACE("interval_bug", tout << "(M, P) #" << call_id << "\n";);
                SASSERT(is_P1(i2));
                
                set_lower_is_open(r, a_o || c_o);
                set_upper_is_open(r, b_o || c_o); 
                
                if (m().is_zero(c)) {
                    SASSERT(c_o);
                    m().reset(new_l_val); m().reset(new_u_val);
                    new_l_kind = EN_MINUS_INFINITY;
                    new_u_kind = EN_PLUS_INFINITY;
                }
                else {
                    round_to_minus_inf();
                    ::div(m(), a, a_k, c, c_k, new_l_val, new_l_kind);
                    round_to_plus_inf();
                    ::div(m(), b, b_k, c, c_k, new_u_val, new_u_kind);
                }
            }
        }
        else {
            SASSERT(is_P(i1));        
            if (is_N1(i2)) {
                // b > 0,    x <= b,   c <= y <= d < 0    -->  b/d <= x/y
                // 0 <= a <= x,        c <= y <= d < 0    -->         x/y  <= a/c
                TRACE("interval_bug", tout << "(P, N) #" << call_id << "\n";);
                
                set_upper_is_open(r, is_P0(i1) ? false : a_o || c_o);
                set_lower_is_open(r, b_o || d_o);
                
                if (m().is_zero(d)) {
                    SASSERT(d_o);
                    m().reset(new_l_val);
                    new_l_kind = EN_MINUS_INFINITY;
                }
                else {
                    round_to_minus_inf();
                    ::div(m(), b, b_k, d, d_k, new_l_val, new_l_kind);
                }
                round_to_plus_inf();
                ::div(m(), a, a_k, c, c_k, new_u_val, new_u_kind);
            }
            else {
                SASSERT(is_P1(i2));
                // 0 <= a <= x,      0 < c <= y <= d    -->   a/d <= x/y
                // b > 0     x <= b, 0 < c <= y         -->          x/y <= b/c
                TRACE("interval_bug", tout << "(P, P) #" << call_id << "\n";);
                
                set_lower_is_open(r, is_P0(i1) ? false : a_o || d_o);
                set_upper_is_open(r, b_o || c_o);
                
                round_to_minus_inf();
                ::div(m(), a, a_k, d, d_k, new_l_val, new_l_kind);
                if (m().is_zero(c)) {
                    SASSERT(c_o);
                    m().reset(new_u_val);
                    new_u_kind = EN_PLUS_INFINITY;
                }
                else {
                    round_to_plus_inf();
                    ::div(m(), b, b_k, c, c_k, new_u_val, new_u_kind);
                }
            }
        }
        
        m().swap(lower(r), new_l_val);
        m().swap(upper(r), new_u_val);
        set_lower_is_inf(r, new_l_kind == EN_MINUS_INFINITY);
        set_upper_is_inf(r, new_u_kind == EN_PLUS_INFINITY);
    }
    TRACE("interval_bug", tout << "result: "; display(tout, r); tout << "\n";);
#ifdef _TRACE
    call_id++;
#endif
}

template<typename C>
void interval_manager<C>::pi_series(int x, numeral & r, bool up) {
    // Store in r the value:  1/16^x (4/(8x + 1) - 2/(8x + 4) - 1/(8x + 5) - 1/(8x + 6))
    _scoped_numeral<numeral_manager> f(m());
    set_rounding(up);
    m().set(r, 4, 8*x + 1);
    set_rounding(!up);  
    m().set(f, 2, 8*x + 4);
    set_rounding(up);
    m().sub(r, f, r);
    set_rounding(!up);  
    m().set(f, 1, 8*x + 5);
    set_rounding(up);
    m().sub(r, f, r);
    set_rounding(!up);
    m().set(f, 1, 8*x + 6); 
    set_rounding(up);
    m().sub(r, f, r);
    m().set(f, 1, 16);
    m().power(f, x, f);
    m().mul(r, f, r);
}

template<typename C>
void interval_manager<C>::pi(unsigned n, interval & r) {
    // Compute an interval that contains pi using the series 
    //   P[0] + P[1] + ... + P[n]
    // where
    //   P[n] := 1/16^x (4/(8x + 1) - 2/(8x + 4) - 1/(8x + 5) - 1/(8x + 6))
    // 
    // The size of the interval is 1/15 * 1/(16^n)
    //
    // Lower is P[0] + P[1] + ... + P[n]
    // Upper is Lower + 1/15 * 1/(16^n)
    
    // compute size of the resulting interval
    round_to_plus_inf(); // overestimate size of the interval
    _scoped_numeral<numeral_manager> len(m());
    _scoped_numeral<numeral_manager> p(m());
    m().set(len, 1, 16);
    m().power(len, n, len);
    m().set(p, 1, 15);
    m().mul(p, len, len);
    
    // compute lower bound
    numeral & l_val = m_result_lower;
    m().reset(l_val);
    for (unsigned i = 0; i <= n; i++) {
        pi_series(i, p, false);
        round_to_minus_inf();
        m().add(l_val, p, l_val);
    }
    
    // computer upper bound
    numeral & u_val = m_result_upper;
    if (m().precise()) {
        // the numeral manager is precise, so we do not need to recompute the series
        m().add(l_val, len, u_val);
    }
    else {
        // recompute the sum rounding to plus infinite
        m().reset(u_val);
        for (unsigned i = 0; i <= n; i++) {
            pi_series(i, p, true);
            round_to_plus_inf();
            m().add(u_val, p, u_val);
        }
        round_to_plus_inf();
        m().add(u_val, len, u_val);
    }

    set_lower_is_open(r, false);
    set_upper_is_open(r, false);
    set_lower_is_inf(r, false);
    set_upper_is_inf(r, false);
    m().set(lower(r), l_val);
    m().set(upper(r), u_val);
}

template<typename C>
void interval_manager<C>::set_pi_prec(unsigned n) {
    SASSERT(n > 0);
    m_pi_n = n;
    pi(n, m_pi);
    mul(1, 2, m_pi, m_pi_div_2);
    mul(3, 2, m_pi, m_3_pi_div_2);
    mul(2, 1, m_pi, m_2_pi);
}

template<typename C>
void interval_manager<C>::set_pi_at_least_prec(unsigned n) {
    if (n > m_pi_n)
        set_pi_prec(n);
}

template<typename C>
void interval_manager<C>::e_series(unsigned k, bool upper, numeral & o) {
    _scoped_numeral<numeral_manager> d(m()), a(m());
    m().set(o, 2);
    m().set(d, 1);
    for (unsigned i = 2; i <= k; i++) {
        set_rounding(!upper);
        m().set(a, static_cast<int>(i));
        m().mul(d, a, d); // d == i!
        m().set(a, d);
        set_rounding(upper);
        m().inv(a);       // a == 1/i!
        m().add(o, a, o);
    }
}

template<typename C>
void interval_manager<C>::e(unsigned k, interval & r) {
    // Store in r lower and upper bounds for Euler's constant.
    // 
    // The procedure uses the series
    //
    // V = 1 + 1/1 + 1/2! + 1/3! + ... + 1/k!
    //
    // The error in the approximation above is <= E = 4/(k+1)!
    // Thus, e must be in the interval [V, V+E]
    numeral & lo = m_result_lower;
    numeral & hi = m_result_upper;

    e_series(k, false, lo);

    _scoped_numeral<numeral_manager> error(m()), aux(m());
    round_to_minus_inf();
    fact(k+1, error);
    round_to_plus_inf();
    m().inv(error);      // error == 1/(k+1)!
    m().set(aux, 4);     
    m().mul(aux, error, error); // error == 4/(k+1)!
    
    if (m().precise()) {
        m().set(hi, lo);
        m().add(hi, error, hi);
    }
    else {
        e_series(k, true, hi);
        round_to_plus_inf();
        m().add(hi, error, hi);
    }

    set_lower_is_open(r, false);
    set_upper_is_open(r, false);
    set_lower_is_inf(r, false);
    set_upper_is_inf(r, false);
    m().set(lower(r), lo);
    m().set(upper(r), hi);
}

#endif
