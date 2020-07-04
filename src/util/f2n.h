/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    f2n.h

Abstract:

    Template for wrapping a float-like API as a numeral-like API.
    The basic idea is to have the rounding mode as an implicit argument.

Author:

    Leonardo de Moura (leonardo) 2012-07-30.

Revision History:

--*/
#pragma once

#include "util/mpf.h"

template<typename fmanager>
class f2n {
public:
    typedef typename fmanager::numeral numeral;
    struct exception {};

private:
    fmanager &        m_manager;
    mpf_rounding_mode m_mode;
    unsigned          m_ebits;
    unsigned          m_sbits;
    numeral           m_tmp1;
    numeral           m_one;
    
    void check(numeral const & n) { if (!m().is_regular(n)) throw exception(); }

public:
    static bool field() { return true; }
    static bool precise() { return false; }
    
    f2n(fmanager & m, unsigned ebits = 11, unsigned sbits = 53):m_manager(m), m_mode(MPF_ROUND_TOWARD_POSITIVE), m_ebits(ebits), m_sbits(sbits) {
        m_manager.set(m_one, ebits, sbits, 1);
    }

    f2n(f2n && other) : m_manager(other.m_manager), m_mode(other.m_mode), m_ebits(other.m_ebits), m_sbits(other.m_sbits),
        m_tmp1(std::move(other.m_tmp1)), m_one(std::move(other.m_one)) {}

    ~f2n() { 
        m().del(m_tmp1); 
        m().del(m_one); 
    }
    
    void set_rounding_mode(mpf_rounding_mode m) { m_mode = m; }
    mpf_rounding_mode rounding_mode() const { return m_mode; }
    void round_to_plus_inf() { m_mode = MPF_ROUND_TOWARD_POSITIVE; }
    void round_to_minus_inf() { m_mode = MPF_ROUND_TOWARD_NEGATIVE; }
    void set_rounding(bool to_plus_inf) { if (to_plus_inf) round_to_plus_inf(); else round_to_minus_inf(); }
    unsigned ebits() const { return m_ebits; }
    unsigned sbits() const { return m_sbits; }

    fmanager & m() const { return m_manager; }

    double to_double(numeral & x) const { return m().to_double(x); }

    void del(numeral & x) { m().del(x); }

    void abs(numeral & o) { m().abs(o); }
    void abs(numeral const & x, numeral & o) { m().abs(x, o); }

    void neg(numeral & o) { m().neg(o); }
    void neg(numeral const & x, numeral & o) { m().neg(x, o); }

    bool is_zero(numeral const & x) { return m().is_zero(x); }
    bool is_neg(numeral const & x) { return m().is_neg(x) && !m().is_zero(x); /* it is not clear whether actual hardware returns true for is_neg(0-) */ }
    bool is_pos(numeral const & x) { return m().is_pos(x) && !m().is_zero(x); }
    bool is_nonneg(numeral const & x) { return !is_neg(x); }
    bool is_nonpos(numeral const & x) { return !is_pos(x); }

    void set(numeral & o, int value) { m().set(o, m_ebits, m_sbits, value); check(o); }
    void set(numeral & o, int n, int d) { m().set(o, m_ebits, m_sbits, m_mode, n, d); check(o); }
    void set(numeral & o, double x) { m().set(o, m_ebits, m_sbits, x); check(o); }
    void set(numeral & o, unsigned value) { m().set(o, m_ebits, m_sbits, (double)value); check(o); }
    void set(numeral & o, numeral const & x) { m().set(o, x); check(o); }
    void set(numeral & o, mpq const & x) { m().set(o, m_ebits, m_sbits, m_mode, x); check(o); }
    void reset(numeral & o) { m().reset(o, m_ebits, m_sbits); }
    static void swap(numeral & x, numeral & y) { x.swap(y); }
    
    void add(numeral const & x, numeral const & y, numeral & o) { m().add(m_mode, x, y, o); check(o); }
    void sub(numeral const & x, numeral const & y, numeral & o) { m().sub(m_mode, x, y, o); check(o); }
    void mul(numeral const & x, numeral const & y, numeral & o) { m().mul(m_mode, x, y, o); check(o); }
    void div(numeral const & x, numeral const & y, numeral & o) { m().div(m_mode, x, y, o); check(o); }
    void inv(numeral & o) { numeral a; set(a, 1); div(a, o, o); del(a);  check(o); }
    void inv(numeral const & x, numeral & o) { set(o, x); inv(o); }
    void inc(numeral & x) { add(x, m_one, x); }
    void dec(numeral & x) { sub(x, m_one, x); }

    void power(numeral const & a, unsigned p, numeral & b) {
        unsigned mask = 1;
        numeral power;
        set(power, a);
        set(b, 1);
        while (mask <= p) {
            if (mask & p)
                mul(b, power, b);
            mul(power, power, power);
            mask = mask << 1;
        }
        del(power);
        check(b);
    }
    
    // Store the floor of a into b. Return true if a is an integer.
    // Throws an exception if the result cannot be computed precisely.
    void floor(numeral const & a, numeral & b) {
        SASSERT(m().is_regular(a));
        // Claim: If a is a regular float, then floor(a) is an integer that can be precisely represented.
        // Justification: (for the case a is nonnegative)
        //       If 0 <= a  > 2^sbits(), then a is an integer, and floor(a) == a
        //       If 0 <= a <= 2^sbits(), then floor(a) is representable since every integer less than 2^sbit
        m().round_to_integral(MPF_ROUND_TOWARD_NEGATIVE, a, m_tmp1);
        SASSERT(m().is_regular(m_tmp1));
        if (m().le(m_tmp1, a)) {
            m().set(b, m_tmp1);
        }
        else {
            // the rounding mode doesn't matter for the following operation.
            m().sub(MPF_ROUND_TOWARD_NEGATIVE, m_tmp1, m_one, b);
        }
        SASSERT(m().is_regular(b));
    }

    void ceil(numeral const & a, numeral & b) {
        SASSERT(m().is_regular(a));
        // See comment in floor
        m().round_to_integral(MPF_ROUND_TOWARD_POSITIVE, a, m_tmp1);
        SASSERT(m().is_regular(m_tmp1));
        if (m().ge(m_tmp1, a)) {
            m().set(b, m_tmp1);
        }
        else {
            // the rounding mode doesn't matter for the following operation.
            m().add(MPF_ROUND_TOWARD_NEGATIVE, m_tmp1, m_one, b);
        }
        SASSERT(m().is_regular(b));
    }

    unsigned prev_power_of_two(numeral const & a) { return m().prev_power_of_two(a); }
    
    bool eq(numeral const & x, numeral const & y) { return m().eq(x, y); }
    bool lt(numeral const & x, numeral const & y) { return m().lt(x, y); }
    bool le(numeral const & x, numeral const & y) { return m().le(x, y); }
    bool gt(numeral const & x, numeral const & y) { return m().gt(x, y); }
    bool ge(numeral const & x, numeral const & y) { return m().ge(x, y); }

    bool is_int(numeral const & x) { return m().is_int(x); }
    bool is_one(numeral const & x) { return m().is_one(x); }
    bool is_minus_one(numeral const & x) { numeral & _x = const_cast<numeral &>(x); m().neg(_x); bool r = m().is_one(_x); m().neg(_x); return r; }

    std::string to_string(numeral const & a) { return m().to_string(a); }
    std::string to_rational_string(numeral const & a) { return m().to_rational_string(a); }
    void display(std::ostream & out, numeral const & a) { out << to_string(a); }
    void display_decimal(std::ostream & out, numeral const & a, unsigned k) { m().display_decimal(out, a, k); }
    void display_smt2(std::ostream & out, numeral const & a, bool decimal) { m().display_smt2(out, a, decimal); }
};

