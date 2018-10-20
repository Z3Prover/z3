/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    mpf.cpp

Abstract:

    Multi Precision Floating Point Numbers

Author:

    Christoph Wintersteiger (cwinter) 2011-12-01.

Revision History:

--*/
#include<sstream>
#include<iomanip>
#include "util/mpf.h"

mpf::mpf() :
    ebits(0),
    sbits(0),
    sign(false),
    significand(0),
    exponent(0) {
}

void mpf::set(unsigned _ebits, unsigned _sbits) {
    ebits       = _ebits;
    sbits       = _sbits;
    sign        = false;
    exponent    = 0;
}

mpf::mpf(unsigned _ebits, unsigned _sbits):
    significand(0) {
    set(ebits, sbits);
}

mpf::~mpf() {
}

void mpf::swap(mpf & other) {
    unsigned tmp = ebits;
    ebits = other.ebits;
    other.ebits = tmp;
    tmp = sbits;
    sbits = other.sbits;
    other.sbits = tmp;
    tmp = sign;
    sign = other.sign;
    other.sign = tmp;
    significand.swap(other.significand);
    std::swap(exponent, other.exponent);
}


mpf_manager::mpf_manager() :
    m_mpz_manager(m_mpq_manager),
    m_powers2(m_mpz_manager) {
}

mpf_manager::~mpf_manager() {
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, int value) {
    static_assert(sizeof(int) == 4, "assume integers are 4 bytes");

    o.sign = false;
    o.ebits = ebits;
    o.sbits = sbits;

    TRACE("mpf_dbg", tout << "set: value = " << value << std::endl;);
    if (value == 0) {
        mk_pzero(ebits, sbits, o);
    }
    else {
        unsigned uval=value;
        if (value < 0) {
            o.sign = true;
            if (value == INT_MIN)
                uval = 0x80000000;
            else
                uval = -value;
        }

        o.exponent = 31;
        while ((uval & 0x80000000) == 0) {
            uval <<= 1;
            o.exponent--;
        }

        m_mpz_manager.set(o.significand, uval & 0x7FFFFFFF); // remove the "1." part

        // align with sbits.
        if (sbits > 31)
            m_mpz_manager.mul2k(o.significand, sbits-32);
        else
            m_mpz_manager.machine_div2k(o.significand, 32-sbits);
    }

    TRACE("mpf_dbg", tout << "set: res = " << to_string(o) << std::endl;);
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, int n, int d) {
    scoped_mpq tmp(m_mpq_manager);
    m_mpq_manager.set(tmp, n, d);
    set(o, ebits, sbits, rm, tmp);
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, double value) {
    // double === mpf(11, 53)
    static_assert(sizeof(double) == 8, "doubles are 8 bytes");

    uint64_t raw;
    memcpy(&raw, &value, sizeof(double));
    bool sign = (raw >> 63) != 0;
    int64_t e =  ((raw & 0x7FF0000000000000ull) >> 52) - 1023;
    uint64_t s = raw & 0x000FFFFFFFFFFFFFull;

    TRACE("mpf_dbg", tout << "set: " << value << " is: raw=" << raw << " (double)" <<
                          " sign=" << sign << " s=" << s << " e=" << e << std::endl;);

    SASSERT(-1023 <= e && e <= +1024);

    o.ebits = ebits;
    o.sbits = sbits;
    o.sign = sign;

    if (e <= -((0x01ll<<(ebits-1))-1))
        o.exponent = mk_bot_exp(ebits);
    else if (e >= (0x01ll<<(ebits-1)))
        o.exponent = mk_top_exp(ebits);
    else
        o.exponent = e;

    m_mpz_manager.set(o.significand, s);

    if (sbits < 53)
        m_mpz_manager.machine_div2k(o.significand, 53-sbits);
    else if (sbits > 53)
        m_mpz_manager.mul2k(o.significand, sbits-53);

    TRACE("mpf_dbg", tout << "set: res = " << to_string(o) << std::endl;);
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, float value) {
    // single === mpf(8, 24)
    static_assert(sizeof(float) == 4, "floats are 4 bytes");

    unsigned int raw;
    memcpy(&raw, &value, sizeof(float));
    bool sign = (raw >> 31) != 0;
    signed int e = ((raw & 0x7F800000) >> 23) - 127;
    unsigned int s = raw & 0x007FFFFF;

    TRACE("mpf_dbg", tout << "set: " << value << " is: raw=" << raw << " (float)" <<
                             " sign=" << sign << " s=" << s << " e=" << e << std::endl;);

    SASSERT(-127 <= e && e <= +128);

    o.ebits = ebits;
    o.sbits = sbits;
    o.sign = sign;

    if (e <= -((0x01ll<<(ebits-1))-1))
        o.exponent = mk_bot_exp(ebits);
    else if (e >= (0x01ll<<(ebits-1)))
        o.exponent = mk_top_exp(ebits);
    else
        o.exponent = e;

    m_mpz_manager.set(o.significand, s);

    if (sbits < 24)
        m_mpz_manager.machine_div2k(o.significand, 24-sbits);
    else if (sbits > 24)
        m_mpz_manager.mul2k(o.significand, sbits-24);

    TRACE("mpf_dbg", tout << "set: res = " << to_string_raw(o) << std::endl;);
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, mpq const & value) {
    TRACE("mpf_dbg", tout << "set: " << m_mpq_manager.to_string(value) << " [" << ebits << "/" << sbits << "]"<< std::endl;);
    scoped_mpz exp(m_mpz_manager);
    m_mpz_manager.set(exp, 0);
    set(o, ebits, sbits, rm, exp, value);
    TRACE("mpf_dbg", tout << "set: res = " << to_string(o) << std::endl;);
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, char const * value) {
    TRACE("mpf_dbg", tout << "set: " << value << " [" << ebits << "/" << sbits << "]"<< std::endl;);

    o.ebits = ebits;
    o.sbits = sbits;

    // We expect [i].[f]P[e], where P means that the exponent is interpreted as 2^e instead of 10^e.

    std::string v(value);

    std::string f, e;
    bool sgn = false;

    if (v.substr(0, 1) == "-") {
        sgn = true;
        v = v.substr(1);
    }
    else if (v.substr(0, 1) == "+")
        v = v.substr(1);

    size_t e_pos = v.find('p');
    if (e_pos == std::string::npos) e_pos = v.find('P');
    f = (e_pos != std::string::npos) ? v.substr(0, e_pos) : v;
    e = (e_pos != std::string::npos) ? v.substr(e_pos+1) : "0";

    TRACE("mpf_dbg", tout << "sgn = " << sgn << " f = " << f << " e = " << e << std::endl;);

    scoped_mpq q(m_mpq_manager);
    m_mpq_manager.set(q, f.c_str());

    scoped_mpz ex(m_mpq_manager);
    m_mpz_manager.set(ex, e.c_str());

    set(o, ebits, sbits, rm, ex, q);
    o.sign = sgn;

    TRACE("mpf_dbg", tout << "set: res = " << to_string(o) << std::endl;);
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, mpz const & exponent, mpq const & significand) {
    // Assumption: this represents significand * 2^exponent.
    TRACE("mpf_dbg", tout << "set: sig = " << m_mpq_manager.to_string(significand) << " exp = " << m_mpz_manager.to_string(exponent) << std::endl;);

    o.ebits = ebits;
    o.sbits = sbits;
    o.sign = m_mpq_manager.is_neg(significand);

    if (m_mpq_manager.is_zero(significand))
        mk_zero(ebits, sbits, o.sign, o);
    else {
        scoped_mpq sig(m_mpq_manager);
        scoped_mpz exp(m_mpq_manager);

        m_mpq_manager.set(sig, significand);
        m_mpq_manager.abs(sig);
        m_mpz_manager.set(exp, exponent);

        // Normalize such that 1.0 <= sig < 2.0
        if (m_mpq_manager.lt(sig, 1)) {
            m_mpq_manager.inv(sig);
            unsigned int pp = m_mpq_manager.prev_power_of_two(sig);
            if (!m_mpq_manager.is_power_of_two(sig, pp)) pp++;
            scoped_mpz p2(m_mpz_manager);
            m_mpq_manager.power(2, pp, p2);
            m_mpq_manager.div(sig, p2, sig);
            m_mpz_manager.sub(exp, mpz(pp), exp);
            m_mpq_manager.inv(sig);
        }
        else if (m_mpq_manager.ge(sig, 2)) {
            unsigned int pp = m_mpq_manager.prev_power_of_two(sig);
            scoped_mpz p2(m_mpz_manager);
            m_mpq_manager.power(2, pp, p2);
            m_mpq_manager.div(sig, p2, sig);
            m_mpz_manager.add(exp, mpz(pp), exp);
        }

        TRACE("mpf_dbg", tout << "Normalized: sig = " << m_mpq_manager.to_string(sig) <<
                                 " exp = " << m_mpz_manager.to_string(exp) << std::endl;);

        // Check that 1.0 <= sig < 2.0
        SASSERT((m_mpq_manager.le(1, sig) && m_mpq_manager.lt(sig, 2)));

        scoped_mpz p(m_mpq_manager);
        scoped_mpq t(m_mpq_manager), sq(m_mpq_manager);
        m_mpz_manager.power(2, sbits + 3 - 1, p);
        m_mpq_manager.mul(p, sig, t);
        m_mpq_manager.floor(t, o.significand);
        m_mpq_manager.set(sq, o.significand);
        m_mpq_manager.div(sq, p, t);
        m_mpq_manager.sub(sig, t, sig);

        // sticky
        if (!m_mpq_manager.is_zero(sig) && m_mpz_manager.is_even(o.significand))
            m_mpz_manager.inc(o.significand);

        TRACE("mpf_dbg", tout << "sig = " << m_mpz_manager.to_string(o.significand) <<
                                 " exp = " << o.exponent << std::endl;);

        if (m_mpz_manager.is_small(exp)) {
            o.exponent = m_mpz_manager.get_int64(exp);
            round(rm, o);
        }
        else
            mk_inf(ebits, sbits, o.sign, o);
    }

    TRACE("mpf_dbg", tout << "set: res = " << to_string(o) << std::endl;);
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, bool sign, mpf_exp_t exponent, uint64_t significand) {
    // Assumption: this represents (sign * -1) * (significand/2^sbits) * 2^exponent.
    o.ebits = ebits;
    o.sbits = sbits;
    o.sign = sign;
    m_mpz_manager.set(o.significand, significand);
    o.exponent = exponent;

    DEBUG_CODE({
        SASSERT(m_mpz_manager.lt(o.significand, m_powers2(sbits-1)));
        SASSERT(o.exponent <= mk_top_exp(ebits));
        SASSERT(o.exponent >= mk_bot_exp(ebits));
    });
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, bool sign, mpf_exp_t exponent, mpz const & significand) {
    // Assumption: this represents (sign * -1) * (significand/2^sbits) * 2^exponent.
    o.ebits = ebits;
    o.sbits = sbits;
    o.sign = sign;
    m_mpz_manager.set(o.significand, significand);
    o.exponent = exponent;
}

void mpf_manager::set(mpf & o, mpf const & x) {
    o.ebits = x.ebits;
    o.sbits = x.sbits;
    o.sign = x.sign;
    o.exponent = x.exponent;
    m_mpz_manager.set(o.significand, x.significand);
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, mpf const & x) {
    if (is_nan(x))
        mk_nan(ebits, sbits, o);
    else if (is_inf(x))
        mk_inf(ebits, sbits, x.sign, o);
    else if (is_zero(x))
        mk_zero(ebits, sbits, x.sign, o);
    else if (x.ebits == ebits && x.sbits == sbits)
        set(o, x);
    else {
        set(o, x);
        unpack(o, true);

        o.ebits = ebits;
        o.sbits = sbits;

        signed ds = sbits - x.sbits + 3;  // plus rounding bits
        if (ds > 0)
        {
            m_mpz_manager.mul2k(o.significand, ds);
            round(rm, o);
        }
        else if (ds < 0)
        {
            bool sticky = false;
            while (ds < 0)
            {
                sticky |= m_mpz_manager.is_odd(o.significand);
                m_mpz_manager.machine_div2k(o.significand, 1);
                ds++;
            }
            if (sticky && m_mpz_manager.is_even(o.significand))
                m_mpz_manager.inc(o.significand);
            round(rm, o);
        }
    }
}

void mpf_manager::abs(mpf & o) {
    o.sign = false;
}

void mpf_manager::abs(mpf const & x, mpf & o) {
    set(o, x);
    abs(o);
}

void mpf_manager::neg(mpf & o) {
    if (!is_nan(o))
        o.sign = !o.sign;
}

void mpf_manager::neg(mpf const & x, mpf & o) {
    set(o, x);
    neg(o);
}

bool mpf_manager::is_zero(mpf const & x) {
    return has_bot_exp(x) && m_mpz_manager.is_zero(sig(x));
}

bool mpf_manager::is_one(mpf const & x) {
    return m_mpz_manager.is_zero(sig(x)) && exp(x) == 0;
}

bool mpf_manager::is_neg(mpf const & x) {
    return x.sign && !is_nan(x);
}

bool mpf_manager::is_pos(mpf const & x) {
    return !x.sign && !is_nan(x);
}

bool mpf_manager::is_nzero(mpf const & x) {
    return x.sign && is_zero(x);
}

bool mpf_manager::is_pzero(mpf const & x) {
    return !x.sign && is_zero(x);
}

bool mpf_manager::eq(mpf const & x, mpf const & y) {
    SASSERT(x.sbits == y.sbits && x.ebits == y.ebits);
    if (is_nan(x) || is_nan(y))
        return false;
    else if (is_zero(x) && is_zero(y))
        return true;
    else if (sgn(x) != sgn(y))
        return false;
    else
        return exp(x)==exp(y) && m_mpz_manager.eq(sig(x), sig(y));
}

bool mpf_manager::lt(mpf const & x, mpf const & y) {
    SASSERT(x.sbits == y.sbits && x.ebits == y.ebits);
    if (is_nan(x) || is_nan(y))
        return false;
    else if (is_zero(x) && is_zero(y))
        return false;
    else if (sgn(x)) {
        if (!sgn(y))
            return true;
        else
            return exp(y) < exp(x) ||
                   (exp(y) == exp(x) && m_mpz_manager.lt(sig(y), sig(x)));
    }
    else { // !sgn(x)
        if (sgn(y))
            return false;
        else
            return exp(x) < exp(y) ||
                   (exp(x)==exp(y) && m_mpz_manager.lt(sig(x), sig(y)));
    }
}

bool mpf_manager::lte(mpf const & x, mpf const & y) {
    SASSERT(x.sbits == y.sbits && x.ebits == y.ebits);
    return lt(x, y) || eq(x, y);
}

bool mpf_manager::gt(mpf const & x, mpf const & y) {
    SASSERT(x.sbits == y.sbits && x.ebits == y.ebits);
    if (is_nan(x) || is_nan(y))
        return false;
    else if (is_zero(x) && is_zero(y))
        return false;
    else
        return !lte(x, y);
}

bool mpf_manager::gte(mpf const & x, mpf const & y) {
    SASSERT(x.sbits == y.sbits && x.ebits == y.ebits);
    return gt(x, y) || eq(x, y);
}

void mpf_manager::add(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf & o) {
    add_sub(rm, x, y, o, false);
}

void mpf_manager::sub(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf & o) {
    add_sub(rm, x, y, o, true);
}

void mpf_manager::add_sub(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf & o, bool sub) {
    SASSERT(x.sbits == y.sbits && x.ebits == y.ebits);

    bool sgn_y = sgn(y) ^ sub;

    if (is_nan(x))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_nan(y))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_inf(x)) {
        if (is_inf(y) && (sgn(x) ^ sgn_y))
            mk_nan(x.ebits, x.sbits, o);
        else
            set(o, x);
    }
    else if (is_inf(y)) {
        if (is_inf(x) && (sgn(x) ^ sgn_y))
            mk_nan(x.ebits, x.sbits, o);
        else {
            set(o, y);
            o.sign = sgn_y;
        }
    }
    else if (is_zero(x) && is_zero(y)) {
        if ((x.sign && sgn_y) ||
            ((rm == MPF_ROUND_TOWARD_NEGATIVE) && (x.sign != sgn_y)))
            mk_nzero(x.ebits, x.sbits, o);
        else
            mk_pzero(x.ebits, x.sbits, o);
    }
    else if (is_zero(x)) {
        set(o, y);
        o.sign = sgn_y;
    }
    else if (is_zero(y))
        set(o, x);
    else {
        o.ebits = x.ebits;
        o.sbits = x.sbits;

        SASSERT(is_normal(x) || is_denormal(x));
        SASSERT(is_normal(y) || is_denormal(y));

        scoped_mpf a(*this), b(*this);
        set(a, x);
        set(b, y);
        b.get().sign = sgn_y;

        // Unpack a/b, this inserts the hidden bit and adjusts the exponent.
        unpack(a, false);
        unpack(b, false);

        if (exp(b) > exp(a))
            a.swap(b);

        mpf_exp_t exp_delta = exp(a) - exp(b);

        SASSERT(exp(a) >= exp(b));
        SASSERT(exp_delta >= 0);

        if (exp_delta > x.sbits+2)
            exp_delta = x.sbits+2;

        TRACE("mpf_dbg", tout << "A  = " << to_string(a) << std::endl;);
        TRACE("mpf_dbg", tout << "B  = " << to_string(b) << std::endl;);
        TRACE("mpf_dbg", tout << "d  = " << exp_delta << std::endl;);

        // Introduce 3 extra bits into both numbers.
        m_mpz_manager.mul2k(a.significand(), 3, a.significand());
        m_mpz_manager.mul2k(b.significand(), 3, b.significand());

        // Alignment shift with sticky bit computation.
        SASSERT(exp_delta <= INT_MAX);
        scoped_mpz sticky_rem(m_mpz_manager);
        m_mpz_manager.machine_div_rem(b.significand(), m_powers2((int)exp_delta), b.significand(), sticky_rem);

        TRACE("mpf_dbg", tout << "A' = " << m_mpz_manager.to_string(a.significand()) << std::endl;);
        TRACE("mpf_dbg", tout << "B' = " << m_mpz_manager.to_string(b.significand()) << std::endl;);

        // Significand addition
        if (sgn(a) != sgn(b)) {
            TRACE("mpf_dbg", tout << "SUBTRACTING" << std::endl;);
            m_mpz_manager.sub(a.significand(), b.significand(), o.significand);
            if (!sticky_rem.is_zero() && m_mpz_manager.is_even(o.significand))
                m_mpz_manager.dec(o.significand);
        }
        else {
            TRACE("mpf_dbg", tout << "ADDING" << std::endl;);
            m_mpz_manager.add(a.significand(), b.significand(), o.significand);
            if (!sticky_rem.is_zero() && m_mpz_manager.is_even(o.significand))
                m_mpz_manager.inc(o.significand);
        }

        TRACE("mpf_dbg", tout << "sum[-2:sbits+2] = " << m_mpz_manager.to_string(o.significand) << std::endl;);

        if (m_mpz_manager.is_zero(o.significand))
            mk_zero(o.ebits, o.sbits, rm == MPF_ROUND_TOWARD_NEGATIVE, o);
        else {
            bool neg = m_mpz_manager.is_neg(o.significand);
            TRACE("mpf_dbg", tout << "NEG=" << neg << std::endl;);
            m_mpz_manager.abs(o.significand);
            TRACE("mpf_dbg", tout << "fs[-1:sbits+2] = " << m_mpz_manager.to_string(o.significand) << std::endl;);
            o.sign = ((!a.sign() &&  b.sign() &&  neg) ||
                      ( a.sign() && !b.sign() && !neg) ||
                      ( a.sign() &&  b.sign()));
            o.exponent = a.exponent();
            round(rm, o);
        }
    }
}

void mpf_manager::mul(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf & o) {
    TRACE("mpf_mul_bug", tout << "rm: " << rm << "\n";
          tout << "X: " << to_string(x) << "\n";
          tout << "Y: " << to_string(y) << "\n";);
    SASSERT(x.sbits == y.sbits && x.ebits == y.ebits);

    TRACE("mpf_dbg", tout << "X = " << to_string(x) << std::endl;);
    TRACE("mpf_dbg", tout << "Y = " << to_string(y) << std::endl;);

    if (is_nan(x))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_nan(y))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_pinf(x)) {
        if (is_zero(y))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_inf(x.ebits, x.sbits, y.sign, o);
    }
    else if (is_pinf(y)) {
        if (is_zero(x))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_inf(x.ebits, x.sbits, x.sign, o);
    }
    else if (is_ninf(x)) {
        if (is_zero(y))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_inf(x.ebits, x.sbits, !y.sign, o);
    }
    else if (is_ninf(y)) {
        if (is_zero(x))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_inf(x.ebits, x.sbits, !x.sign, o);
    }
    else if (is_zero(x) || is_zero(y)) {
        mk_zero(x.ebits, x.sbits, x.sign != y.sign, o);
    }
    else {
        o.ebits = x.ebits;
        o.sbits = x.sbits;
        o.sign = x.sign ^ y.sign;

        scoped_mpf a(*this, x.ebits, x.sbits), b(*this, x.ebits, x.sbits);
        set(a, x);
        set(b, y);
        unpack(a, true);
        unpack(b, true);

        TRACE("mpf_dbg", tout << "A = " << to_string(a) << std::endl;);
        TRACE("mpf_dbg", tout << "B = " << to_string(b) << std::endl;);

        o.exponent = a.exponent() + b.exponent();

        TRACE("mpf_dbg", tout << "A' = " << m_mpz_manager.to_string(a.significand()) << std::endl;);
        TRACE("mpf_dbg", tout << "B' = " << m_mpz_manager.to_string(b.significand()) << std::endl;);

        m_mpz_manager.mul(a.significand(), b.significand(), o.significand);

        TRACE("mpf_dbg", tout << "PRODUCT = " << to_string(o) << std::endl;);

        // Remove the extra bits, keeping a sticky bit.
        scoped_mpz sticky_rem(m_mpz_manager);
        if (o.sbits >= 4)
            m_mpz_manager.machine_div_rem(o.significand, m_powers2(o.sbits - 4), o.significand, sticky_rem);
        else
            m_mpz_manager.mul2k(o.significand, 4-o.sbits, o.significand);

        if (!m_mpz_manager.is_zero(sticky_rem) && m_mpz_manager.is_even(o.significand))
            m_mpz_manager.inc(o.significand);

        round(rm, o);
    }
    TRACE("mpf_mul_bug", tout << "result: " << to_string(o) << "\n";);
}

void mpf_manager::div(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf & o) {
    SASSERT(x.sbits == y.sbits && x.ebits == y.ebits);

    TRACE("mpf_dbg", tout << "X = " << to_string(x) << std::endl;);
    TRACE("mpf_dbg", tout << "Y = " << to_string(y) << std::endl;);

    if (is_nan(x))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_nan(y))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_pinf(x)) {
        if (is_inf(y))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_inf(x.ebits, x.sbits, y.sign, o);
    }
    else if (is_pinf(y)) {
        if (is_inf(x))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_zero(x.ebits, x.sbits, x.sign != y.sign, o);
    }
    else if (is_ninf(x)) {
        if (is_inf(y))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_inf(x.ebits, x.sbits, !y.sign, o);
    }
    else if (is_ninf(y)) {
        if (is_inf(x))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_zero(x.ebits, x.sbits, x.sign != y.sign, o);
    }
    else if (is_zero(y)) {
        if (is_zero(x))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_inf(x.ebits, x.sbits, x.sign != y.sign, o);
    }
    else if (is_zero(x)) {
        // Special case to avoid problems with unpacking of zeros.
        mk_zero(x.ebits, x.sbits, x.sign != y.sign, o);
    }
    else {
        o.ebits = x.ebits;
        o.sbits = x.sbits;
        o.sign = x.sign ^ y.sign;

        scoped_mpf a(*this), b(*this);
        set(a, x);
        set(b, y);
        unpack(a, true);
        unpack(b, true);

        TRACE("mpf_dbg", tout << "A = " << to_string(a) << std::endl;);
        TRACE("mpf_dbg", tout << "B = " << to_string(b) << std::endl;);

        o.exponent = a.exponent() - b.exponent();

        TRACE("mpf_dbg", tout << "A' = " << m_mpz_manager.to_string(a.significand()) << std::endl;);
        TRACE("mpf_dbg", tout << "B' = " << m_mpz_manager.to_string(b.significand()) << std::endl;);

        unsigned extra_bits = x.sbits + 2;
        m_mpz_manager.mul2k(a.significand(), x.sbits + extra_bits);
        m_mpz_manager.machine_div(a.significand(), b.significand(), o.significand);

        TRACE("mpf_dbg", tout << "QUOTIENT = " << to_string(o) << std::endl;);

        // Remove the extra bits, keeping a sticky bit.
        scoped_mpz sticky_rem(m_mpz_manager);
        m_mpz_manager.machine_div_rem(o.significand, m_powers2(extra_bits-2), o.significand, sticky_rem);
        if (!m_mpz_manager.is_zero(sticky_rem) && m_mpz_manager.is_even(o.significand))
            m_mpz_manager.inc(o.significand);

        TRACE("mpf_dbg", tout << "QUOTIENT' = " << to_string(o) << std::endl;);

        round(rm, o);
    }
}

void mpf_manager::fma(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf const &z, mpf & o) {
    SASSERT(x.sbits == y.sbits && x.ebits == y.ebits &&
            x.sbits == y.sbits && z.ebits == z.ebits);

    TRACE("mpf_dbg", tout << "X = " << to_string(x) << std::endl;);
    TRACE("mpf_dbg", tout << "Y = " << to_string(y) << std::endl;);
    TRACE("mpf_dbg", tout << "Z = " << to_string(z) << std::endl;);

    if (is_nan(x) || is_nan(y) || is_nan(z))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_pinf(x)) {
        if (is_zero(y))
            mk_nan(x.ebits, x.sbits, o);
        else if (is_inf(z) && sgn(x) ^ sgn (y) ^ sgn(z))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_inf(x.ebits, x.sbits, y.sign, o);
    }
    else if (is_pinf(y)) {
        if (is_zero(x))
            mk_nan(x.ebits, x.sbits, o);
        else if (is_inf(z) && sgn(x) ^ sgn (y) ^ sgn(z))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_inf(x.ebits, x.sbits, x.sign, o);
    }
    else if (is_ninf(x)) {
        if (is_zero(y))
            mk_nan(x.ebits, x.sbits, o);
        else if (is_inf(z) && sgn(x) ^ sgn (y) ^ sgn(z))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_inf(x.ebits, x.sbits, !y.sign, o);
    }
    else if (is_ninf(y)) {
        if (is_zero(x))
            mk_nan(x.ebits, x.sbits, o);
        else if (is_inf(z) && sgn(x) ^ sgn (y) ^ sgn(z))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_inf(x.ebits, x.sbits, !x.sign, o);
    }
    else if (is_inf(z)) {
        set(o, z);
    }
    else if (is_zero(x) || is_zero(y)) {
        bool xy_sgn = sgn(x) ^ sgn(y);
        if (is_zero(z) && (xy_sgn ^ sgn(z)))
            mk_zero(x.ebits, x.sbits, rm == MPF_ROUND_TOWARD_NEGATIVE, o);
        else
            set(o, z);
    }
    else {
        o.ebits = x.ebits;
        o.sbits = x.sbits;

        scoped_mpf mr(*this);
        scoped_mpf a(*this, x.ebits, x.sbits), b(*this, x.ebits, x.sbits), c(*this, x.ebits, x.sbits);
        set(a, x);
        set(b, y);
        set(c, z);
        unpack(a, true);
        unpack(b, true);
        unpack(c, true);

        TRACE("mpf_dbg", tout << "A = " << to_string(a) << std::endl;
                         tout << "B = " << to_string(b) << std::endl;
                         tout << "C = " << to_string(c) << std::endl;
                         tout << "A = " << to_string_binary(a, 1, 0) << std::endl;
                         tout << "B = " << to_string_binary(b, 1, 0) << std::endl;
                         tout << "C = " << to_string_binary(c, 1, 0) << std::endl;);

        SASSERT(m_mpz_manager.lt(a.significand(), m_powers2(x.sbits)));
        SASSERT(m_mpz_manager.lt(b.significand(), m_powers2(x.sbits)));
        SASSERT(m_mpz_manager.lt(c.significand(), m_powers2(x.sbits)));
        SASSERT(m_mpz_manager.ge(a.significand(), m_powers2(x.sbits-1)));
        SASSERT(m_mpz_manager.ge(b.significand(), m_powers2(x.sbits-1)));

        // A/B in _1.[sbits-1].
        mr.set(x.ebits+2, 2*x.sbits-1, a.sign() != b.sign(), a.exponent() + b.exponent());
        m_mpz_manager.mul(a.significand(), b.significand(), mr.significand());

        TRACE("mpf_dbg", tout << "M = " << to_string(mr) << std::endl;
                         tout << "M = " << to_string_binary(mr, 1, 0) << std::endl;);

        // mul_res is [-1][0].[2*sbits - 2], i.e., >= 2^(2*sbits-2) and < 2^(2*sbits).
        SASSERT(m_mpz_manager.lt(mr.significand(), m_powers2(2*x.sbits)));
        SASSERT(m_mpz_manager.ge(mr.significand(), m_powers2(2*x.sbits - 2)));

        // Introduce (sbits+3) extra bits into c in _[0].[sbits-1] s.t. c in _[0].[2*sbits-2]
        c.set(x.ebits+2, 2*x.sbits-1+3, c.sign(), c.exponent(), c.significand());
        m_mpz_manager.mul2k(c.significand(), x.sbits - 1 + 3);
        // And + 3 bits into mr as well.
        mr.set(x.ebits + 2, 2 * x.sbits - 1 + 3, mr.sign(), mr.exponent(), mr.significand());
        m_mpz_manager.mul2k(mr.significand(), 3);

        TRACE("mpf_dbg", tout << "C_= " << to_string(c) << std::endl;
                         tout << "C_= " << to_string_binary(c, 1, 0) << std::endl;);

        SASSERT(m_mpz_manager.lt(c.significand(), m_powers2(2*x.sbits + 3)));
        SASSERT(m_mpz_manager.is_zero(c.significand()) ||
                m_mpz_manager.ge(c.significand(), m_powers2(2*x.sbits - 2 + 3)));

        if (exp(c) > exp(mr)) {
            TRACE("mpf_dbg", tout << "Swap!" << std::endl;);
            mr.swap(c);
        }

        // Alignment shift with sticky bit computation.
        mpf_exp_t exp_delta_w = exp(mr) - exp(c);
        SASSERT(exp(mr) >= exp(c) && exp_delta_w >= 0);

        if (exp_delta_w > 2 * x.sbits + 3)
            exp_delta_w = 2 * x.sbits + 3;

        unsigned exp_delta = (unsigned)exp_delta_w;

        scoped_mpz sticky_rem(m_mpz_manager);
        m_mpz_manager.machine_div_rem(c.significand(), m_powers2(exp_delta), c.significand(), sticky_rem);
        TRACE("mpf_dbg", tout << "alignment shift by delta=" << exp_delta << " -> sig = " << m_mpz_manager.to_string(c.significand()) <<
                         " sticky_rem = " << m_mpz_manager.to_string(sticky_rem) << std::endl;);
        bool alignment_sticky = !m_mpz_manager.is_zero(sticky_rem);

        TRACE("mpf_dbg", tout << "M'= " << m_mpz_manager.to_string(mr.significand()) << std::endl;
                         tout << "M'= " << to_string_binary(mr, 1, 0) << std::endl; );
        TRACE("mpf_dbg", tout << "C'= " << m_mpz_manager.to_string(c.significand()) << std::endl;
                         tout << "C'= " << to_string_binary(c, 1, 0) << std::endl; );

        // Significand addition
        scoped_mpf res(mr);

        if (sgn(mr) != sgn(c)) {
            TRACE("mpf_dbg", tout << "SUBTRACTING" << std::endl;);
            m_mpz_manager.sub(mr.significand(), c.significand(), res.significand());

            if (alignment_sticky && m_mpz_manager.is_even(res.significand()))
                m_mpz_manager.dec(res.get().significand);

            if (m_mpz_manager.is_neg(res.significand())) {
                m_mpz_manager.abs(res.significand());
                res.get().sign = !res.sign();
            }
        }
        else {
            TRACE("mpf_dbg", tout << "ADDING" << std::endl;);
            m_mpz_manager.add(mr.significand(), c.significand(), res.significand());

            if (alignment_sticky && m_mpz_manager.is_even(res.significand()))
                m_mpz_manager.inc(res.get().significand);
        }

        TRACE("mpf_dbg", tout << "S'= " << m_mpz_manager.to_string(res.significand()) << std::endl;
                         tout << "S'= " << to_string_binary(res, 1, 0) << std::endl; );

        // Renormalize
        bool renorm_sticky = false;

        SASSERT(m_mpz_manager.lt(res.significand(), m_powers2(2 * x.sbits + 1 + 3)));
        if (m_mpz_manager.ge(res.significand(), m_powers2(2 * x.sbits + 3)))
        {
            SASSERT(exp(res) < mk_max_exp(x.ebits)); // NYI.

            res.get().exponent++;
            renorm_sticky = !m_mpz_manager.is_even(res.significand());
            m_mpz_manager.machine_div2k(res.significand(), 1);
            TRACE("mpf_dbg", tout << "Add/Sub overflew into 4.xxx!" << std::endl;
                             tout << "S*= " << to_string_binary(res, 2, 0) << std::endl;);
        }

        mpf_exp_t min_exp = mk_min_exp(x.ebits);
        unsigned sig_width = m_mpz_manager.prev_power_of_two(res.get().significand) + 1;
        mpf_exp_t sig_lz = 2 * x.sbits + 3 - sig_width;
        mpf_exp_t max_exp_delta = res.exponent() - min_exp;
        unsigned renorm_delta = (unsigned) std::max((mpf_exp_t)0, std::min(sig_lz, max_exp_delta));
        res.get().exponent -= renorm_delta;
        m_mpz_manager.mul2k(res.significand(), renorm_delta);

        TRACE("mpf_dbg", tout << "R*= " << to_string_binary(res, 2, 0) << " (renormalized, delta=" << renorm_delta << ")" << std::endl;);

        set(o, x.ebits, x.sbits, res.sign(), res.exponent(), mpz(0));

        if (x.sbits >= 4) {
            m_mpz_manager.machine_div_rem(res.significand(), m_powers2(x.sbits - 4 + 3), o.significand, sticky_rem);
            renorm_sticky |= !m_mpz_manager.is_zero(sticky_rem);
        }
        else {
            m_mpz_manager.mul2k(res.significand(), 4 - x.sbits + 3, o.significand);
        }

        if (renorm_sticky && m_mpz_manager.is_even(o.significand))
            m_mpz_manager.inc(o.significand);

        TRACE("mpf_dbg", tout << "sum[-1:sbits+2] = " << m_mpz_manager.to_string(o.significand) << std::endl;
                         tout << "R = " << to_string_binary(o, 1, 3) << std::endl;);

        if (m_mpz_manager.is_zero(o.significand))
            mk_zero(x.ebits, x.sbits, rm == MPF_ROUND_TOWARD_NEGATIVE, o);
        else
            round(rm, o);
    }

}

void my_mpz_sqrt(unsynch_mpz_manager & m, unsigned sbits, bool odd_exp, mpz & in, mpz & o) {
    scoped_mpz lower(m), upper(m);
    scoped_mpz mid(m), product(m), diff(m);
    // we have lower <= a.significand <= upper and we need 1.[52+3 bits] in the bounds.
    // since we compare upper*upper to a.significand further down, we need a.significand
    // to be of twice the size.
    m.set(lower, 1);
    m.mul2k(lower, sbits+2-1);

    if (odd_exp)
        m.mul2k(in, 4, upper);
    else
        m.mul2k(in, 3, upper);

    if (m.eq(lower, upper))
        m.set(o, lower);

    while (m.neq(lower, upper)) {
        STRACE("mpf_dbg", tout << "SIG = " << m.to_string(in) <<
                                    " LOWER = " << m.to_string(lower) <<
                                    " UPPER = " << m.to_string(upper) << std::endl;);
        m.sub(upper, lower, diff);
        if (m.is_one(diff)) {
            m.mul(lower, lower, product);
            if (m.eq(product, in)) {
                STRACE("mpf_dbg", tout << "choosing lower" << std::endl;);
                m.set(o, lower);
            }
            else {
                STRACE("mpf_dbg", tout << "choosing upper" << std::endl;);
                m.set(o, upper); // choosing upper is like a sticky bit here.
            }
            break;
        }

        m.add(lower, upper, mid);
        m.machine_div2k(mid, 1);
        m.mul(mid, mid, product);

        STRACE("mpf_dbg", tout << "MID = " << m.to_string(mid) <<
                                  " PROD = " << m.to_string(product) << std::endl;);

        if (m.lt(product, in))
            m.set(lower, mid);
        else if (m.gt(product, in))
            m.set(upper, mid);
        else {
            SASSERT(m.eq(product, in));
            m.set(o, mid);
            break;
        }
    }
}

void mpf_manager::sqrt(mpf_rounding_mode rm, mpf const & x, mpf & o) {
    SASSERT(x.ebits > 0 && x.sbits > 0);

    TRACE("mpf_dbg", tout << "X = " << to_string(x) << std::endl;);

    if (is_nan(x))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_pinf(x))
        set(o, x);
    else if (is_zero(x))
        set(o, x);
    else if (x.sign)
        mk_nan(x.ebits, x.sbits, o);
    else {
        o.ebits = x.ebits;
        o.sbits = x.sbits;
        o.sign = false;

        scoped_mpf a(*this);
        set(a, x);
        unpack(a, true);

        TRACE("mpf_dbg", tout << "A = " << to_string(a) << std::endl;);

        m_mpz_manager.mul2k(a.significand(), x.sbits + ((a.exponent() % 2)?6:7));
        if (!m_mpz_manager.root(a.significand(), 2, o.significand))
        {
            // If the result is inexact, it is 1 too large.
            // We need a sticky bit in the last position here, so we fix that.
            if (m_mpz_manager.is_even(o.significand))
                m_mpz_manager.dec(o.significand);
            TRACE("mpf_dbg", tout << "dec'ed " << m_mpz_manager.to_string(o.significand) << std::endl;);
        }
        o.exponent = a.exponent() >> 1;
        if (a.exponent() % 2 == 0) o.exponent--;

        round(rm, o);
    }

    TRACE("mpf_dbg", tout << "SQRT = " << to_string(o) << std::endl;);
}

void mpf_manager::round_to_integral(mpf_rounding_mode rm, mpf const & x, mpf & o) {
    SASSERT(x.ebits > 0 && x.sbits > 0);

    TRACE("mpf_dbg", tout << "X = " << to_string(x) << std::endl;);

    if (is_nan(x))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_inf(x))
        set(o, x);
    else if (is_zero(x))
        mk_zero(x.ebits, x.sbits, x.sign, o); // -0.0 -> -0.0, says IEEE754, Sec 5.9.
    else if (x.exponent < 0) {
        if (rm == MPF_ROUND_TOWARD_ZERO)
            mk_zero(x.ebits, x.sbits, x.sign, o);
        else if (rm == MPF_ROUND_TOWARD_NEGATIVE) {
            if (x.sign)
                mk_one(x.ebits, x.sbits, true, o);
            else
                mk_zero(x.ebits, x.sbits, false, o);
        }
        else if (rm == MPF_ROUND_TOWARD_POSITIVE) {
            if (x.sign)
                mk_zero(x.ebits, x.sbits, true, o);
            else
                mk_one(x.ebits, x.sbits, false, o);
        }
        else {
            SASSERT(rm == MPF_ROUND_NEAREST_TEVEN || rm == MPF_ROUND_NEAREST_TAWAY);
            bool tie = m_mpz_manager.is_zero(x.significand) && x.exponent == -1;
            TRACE("mpf_dbg", tout << "tie = " << tie << std::endl;);
            if (tie && rm == MPF_ROUND_NEAREST_TEVEN)
                mk_zero(x.ebits, x.sbits, x.sign, o);
            else if (tie && rm == MPF_ROUND_NEAREST_TAWAY)
                mk_one(x.ebits, x.sbits, x.sign, o);
            else if (x.exponent < -1)
                mk_zero(x.ebits, x.sbits, x.sign, o);
            else
                mk_one(x.ebits, x.sbits, x.sign, o);
        }
    }
    else if (x.exponent >= x.sbits - 1)
        set(o, x);
    else {
        SASSERT(x.exponent >= 0 && x.exponent < x.sbits-1);

        o.ebits = x.ebits;
        o.sbits = x.sbits;
        o.sign = x.sign;

        scoped_mpf a(*this);
        set(a, x);
        unpack(a, true); // A includes hidden bit

        TRACE("mpf_dbg", tout << "A = " << to_string_raw(a) << std::endl;);

        SASSERT(m_mpz_manager.lt(a.significand(), m_powers2(x.sbits)));
        SASSERT(m_mpz_manager.ge(a.significand(), m_powers2(x.sbits - 1)));

        o.exponent = a.exponent();
        m_mpz_manager.set(o.significand, a.significand());

        unsigned shift = (o.sbits - 1) - ((unsigned)o.exponent);
        const mpz & shift_p = m_powers2(shift);
        const mpz & shiftm1_p = m_powers2(shift-1);
        TRACE("mpf_dbg", tout << "shift=" << shift << std::endl;);
        TRACE("mpf_dbg", tout << "shiftm1_p=" << m_mpz_manager.to_string(shiftm1_p) << std::endl;);

        scoped_mpz div(m_mpz_manager), rem(m_mpz_manager);
        m_mpz_manager.machine_div_rem(o.significand, shift_p, div, rem);
        TRACE("mpf_dbg", tout << "div=" << m_mpz_manager.to_string(div) << " rem=" << m_mpz_manager.to_string(rem) << std::endl;);

        switch (rm) {
        case MPF_ROUND_NEAREST_TEVEN:
        case MPF_ROUND_NEAREST_TAWAY: {
            bool tie = m_mpz_manager.eq(rem, shiftm1_p);
            bool less_than_tie = m_mpz_manager.lt(rem, shiftm1_p);
            bool more_than_tie = m_mpz_manager.gt(rem, shiftm1_p);
            (void)less_than_tie;
            TRACE("mpf_dbg", tout << "tie= " << tie << "; <tie = " << less_than_tie << "; >tie = " << more_than_tie << std::endl;);
            if (tie) {
                if ((rm == MPF_ROUND_NEAREST_TEVEN && m_mpz_manager.is_odd(div)) ||
                    (rm == MPF_ROUND_NEAREST_TAWAY)) {
                    TRACE("mpf_dbg", tout << "div++ (1)" << std::endl;);
                    m_mpz_manager.inc(div);
                }
            }
            else {
                SASSERT(less_than_tie || more_than_tie);
                if (more_than_tie) {
                    m_mpz_manager.inc(div);
                    TRACE("mpf_dbg", tout << "div++ (2)" << std::endl;);
                }
            }
            break;
        }
        case MPF_ROUND_TOWARD_POSITIVE:
            if (!m_mpz_manager.is_zero(rem) && !o.sign)
                m_mpz_manager.inc(div);
            break;
        case MPF_ROUND_TOWARD_NEGATIVE:
            if (!m_mpz_manager.is_zero(rem) && o.sign)
                m_mpz_manager.inc(div);
            break;
        case MPF_ROUND_TOWARD_ZERO:
        default:
            /* nothing */;
        }

        m_mpz_manager.mul2k(div, shift, o.significand);
        SASSERT(m_mpz_manager.ge(o.significand, m_powers2(o.sbits - 1)));

        // re-normalize
        while (m_mpz_manager.ge(o.significand, m_powers2(o.sbits))) {
            m_mpz_manager.machine_div2k(o.significand, 1);
            o.exponent++;
        }

        m_mpz_manager.sub(o.significand, m_powers2(o.sbits - 1), o.significand); // strip hidden bit
    }

    TRACE("mpf_dbg", tout << "INTEGRAL = " << to_string(o) << std::endl;);
}

void mpf_manager::to_mpz(mpf const & x, unsynch_mpz_manager & zm, mpz & o) {
    // x is assumed to be unpacked.
    SASSERT(x.exponent < INT_MAX);

    zm.set(o, x.significand);
    if (x.sign) zm.neg(o);
    int e = (int)x.exponent - x.sbits + 1;
    if (e < 0)
        zm.machine_div2k(o, -e);
    else
        zm.mul2k(o, e);
}

void mpf_manager::to_sbv_mpq(mpf_rounding_mode rm, const mpf & x, scoped_mpq & o) {
    SASSERT(!is_nan(x) && !is_inf(x));

    scoped_mpf t(*this);
    scoped_mpz z(m_mpz_manager);

    set(t, x);
    unpack(t, true);

    SASSERT(t.exponent() < INT_MAX);

    m_mpz_manager.set(z, t.significand());
    mpf_exp_t e = (mpf_exp_t)t.exponent() - t.sbits() + 1;
    if (e < 0) {
        bool last = m_mpz_manager.is_odd(z), round = false, sticky = false;
        for (; e != 0; e++) {
            m_mpz_manager.machine_div2k(z, 1);
            sticky |= round;
            round = last;
            last = m_mpz_manager.is_odd(z);
        }
        bool inc = false;
        switch (rm) {
        case MPF_ROUND_NEAREST_TEVEN: inc = round && (last || sticky); break;
        case MPF_ROUND_NEAREST_TAWAY: inc = round; break;
        case MPF_ROUND_TOWARD_POSITIVE: inc = (!x.sign && (round || sticky)); break;
        case MPF_ROUND_TOWARD_NEGATIVE: inc = (x.sign && (round || sticky)); break;
        case MPF_ROUND_TOWARD_ZERO: inc = false; break;
        default: UNREACHABLE();
        }
        if (inc) m_mpz_manager.inc(z);
        TRACE("mpf_dbg_sbv",
              tout << "SBV: (" << to_string(x) << ") == " << m_mpq_manager.to_string(z) << std::endl;
              tout << "sign=" << t.sign() << " last=" << last << " round=" << round <<
                  " sticky=" << sticky << " inc=" << inc << std::endl; );
    }
    else
        m_mpz_manager.mul2k(z, (unsigned) e);

    m_mpq_manager.set(o, z);
    if (x.sign) m_mpq_manager.neg(o);

    TRACE("mpf_dbg", tout << "SBV = " << m_mpq_manager.to_string(o) << std::endl;);
}

void mpf_manager::to_ieee_bv_mpz(const mpf & x, scoped_mpz & o) {
    SASSERT(!is_nan(x));
    SASSERT(exp(x) < INT_MAX);

    unsigned sbits = x.get_sbits();
    unsigned ebits = x.get_ebits();

    if (is_inf(x)) {
        m_mpz_manager.set(o, sgn(x));
        m_mpz_manager.mul2k(o, ebits);
        const mpz & exp = m_powers2.m1(ebits);
        m_mpz_manager.add(o, exp, o);
        m_mpz_manager.mul2k(o, sbits - 1);
    }
    else {
        scoped_mpz biased_exp(m_mpz_manager);
        m_mpz_manager.set(biased_exp, bias_exp(ebits, exp(x)));
        m_mpz_manager.set(o, sgn(x));
        m_mpz_manager.mul2k(o, ebits);
        m_mpz_manager.add(o, biased_exp, o);
        m_mpz_manager.mul2k(o, sbits - 1);
        m_mpz_manager.add(o, sig(x), o);
    }

    TRACE("mpf_dbg", tout << "IEEE_BV = " << m_mpz_manager.to_string(o) << std::endl;);
}

void mpf_manager::renormalize(unsigned ebits, unsigned sbits, mpf_exp_t & exp, mpz & sig) {
    if (m_mpz_manager.is_zero(sig))
        return;

    const mpz & pg = m_powers2(sbits);
    while (m_mpz_manager.ge(sig, pg)) {
        m_mpz_manager.machine_div2k(sig, 1);
        exp++;
    }

    const mpz & pl = m_powers2(sbits-1);
    while (m_mpz_manager.lt(sig, pl)) {
        m_mpz_manager.mul2k(sig, 1);
        exp--;
    }
}

void mpf_manager::partial_remainder(mpf & x, mpf const & y, mpf_exp_t const & exp_diff, bool partial) {
    unsigned ebits = x.ebits;
    unsigned sbits = x.sbits;

    SASSERT(-1 <= exp_diff && exp_diff < INT64_MAX);
    SASSERT(exp_diff < ebits+sbits || partial);

    signed int D = (signed int)(exp_diff);
    mpf_exp_t N = sbits-1;

    TRACE("mpf_dbg_rem", tout << "x=" << to_string(x) << std::endl;
                         tout << "y=" << to_string(y) << std::endl;
                         tout << "d=" << D << std::endl;
                         tout << "partial=" << partial << std::endl;);

    SASSERT(m_mpz_manager.lt(x.significand, m_powers2(sbits)));
    SASSERT(m_mpz_manager.ge(x.significand, m_powers2(sbits - 1)));
    SASSERT(m_mpz_manager.lt(y.significand, m_powers2(sbits)));
    SASSERT(m_mpz_manager.ge(y.significand, m_powers2(sbits - 1)));

    // 1. Compute a/b
    bool x_div_y_sgn = x.sign != y.sign;
    mpf_exp_t x_div_y_exp = D;
    scoped_mpz x_sig_shifted(m_mpz_manager), x_div_y_sig_lrg(m_mpz_manager), x_div_y_rem(m_mpz_manager);
    scoped_mpz x_rem_y_sig(m_mpz_manager);
    m_mpz_manager.mul2k(x.significand, 2*sbits + 2, x_sig_shifted);
    m_mpz_manager.machine_div_rem(x_sig_shifted, y.significand, x_div_y_sig_lrg, x_div_y_rem); // rem useful?
    // x/y is in x_diuv_y_sig_lrg and has sbits+3 extra bits.

    TRACE("mpf_dbg_rem", tout << "X/Y_exp=" << x_div_y_exp << std::endl;
                         tout << "X/Y_sig_lrg=" << m_mpz_manager.to_string(x_div_y_sig_lrg) << std::endl;
                         tout << "X/Y_rem=" << m_mpz_manager.to_string(x_div_y_rem) << std::endl;
                         tout << "X/Y~=" << to_string_hexfloat(x_div_y_sgn, x_div_y_exp, x_div_y_sig_lrg, ebits, sbits, sbits+3) << std::endl;);

    // 2. Round a/b to integer Q/QQ
    bool Q_sgn = x_div_y_sgn;
    mpf_exp_t Q_exp = x_div_y_exp;
    scoped_mpz Q_sig(m_mpz_manager), Q_rem(m_mpz_manager);
    unsigned Q_shft = (sbits-1) + (sbits+3) -  (unsigned) (partial ? N :Q_exp);
    if (partial) {
        // Round according to MPF_ROUND_TOWARD_ZERO
        SASSERT(0 < N && N < Q_exp && Q_exp < INT_MAX);
        m_mpz_manager.machine_div2k(x_div_y_sig_lrg, Q_shft, Q_sig);
    }
    else {
        // Round according to MPF_ROUND_NEAREST_TEVEN
        m_mpz_manager.machine_div_rem(x_div_y_sig_lrg, m_powers2(Q_shft), Q_sig, Q_rem);
        const mpz & shiftm1_p = m_powers2(Q_shft-1);
        bool tie = m_mpz_manager.eq(Q_rem, shiftm1_p);
        bool more_than_tie = m_mpz_manager.gt(Q_rem, shiftm1_p);
        TRACE("mpf_dbg_rem", tout << "tie= " << tie << "; >tie= " << more_than_tie << std::endl;);
        if ((tie && m_mpz_manager.is_odd(Q_sig)) || more_than_tie)
            m_mpz_manager.inc(Q_sig);
    }
    m_mpz_manager.mul2k(Q_sig, Q_shft);
    m_mpz_manager.machine_div2k(Q_sig, sbits+3);
    renormalize(ebits, sbits, Q_exp, Q_sig);

    (void)Q_sgn;
    TRACE("mpf_dbg_rem", tout << "Q_exp=" << Q_exp << std::endl;
                         tout << "Q_sig=" << m_mpz_manager.to_string(Q_sig) << std::endl;
                         tout << "Q=" << to_string_hexfloat(Q_sgn, Q_exp, Q_sig, ebits, sbits, 0) << std::endl;);

    if ((D == -1 || partial) && m_mpz_manager.is_zero(Q_sig))
        return; // This means x % y = x.

    // no extra bits in Q_sig.
    SASSERT(!m_mpz_manager.is_zero(Q_sig));
    SASSERT(m_mpz_manager.lt(Q_sig, m_powers2(sbits)));
    SASSERT(m_mpz_manager.ge(Q_sig, m_powers2(sbits - 1)));


    // 3. Compute Y*Q / Y*QQ*2^{D-N}
    bool YQ_sgn = x.sign;
    scoped_mpz YQ_sig(m_mpz_manager);
    mpf_exp_t YQ_exp = Q_exp + y.exponent;
    m_mpz_manager.mul(y.significand, Q_sig, YQ_sig);
    renormalize(ebits, 2*sbits-1, YQ_exp, YQ_sig); // YQ_sig has `sbits-1' extra bits.

    (void)YQ_sgn;
    TRACE("mpf_dbg_rem", tout << "YQ_sgn=" << YQ_sgn << std::endl;
                         tout << "YQ_exp=" << YQ_exp << std::endl;
                         tout << "YQ_sig=" << m_mpz_manager.to_string(YQ_sig) << std::endl;
                         tout << "YQ=" << to_string_hexfloat(YQ_sgn, YQ_exp, YQ_sig, ebits, sbits, sbits-1) << std::endl;);

    // `sbits-1' extra bits in YQ_sig.
    SASSERT(m_mpz_manager.lt(YQ_sig, m_powers2(2*sbits-1)));
    SASSERT(m_mpz_manager.ge(YQ_sig, m_powers2(2*sbits-2)) || YQ_exp <= mk_bot_exp(ebits));

    // 4. Compute X-Y*Q
    mpf_exp_t X_YQ_exp = x.exponent;
    scoped_mpz X_YQ_sig(m_mpz_manager);
    mpf_exp_t exp_delta = exp(x) - YQ_exp;
    TRACE("mpf_dbg_rem", tout << "exp_delta=" << exp_delta << std::endl;);
    SASSERT(INT_MIN < exp_delta && exp_delta <= INT_MAX);
    scoped_mpz minuend(m_mpz_manager), subtrahend(m_mpz_manager);

    scoped_mpz x_sig_lrg(m_mpz_manager);
    m_mpz_manager.mul2k(x.significand, sbits-1, x_sig_lrg); // sbits-1 extra bits into x

    m_mpz_manager.set(minuend, x_sig_lrg);
    m_mpz_manager.set(subtrahend, YQ_sig);

    SASSERT(m_mpz_manager.lt(minuend, m_powers2(2*sbits-1)));
    SASSERT(m_mpz_manager.ge(minuend, m_powers2(2*sbits-2)));
    SASSERT(m_mpz_manager.lt(subtrahend, m_powers2(2*sbits-1)));
    SASSERT(m_mpz_manager.ge(subtrahend, m_powers2(2*sbits-2)));

    if (exp_delta != 0) {
        scoped_mpz sticky_rem(m_mpz_manager);
        m_mpz_manager.set(sticky_rem, 0);
        if (exp_delta > sbits+5)
            sticky_rem.swap(subtrahend);
        else if (exp_delta > 0)
            m_mpz_manager.machine_div_rem(subtrahend, m_powers2((unsigned)exp_delta), subtrahend, sticky_rem);
        else {
            SASSERT(exp_delta < 0);
            exp_delta = -exp_delta;
            m_mpz_manager.mul2k(subtrahend, (int)exp_delta);
        }
        if (!m_mpz_manager.is_zero(sticky_rem) && m_mpz_manager.is_even(subtrahend))
            m_mpz_manager.inc(subtrahend);
        TRACE("mpf_dbg_rem", tout << "aligned subtrahend=" << m_mpz_manager.to_string(subtrahend) << std::endl;);
    }

    m_mpz_manager.sub(minuend, subtrahend, X_YQ_sig);
    TRACE("mpf_dbg_rem", tout << "X_YQ_sig'=" << m_mpz_manager.to_string(X_YQ_sig) << std::endl;);

    bool neg = m_mpz_manager.is_neg(X_YQ_sig);
    if (neg) m_mpz_manager.neg(X_YQ_sig);
    bool X_YQ_sgn = x.sign ^ neg;

    // 5. Rounding
    if (m_mpz_manager.is_zero(X_YQ_sig))
        mk_zero(ebits, sbits, x.sign, x);
    else {
        renormalize(ebits, 2*sbits-1, X_YQ_exp, X_YQ_sig);

        TRACE("mpf_dbg_rem", tout << "minuend=" << m_mpz_manager.to_string(minuend) << std::endl;
                             tout << "subtrahend=" << m_mpz_manager.to_string(subtrahend) << std::endl;
                             tout << "X_YQ_sgn=" << X_YQ_sgn << std::endl;
                             tout << "X_YQ_exp=" << X_YQ_exp << std::endl;
                             tout << "X_YQ_sig=" << m_mpz_manager.to_string(X_YQ_sig) << std::endl;
                             tout << "X-YQ=" << to_string_hexfloat(X_YQ_sgn, X_YQ_exp, X_YQ_sig, ebits, sbits, sbits-1) << std::endl;);

        // `sbits-1' extra bits in X_YQ_sig
        SASSERT(m_mpz_manager.lt(X_YQ_sig, m_powers2(2*sbits-1)));
        scoped_mpz rnd_bits(m_mpz_manager);
        m_mpz_manager.machine_div_rem(X_YQ_sig, m_powers2(sbits-1), X_YQ_sig, rnd_bits);
        TRACE("mpf_dbg_rem", tout << "final sticky=" << m_mpz_manager.to_string(rnd_bits) << std::endl; );

        // Round to nearest, ties to even.
        if (m_mpz_manager.eq(rnd_bits, mpz(32))) { // tie.
            if (m_mpz_manager.is_odd(X_YQ_sig)) {
                m_mpz_manager.inc(X_YQ_sig);
            }
        }
        else if (m_mpz_manager.gt(rnd_bits, mpz(32)))
            m_mpz_manager.inc(X_YQ_sig);

        set(x, ebits, sbits, X_YQ_sgn, X_YQ_exp, X_YQ_sig);
    }

    TRACE("mpf_dbg_rem", tout << "partial remainder = " << to_string_hexfloat(x) << std::endl;);
}

void mpf_manager::rem(mpf const & x, mpf const & y, mpf & o) {
    SASSERT(x.sbits == y.sbits && x.ebits == y.ebits);

    TRACE("mpf_dbg_rem", tout << "X = " << to_string(x) << "=" << to_string_hexfloat(x) << std::endl;
                         tout << "Y = " << to_string(y) << "=" << to_string_hexfloat(y) << std::endl;);

    if (is_nan(x) || is_nan(y))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_inf(x))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_inf(y))
        set(o, x);
    else if (is_zero(y))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_zero(x))
        set(o, x);
    else {
        SASSERT(is_regular(x) && is_regular(y));

        // This is a generalized version of the algorithm for FPREM1 in the `Intel
        // 64 and IA-32 Architectures Software Developer's Manual',
        // Section 3-402 Vol. 2A `FPREM1-Partial Remainder'.
        scoped_mpf ST0(*this), ST1(*this);
        set(ST0, x);
        set(ST1, y);
        unpack(ST0, true);
        unpack(ST1, true);

        const mpf_exp_t B = x.sbits;
        mpf_exp_t D;
        do {
            if (ST0.exponent() < ST1.exponent() - 1) {
                D = 0;
            }
            else {
                D = ST0.exponent() - ST1.exponent();
                partial_remainder(ST0.get(), ST1.get(), D, (D >= B));
            }
        } while (D >= B && !ST0.is_zero());

        m_mpz_manager.mul2k(ST0.significand(), 3);
        set(o, x.ebits, x.sbits, MPF_ROUND_TOWARD_ZERO, ST0);
        round(MPF_ROUND_NEAREST_TEVEN, o);
    }

    TRACE("mpf_dbg_rem", tout << "R = " << to_string(o) << "=" << to_string_hexfloat(o) << std::endl; );
    TRACE("mpf_dbg", tout << "REMAINDER = " << to_string(o) << std::endl;);
}

void mpf_manager::maximum(mpf const & x, mpf const & y, mpf & o) {
    if (is_nan(x))
        set(o, y);
    else if (is_nan(y))
        set(o, x);
    else if (is_zero(x) && is_zero(y) && sgn(x) != sgn(y)) {
        UNREACHABLE(); // max(+0, -0) and max(-0, +0) are unspecified.
    }
    else if (is_zero(x) && is_zero(y))
        set(o, y);
    else if (gt(x, y))
        set(o, x);
    else
        set(o, y);
}

void mpf_manager::minimum(mpf const & x, mpf const & y, mpf & o) {
    if (is_nan(x))
        set(o, y);
    else if (is_nan(y))
        set(o, x);
    else if (is_zero(x) && is_zero(y) && sgn(x) != sgn(y)) {
        UNREACHABLE(); // min(+0, -0) and min(-0, +0) are unspecified.
    }
    else if (is_zero(x) && is_zero(y))
        set(o, y);
    else if (lt(x, y))
        set(o, x);
    else
        set(o, y);
}

std::string mpf_manager::to_string(mpf const & x) {
    std::string res;

    if (is_nan(x))
        res = "NaN";
    else {
        if (is_inf(x))
            res = sgn(x) ? "-oo" : "+oo";
        else if (is_zero(x))
            res = sgn(x) ? "-zero" : "+zero";
        else {
            res = sgn(x) ? "-" : "";
            scoped_mpz num(m_mpq_manager), denom(m_mpq_manager);
            num   = 0;
            denom = 1;
            mpf_exp_t exponent;

            if (is_denormal(x))
                exponent = mk_min_exp(x.ebits);
            else {
                m_mpz_manager.set(num, 1);
                m_mpz_manager.mul2k(num, x.sbits-1, num);
                exponent = exp(x);
            }

            m_mpz_manager.add(num, sig(x), num);
            m_mpz_manager.mul2k(denom, x.sbits-1, denom);

            //TRACE("mpf_dbg", tout << "SIG=" << m_mpq_manager.to_string(sig(x)) << std::endl; );
            //TRACE("mpf_dbg", tout << "NUM=" << m_mpq_manager.to_string(num) << std::endl;);
            //TRACE("mpf_dbg", tout << "DEN=" << m_mpq_manager.to_string(denom) << std::endl;);
            //TRACE("mpf_dbg", tout << "EXP=" << exponent << std::endl;);

            scoped_mpq r(m_mpq_manager);
            m_mpq_manager.set(r, num);
            m_mpq_manager.div(r, denom, r);

            std::stringstream ss;
            m_mpq_manager.display_decimal(ss, r, x.sbits);
            if (m_mpq_manager.is_int(r))
                ss << ".0";
            ss << " " << exponent;
            res += ss.str();
        }
    }

    //DEBUG_CODE(
    //   res += " " + to_string_raw(x);
    //);

    return res;
}

std::string mpf_manager::to_rational_string(mpf const & x)  {
    scoped_mpq q(m_mpq_manager);
    to_rational(x, q);
    return m_mpq_manager.to_string(q);
}

void mpf_manager::display_decimal(std::ostream & out, mpf const & a, unsigned k) {
    scoped_mpq q(m_mpq_manager);
    to_rational(a, q);
    m_mpq_manager.display_decimal(out, q, k);
}

void mpf_manager::display_smt2(std::ostream & out, mpf const & a, bool decimal) {
    scoped_mpq q(m_mpq_manager);
    to_rational(a, q);
    m_mpq_manager.display_smt2(out, q, decimal);
}

std::string mpf_manager::to_string_raw(mpf const & x) {
    std::string res;
    res += "[";
    res += (x.sign?"-":"+");
    res += " ";
    res += m_mpz_manager.to_string(sig(x));
    res += " ";
    std::stringstream ss("");
    ss << exp(x);
    res += ss.str();
    if (is_normal(x))
        res += " N";
    else
        res += " D";
    res += "]";
    return res;
}

std::string mpf_manager::to_string_hexfloat(bool sgn, mpf_exp_t exp, scoped_mpz const & sig, unsigned ebits, unsigned sbits, unsigned rbits) {
    scoped_mpf q(*this);
    scoped_mpz q_sig(m_mpz_manager);
    m_mpz_manager.set(q_sig, sig);
    if (rbits != 0) m_mpz_manager.div(q_sig, m_powers2(rbits), q_sig); // restore scale
    if (m_mpz_manager.ge(q_sig, m_powers2(sbits-1)))
        m_mpz_manager.sub(q_sig, m_powers2(sbits-1), q_sig); // strip hidden bit
    else if (exp == mk_min_exp(ebits))
        exp = mk_bot_exp(ebits);
    set(q, ebits, sbits, sgn, exp, q_sig);
    return to_string(q.get());
}

std::string mpf_manager::to_string_hexfloat(mpf const & x) {
    std::stringstream ss("");
    std::ios::fmtflags ff = ss.setf(std::ios_base::hex | std::ios_base::uppercase |
                                    std::ios_base::showpoint | std::ios_base::showpos);
    ss.setf(ff);
    ss.precision(13);
#if defined(_WIN32) && _MSC_VER >= 1800
    ss << std::hexfloat << to_double(x);
#else
    ss << std::hex << (*reinterpret_cast<const unsigned long long *>(&(x)));
#endif
    return ss.str();
}

std::string mpf_manager::to_string_binary(mpf const & x, unsigned upper_extra, unsigned lower_extra) {
    std::string res;

    if (is_nan(x))
        res = std::string("") + "#b0 " +
              "#b" + std::string(x.ebits, '1') + " " +
              "#b" + std::string(x.sbits-2, '0') + "1 " +
              "(NaN)";
    else if (is_inf(x))
        res = std::string("") + "#b" + (sgn(x)?"1":"0") +  " " +
              "#b" + std::string(x.ebits, '1') + " " +
              "#b" + std::string(x.sbits - 1, '0') + "1 " +
              "(" + (sgn(x)?"-":"+") + "oo)";
    else if (is_zero(x))
        res = std::string("") + "#b" + (sgn(x) ? "1" : "0") + " " +
              "#b" + std::string(x.ebits, '0') + " " +
              "#b" + std::string(x.sbits - 1, '0') + " " +
              "(" + (sgn(x) ? "-" : "+") + "zero)";
    else {
        SASSERT(m_mpz_manager.is_nonneg(sig(x)));

        res = std::string("") + "#b" + (sgn(x) ? "1" : "0") + " ";

        scoped_mpz tmp(m_mpz_manager);

        if (is_denormal(x))
            m_mpz_manager.set(tmp, bias_exp(x.ebits, mk_min_exp(x.ebits)));
        else {
            m_mpz_manager.set(tmp, bias_exp(x.ebits, exp(x)));
        }

        std::string tmp_str = "";
        for (unsigned i = 0; i < x.ebits; i++) {
            tmp_str += m_mpz_manager.is_odd(tmp) ? "1" : "0";
            tmp /= 2;
        }
        std::reverse(tmp_str.begin(), tmp_str.end());
        res += "#b" + tmp_str + " ";

        tmp_str = "";
        m_mpz_manager.set(tmp, sig(x));
        unsigned num_bits = upper_extra + x.sbits + lower_extra;
        for (unsigned i = 0; i < num_bits || !tmp.is_zero(); i++) {
            tmp_str += m_mpz_manager.is_odd(tmp) ? "1" : "0";
            tmp /= 2;
            if (i == lower_extra - 1)
                tmp_str += ",";
            if (i == x.sbits + lower_extra - 2) {
                tmp_str += ".";
                if (i == num_bits - 1)
                    tmp_str += " ";
            }
        }
        std::reverse(tmp_str.begin(), tmp_str.end());
        res += "#b" + tmp_str;
    }

    return res;
}

void mpf_manager::to_rational(mpf const & x, unsynch_mpq_manager & qm, mpq & o) {
    scoped_mpf a(*this);
    scoped_mpz n(m_mpq_manager), d(m_mpq_manager);
    set(a, x);
    unpack(a, true);

    m_mpz_manager.set(n, a.significand());
    if (a.sign()) m_mpz_manager.neg(n);
    m_mpz_manager.power(2, a.sbits() - 1, d);
    if (a.exponent() >= 0)
        m_mpz_manager.mul2k(n, (unsigned)a.exponent());
    else
        m_mpz_manager.mul2k(d, (unsigned)-a.exponent());

    qm.set(o, n, d);
}

double mpf_manager::to_double(mpf const & x) {
    SASSERT(x.ebits <= 11 && x.sbits <= 53);
    uint64_t raw = 0;
    int64_t sig = 0, exp = 0;

    sig = m_mpz_manager.get_uint64(x.significand);
    sig <<= 53 - x.sbits;

    if (has_top_exp(x))
        exp = 1024;
    else if (has_bot_exp(x))
        exp = -1023;
    else
        exp = x.exponent;

    exp += 1023;

    raw = (exp << 52) | sig;

    if (x.sign)
        raw = raw | 0x8000000000000000ull;

    double ret;
    memcpy(&ret, &raw, sizeof(double));
    return ret;
}

float mpf_manager::to_float(mpf const & x) {
    SASSERT(x.ebits <= 8 && x.sbits <= 24);
    unsigned int raw = 0;
    unsigned int sig = 0, exp = 0;

    uint64_t q = m_mpz_manager.get_uint64(x.significand);
    SASSERT(q < 4294967296ull);
    sig = q & 0x00000000FFFFFFFF;
    sig <<= 24 - x.sbits;

    if (has_top_exp(x))
        exp = +128;
    else if (has_bot_exp(x))
        exp = -127;
    else {
        int64_t q = x.exponent;
        SASSERT(q < 4294967296ll);
        exp = q & 0x00000000FFFFFFFF;
    }

    exp += 127;

    raw = (exp << 23) | sig;

    if (x.sign)
        raw = raw | 0x80000000;

    float ret;
    memcpy(&ret, &raw, sizeof(float));
    return ret;
}

bool mpf_manager::is_nan(mpf const & x) {
    return has_top_exp(x) && !m_mpz_manager.is_zero(sig(x));
}

bool mpf_manager::is_inf(mpf const & x) {
    return has_top_exp(x) && m_mpz_manager.is_zero(sig(x));
}

bool mpf_manager::is_pinf(mpf const & x) {
    return !x.sign && is_inf(x);
}

bool mpf_manager::is_ninf(mpf const & x) {
    return x.sign && is_inf(x);
}

bool mpf_manager::is_normal(mpf const & x) {
    return !(has_top_exp(x) || is_denormal(x) || is_zero(x));
}

bool mpf_manager::is_denormal(mpf const & x) {
    return !is_zero(x) && has_bot_exp(x);
}

bool mpf_manager::is_int(mpf const & x) {
    if (!is_normal(x))
        return false;

    if (exp(x) >= x.sbits-1)
        return true;
    else if (exp(x) < 0)
        return false;
    else
    {
        SASSERT(x.exponent >= 0 && x.exponent < x.sbits-1);

        scoped_mpz t(m_mpz_manager);
        m_mpz_manager.set(t, sig(x));
        unsigned shift = x.sbits - ((unsigned)exp(x)) - 1;
        do {
            if (m_mpz_manager.is_odd(t))
                return false;
            m_mpz_manager.machine_div2k(t, 1);
        }
        while (--shift != 0);

        return true;
    }
}

bool mpf_manager::has_bot_exp(mpf const & x) {
    return exp(x) == mk_bot_exp(x.ebits);
}

bool mpf_manager::has_top_exp(mpf const & x) {
    return exp(x) == mk_top_exp(x.ebits);
}

mpf_exp_t mpf_manager::mk_bot_exp(unsigned ebits) {
    SASSERT(ebits >= 2);
    return m_mpz_manager.get_int64(m_powers2.m1(ebits-1, true));
}

mpf_exp_t mpf_manager::mk_top_exp(unsigned ebits) {
    SASSERT(ebits >= 2);
    return m_mpz_manager.get_int64(m_powers2(ebits-1));
}

mpf_exp_t mpf_manager::mk_min_exp(unsigned ebits) {
    SASSERT(ebits > 0);
    mpf_exp_t r = m_mpz_manager.get_int64(m_powers2.m1(ebits-1, true));
    return r+1;
}

mpf_exp_t mpf_manager::mk_max_exp(unsigned ebits) {
    SASSERT(ebits > 0);
    return m_mpz_manager.get_int64(m_powers2.m1(ebits-1, false));
}

mpf_exp_t mpf_manager::bias_exp(unsigned ebits, mpf_exp_t unbiased_exponent) {
    return unbiased_exponent + m_mpz_manager.get_int64(m_powers2.m1(ebits - 1, false));
}
mpf_exp_t mpf_manager::unbias_exp(unsigned ebits, mpf_exp_t biased_exponent) {
    return biased_exponent - m_mpz_manager.get_int64(m_powers2.m1(ebits - 1, false));
}

void mpf_manager::mk_nzero(unsigned ebits, unsigned sbits, mpf & o) {
    o.sbits = sbits;
    o.ebits = ebits;
    o.exponent = mk_bot_exp(ebits);
    m_mpz_manager.set(o.significand, 0);
    o.sign = true;
}

void mpf_manager::mk_pzero(unsigned ebits, unsigned sbits, mpf & o) {
    o.sbits = sbits;
    o.ebits = ebits;
    o.exponent = mk_bot_exp(ebits);
    m_mpz_manager.set(o.significand, 0);
    o.sign = false;
}

void mpf_manager::mk_zero(unsigned ebits, unsigned sbits, bool sign, mpf & o) {
    if (sign)
        mk_nzero(ebits, sbits, o);
    else
        mk_pzero(ebits, sbits, o);
}

void mpf_manager::mk_nan(unsigned ebits, unsigned sbits, mpf & o) {
    o.sbits = sbits;
    o.ebits = ebits;
    o.exponent = mk_top_exp(ebits);
    // This is a quiet NaN, i.e., the first bit should be 1.
    m_mpz_manager.set(o.significand, m_powers2(sbits-1));
    m_mpz_manager.dec(o.significand);
    o.sign = false;
}

void mpf_manager::mk_one(unsigned ebits, unsigned sbits, bool sign, mpf & o) const {
    o.sbits = sbits;
    o.ebits = ebits;
    o.sign = sign;
    m_mpz_manager.set(o.significand, 0);
    o.exponent = 0;
}

void mpf_manager::mk_max_value(unsigned ebits, unsigned sbits, bool sign, mpf & o) {
    o.sbits = sbits;
    o.ebits = ebits;
    o.sign = sign;
    o.exponent = mk_top_exp(ebits) - 1;
    m_mpz_manager.set(o.significand, m_powers2.m1(sbits-1, false));
}

void mpf_manager::mk_inf(unsigned ebits, unsigned sbits, bool sign, mpf & o) {
    o.sbits = sbits;
    o.ebits = ebits;
    o.sign = sign;
    o.exponent = mk_top_exp(ebits);
    m_mpz_manager.set(o.significand, 0);
}

void mpf_manager::mk_pinf(unsigned ebits, unsigned sbits, mpf & o) {
    mk_inf(ebits, sbits, false, o);
}

void mpf_manager::mk_ninf(unsigned ebits, unsigned sbits, mpf & o) {
    mk_inf(ebits, sbits, true, o);
}

void mpf_manager::unpack(mpf & o, bool normalize) {
    TRACE("mpf_dbg", tout << "unpack " << to_string(o) << ": ebits=" <<
                             o.ebits << " sbits=" << o.sbits <<
                             " normalize=" << normalize <<
                             " has_top_exp=" << has_top_exp(o) << " (" << mk_top_exp(o.ebits) << ")" <<
                             " has_bot_exp=" << has_bot_exp(o) << " (" << mk_bot_exp(o.ebits) << ")" <<
                             " is_zero=" << is_zero(o) << std::endl;);

    // Insert the hidden bit or adjust the exponent of denormal numbers.
    if (is_zero(o))
        return;

    if (is_normal(o))
        m_mpz_manager.add(o.significand, m_powers2(o.sbits-1), o.significand);
    else {
        o.exponent = mk_bot_exp(o.ebits) + 1;
        if (normalize && !m_mpz_manager.is_zero(o.significand)) {
            const mpz & p = m_powers2(o.sbits-1);
            while (m_mpz_manager.gt(p, o.significand)) {
                o.exponent--;
                m_mpz_manager.mul2k(o.significand, 1, o.significand);
            }
        }
    }
}

void mpf_manager::mk_round_inf(mpf_rounding_mode rm, mpf & o) {
    if (!o.sign) {
        if (rm == MPF_ROUND_TOWARD_ZERO || rm == MPF_ROUND_TOWARD_NEGATIVE)
            mk_max_value(o.ebits, o.sbits, o.sign, o);
        else
            mk_inf(o.ebits, o.sbits, o.sign, o);
    }
    else {
        if (rm == MPF_ROUND_TOWARD_ZERO || rm == MPF_ROUND_TOWARD_POSITIVE)
            mk_max_value(o.ebits, o.sbits, o.sign, o);
        else
            mk_inf(o.ebits, o.sbits, o.sign, o);
    }
}

void mpf_manager::round(mpf_rounding_mode rm, mpf & o) {
    // Assumptions: o.significand is of the form f[-1:0] . f[1:sbits-1] [round,extra,sticky],
    // i.e., it has 2 + (sbits-1) + 3 = sbits + 4 bits.

    TRACE("mpf_dbg", tout << "RND: " << to_string(o) << std::endl;
                     tout << to_string_binary(o, 1, 3) << std::endl;);

    DEBUG_CODE({
        const mpz & p_m3 = m_powers2(o.sbits+4);
        SASSERT(m_mpz_manager.lt(o.significand, p_m3));
    });

    mpf_exp_t e_max    = mk_max_exp(o.ebits);
    mpf_exp_t e_min    = mk_min_exp(o.ebits);

    unsigned sig_width = m_mpz_manager.prev_power_of_two(o.significand) + 1;
    mpf_exp_t lz       = o.sbits + 4 - sig_width;
    mpf_exp_t beta     = o.exponent - lz + 1;

    scoped_mpz sigma(m_mpz_manager);

    if (beta < e_min) {
        // denormal significand/TINY
        m_mpz_manager.set(sigma, o.exponent - e_min);
        o.exponent = e_min;
    }
    else {
        m_mpz_manager.set(sigma, lz - 1);
        o.exponent = beta;
    }

    scoped_mpz sigma_cap(m_mpz_manager);
    sigma_cap = o.sbits + 2;
    m_mpz_manager.neg(sigma_cap);
    if (m_mpz_manager.lt(sigma, sigma_cap))
        m_mpz_manager.set(sigma, sigma_cap);

    TRACE("mpf_dbg", tout << "e_min_norm = " << e_min << std::endl;
                     tout << "e_max_norm = " << e_max << std::endl;
                     tout << "beta = " << beta << ", (beta < e_min) = " << (beta < e_min) << std::endl;
                     tout << "LZ = " << lz << std::endl;
                     tout << "sigma = " << m_mpz_manager.to_string(sigma) << std::endl;
                     tout << "sigma_cap = " << m_mpz_manager.to_string(sigma_cap) << std::endl;);

    // Normalization shift

    TRACE("mpf_dbg", tout << "Shift distance: " << m_mpz_manager.to_string(sigma) << " " << ((m_mpz_manager.is_nonneg(sigma))?"(LEFT)":"(RIGHT)") << std::endl;);

    if (m_mpz_manager.le(sigma, -1)) {
        // Right shift
        scoped_mpz sticky_rem(m_mpz_manager);
        unsigned nsigma_uint = (unsigned)-m_mpz_manager.get_int64(sigma); // sigma is capped, this is safe.
        m_mpz_manager.machine_div_rem(o.significand, m_powers2(nsigma_uint), o.significand, sticky_rem);
        bool sticky = !m_mpz_manager.is_zero(sticky_rem);
        if (sticky && m_mpz_manager.is_even(o.significand))
            m_mpz_manager.inc(o.significand);
    }
    else {
        // Left shift
        unsigned sigma_uint = static_cast<unsigned>(m_mpz_manager.get_int64(sigma));
        m_mpz_manager.mul2k(o.significand, sigma_uint, o.significand);
    }

    TRACE("mpf_dbg", tout << "Shifted: " << to_string(o) << std::endl;
                     tout << to_string_binary(o, 1, 3) << std::endl;);

    // Significand rounding (sigrd)

    bool sticky = !m_mpz_manager.is_even(o.significand);
    m_mpz_manager.machine_div2k(o.significand, 1);
    sticky = sticky || !m_mpz_manager.is_even(o.significand);
    m_mpz_manager.machine_div2k(o.significand, 1);
    bool round = !m_mpz_manager.is_even(o.significand);
    m_mpz_manager.machine_div2k(o.significand, 1);

    bool last = !m_mpz_manager.is_even(o.significand);

    TRACE("mpf_dbg", tout << "sign=" << o.sign << " last=" << last << " round=" << round << " sticky=" << sticky << std::endl;);
    TRACE("mpf_dbg", tout << "before rounding decision: " << to_string(o) << std::endl;);

    // The significand has the right size now, but we might have to increment it
    // depending on the sign, the last/round/sticky bits, and the rounding mode.
    bool inc = false;
    switch (rm) {
    case MPF_ROUND_NEAREST_TEVEN: inc = round && (last || sticky); break;
    case MPF_ROUND_NEAREST_TAWAY: inc = round; break;
    case MPF_ROUND_TOWARD_POSITIVE: inc = (!o.sign && (round || sticky)); break;
    case MPF_ROUND_TOWARD_NEGATIVE: inc = (o.sign && (round || sticky)); break;
    case MPF_ROUND_TOWARD_ZERO: inc = false; break;
    default: UNREACHABLE();
    }

    TRACE("mpf_dbg", tout << "Rounding increment -> significand +" << (int)inc << std::endl;);
    if (inc)
        m_mpz_manager.inc(o.significand);

    TRACE("mpf_dbg", tout << "Rounded significand: " << to_string(o) << std::endl;);

    // Post normalization (post)

    const mpz & p_sig = m_powers2(o.sbits);
    if (m_mpz_manager.ge(o.significand, p_sig)) {
        m_mpz_manager.machine_div2k(o.significand, 1);
        o.exponent++;
    }

    bool SIGovf = o.exponent > e_max;
    TRACE("mpf_dbg", tout << "Post-normalized: " << to_string(o) << std::endl;);
    TRACE("mpf_dbg", tout << "SIGovf = " << SIGovf << std::endl;);

    // Exponent rounding (exprd)

    bool o_has_max_exp = (o.exponent > e_max);
    bool OVF2 = SIGovf && o_has_max_exp;

    TRACE("mpf_dbg", tout << "OVF2 = " << OVF2 << std::endl;);
    TRACE("mpf_dbg", tout << "o_has_max_exp = " << o_has_max_exp << std::endl;);

    if (OVF2)
        mk_round_inf(rm, o);
    else {
        const mpz & p = m_powers2(o.sbits-1);

        if (m_mpz_manager.ge(o.significand, p)) {
            TRACE("mpf_dbg", tout << "NORMAL: " << m_mpz_manager.to_string(o.significand) << std::endl;);
            m_mpz_manager.sub(o.significand, p, o.significand); // Strips the hidden bit.
        }
        else {
            TRACE("mpf_dbg", tout << "DENORMAL: " << m_mpz_manager.to_string(o.significand) << std::endl;);
            o.exponent = mk_bot_exp(o.ebits);
        }
    }

    TRACE("mpf_dbg", tout << "ROUNDED = " << to_string(o) << std::endl;
                     tout << to_string_binary(o, -1, 0) << " (hidden bit, unbiased exp)." << std::endl;);
}

void mpf_manager::round_sqrt(mpf_rounding_mode rm, mpf & o) {
    TRACE("mpf_dbg", tout << "RND-SQRT: " << to_string(o) << std::endl;);

    bool sticky = !m_mpz_manager.is_even(o.significand);
    m_mpz_manager.machine_div2k(o.significand, 1);
    sticky = sticky || !m_mpz_manager.is_even(o.significand);
    m_mpz_manager.machine_div2k(o.significand, 1);
    bool round = !m_mpz_manager.is_even(o.significand);
    m_mpz_manager.machine_div2k(o.significand, 1);
    bool last = !m_mpz_manager.is_even(o.significand);
    (void)last;
    bool inc = false;

    // Specialized rounding for sqrt, as there are no negative cases (or half-way cases?)
    switch(rm) {
    case MPF_ROUND_NEAREST_TEVEN:
    case MPF_ROUND_NEAREST_TAWAY: inc = (round && sticky); break;
    case MPF_ROUND_TOWARD_NEGATIVE: break;
    case MPF_ROUND_TOWARD_ZERO: break;
    case MPF_ROUND_TOWARD_POSITIVE: inc = round || sticky; break;
    default: UNREACHABLE();
    }

    TRACE("mpf_dbg", tout << "last=" << last << " round=" << round << " sticky=" << sticky << " --> inc=" << inc << std::endl;);

    if (inc)
        m_mpz_manager.inc(o.significand);

    m_mpz_manager.sub(o.significand, m_powers2(o.sbits-1), o.significand);

    TRACE("mpf_dbg", tout << "ROUNDED = " << to_string(o) << std::endl;);
}

unsigned mpf_manager::prev_power_of_two(mpf const & a) {
    SASSERT(!is_nan(a) && !is_pinf(a) && !is_ninf(a));
    if (!is_pos(a))
        return 0;
    if (a.exponent <= -static_cast<int>(a.sbits))
        return 0; // Number is smaller than 1
    return static_cast<unsigned>(a.sbits + a.exponent - 1);
}
