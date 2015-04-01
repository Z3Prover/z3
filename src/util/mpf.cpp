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
#include"mpf.h"

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

mpf::mpf(mpf const & other) {
    // It is safe if the mpz numbers are small.
    // I need it for resize method in vector.
    // UNREACHABLE();
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
    COMPILE_TIME_ASSERT(sizeof(int) == 4);

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
    COMPILE_TIME_ASSERT(sizeof(double) == 8);

    uint64 raw;
    memcpy(&raw, &value, sizeof(double));
    bool sign = (raw >> 63) != 0;
    int64 e =  ((raw & 0x7FF0000000000000ull) >> 52) - 1023;
    uint64 s = raw & 0x000FFFFFFFFFFFFFull;

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
    COMPILE_TIME_ASSERT(sizeof(float) == 4);

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
    set(o, ebits, sbits, rm, value, exp);
    TRACE("mpf_dbg", tout << "set: res = " << to_string(o) << std::endl;);
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, char const * value) {    
    TRACE("mpf_dbg", tout << "set: " << value << " [" << ebits << "/" << sbits << "]"<< std::endl;);

    o.ebits = ebits;
    o.sbits = sbits;

    // We expect [i].[f]P[e], where P means that the exponent is interpreted as 2^e instead of 10^e.

    std::string v(value);
    size_t e_pos = v.find('p');
    if (e_pos == std::string::npos) e_pos = v.find('P');

    std::string f, e;

	f = (e_pos != std::string::npos) ? v.substr(0, e_pos) : v;
    e = (e_pos != std::string::npos) ? v.substr(e_pos+1) : "0";    

    TRACE("mpf_dbg", tout << " f = " << f << " e = " << e << std::endl;);   

    scoped_mpq q(m_mpq_manager);    
    m_mpq_manager.set(q, f.c_str());

    scoped_mpz ex(m_mpq_manager);
    m_mpz_manager.set(ex, e.c_str());

    set(o, ebits, sbits, rm, q, ex);    

    TRACE("mpf_dbg", tout << "set: res = " << to_string(o) << std::endl;);
}

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, mpf_rounding_mode rm, mpq const & significand, mpz const & exponent) {
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
	
        // Normalize
        while (m_mpq_manager.ge(sig, 2)) {
            m_mpq_manager.div(sig, mpq(2), sig);
            m_mpz_manager.inc(exp);
        }
        
        while (m_mpq_manager.lt(sig, 1)) {
            m_mpq_manager.mul(sig, 2, sig);
            m_mpz_manager.dec(exp);
        }

        // 1.0 <= sig < 2.0
        SASSERT((m_mpq_manager.le(1, sig) && m_mpq_manager.lt(sig, 2)));
        
        TRACE("mpf_dbg", tout << "sig = " << m_mpq_manager.to_string(sig) << 
                                 " exp = " << m_mpz_manager.to_string(exp) << std::endl;);        

        m_mpz_manager.set(o.significand, 0);
        for (unsigned i = 0; i < (sbits+3); i++) {
            m_mpz_manager.mul2k(o.significand, 1);
            if (m_mpq_manager.ge(sig, 1)) {
                m_mpz_manager.inc(o.significand);
                m_mpq_manager.dec(sig);
            }
            m_mpq_manager.mul(sig, mpq(2), sig);
        }

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

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, bool sign, uint64 significand, mpf_exp_t exponent) {
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

void mpf_manager::set(mpf & o, unsigned ebits, unsigned sbits, bool sign, mpz const & significand, mpf_exp_t exponent) {
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
                if (!m_mpz_manager.is_even(o.significand)) sticky = true;
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
        if (!m_mpz_manager.is_zero(sticky_rem) && m_mpz_manager.is_even(b.significand()))
            m_mpz_manager.inc(b.significand());

        TRACE("mpf_dbg", tout << "A' = " << m_mpz_manager.to_string(a.significand()) << std::endl;);
        TRACE("mpf_dbg", tout << "B' = " << m_mpz_manager.to_string(b.significand()) << std::endl;);

        // Significand addition
        if (sgn(a) != sgn(b)) {
            TRACE("mpf_dbg", tout << "SUBTRACTING" << std::endl;);
            m_mpz_manager.sub(a.significand(), b.significand(), o.significand);
        }
        else {
            TRACE("mpf_dbg", tout << "ADDING" << std::endl;);
            m_mpz_manager.add(a.significand(), b.significand(), o.significand);
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
        m_mpz_manager.machine_div_rem(o.significand, m_powers2(x.sbits-4), o.significand, sticky_rem);
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

void mpf_manager::fused_mul_add(mpf_rounding_mode rm, mpf const & x, mpf const & y, mpf const &z, mpf & o) {
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
        if (is_zero(z) && rm != MPF_ROUND_TOWARD_NEGATIVE)
            mk_pzero(x.ebits, x.sbits, o);
        else
            set(o, z);
    }
    else {
        o.ebits = x.ebits;
        o.sbits = x.sbits;        

        scoped_mpf mul_res(*this, x.ebits+2, 2*x.sbits);
        scoped_mpf a(*this, x.ebits, x.sbits), b(*this, x.ebits, x.sbits), c(*this, x.ebits, x.sbits);
        set(a, x);
        set(b, y);
        set(c, z);
        unpack(a, true);
        unpack(b, true);
        unpack(c, true);        

        TRACE("mpf_dbg", tout << "A = " << to_string(a) << std::endl;);
        TRACE("mpf_dbg", tout << "B = " << to_string(b) << std::endl;);
        TRACE("mpf_dbg", tout << "C = " << to_string(c) << std::endl;);

        SASSERT(m_mpz_manager.lt(a.significand(), m_powers2(x.sbits)));
        SASSERT(m_mpz_manager.lt(b.significand(), m_powers2(x.sbits)));
        SASSERT(m_mpz_manager.lt(c.significand(), m_powers2(x.sbits)));
        SASSERT(m_mpz_manager.ge(a.significand(), m_powers2(x.sbits-1)));
        SASSERT(m_mpz_manager.ge(b.significand(), m_powers2(x.sbits-1)));        

        mul_res.get().sign = (a.sign() != b.sign());
        mul_res.get().exponent = a.exponent() + b.exponent();
        m_mpz_manager.mul(a.significand(), b.significand(), mul_res.get().significand);

        TRACE("mpf_dbg", tout << "PRODUCT = " << to_string(mul_res) << std::endl;);        

        // mul_res is [-1][0].[2*sbits - 2], i.e., between 2*sbits-1 and 2*sbits.
        SASSERT(m_mpz_manager.lt(mul_res.significand(), m_powers2(2*x.sbits)));
        SASSERT(m_mpz_manager.ge(mul_res.significand(), m_powers2(2*x.sbits - 2)));

        // Introduce extra bits into c.
        m_mpz_manager.mul2k(c.significand(), x.sbits-1, c.significand());

        SASSERT(m_mpz_manager.lt(c.significand(), m_powers2(2 * x.sbits - 1)));
        SASSERT(m_mpz_manager.is_zero(c.significand()) || 
                m_mpz_manager.ge(c.significand(), m_powers2(2 * x.sbits - 2)));

        TRACE("mpf_dbg", tout << "C = " << to_string(c) << std::endl;);

        if (exp(c) > exp(mul_res))
            mul_res.swap(c);

        mpf_exp_t exp_delta = exp(mul_res) - exp(c);

        SASSERT(exp(mul_res) >= exp(c) && exp_delta >= 0);

        if (exp_delta > 2 * x.sbits)
            exp_delta = 2 * x.sbits;
        TRACE("mpf_dbg", tout << "exp_delta = " << exp_delta << std::endl;);

        // Alignment shift with sticky bit computation.
        scoped_mpz sticky_rem(m_mpz_manager);
        m_mpz_manager.machine_div_rem(c.significand(), m_powers2((int)exp_delta), c.significand(), sticky_rem);
        TRACE("mpf_dbg", tout << "alignment shift -> sig = " << m_mpz_manager.to_string(c.significand()) << 
                         " sticky_rem = " << m_mpz_manager.to_string(sticky_rem) << std::endl;);
        if (!m_mpz_manager.is_zero(sticky_rem) && m_mpz_manager.is_even(c.significand()))
            m_mpz_manager.inc(c.significand());

        TRACE("mpf_dbg", tout << "M' = " << m_mpz_manager.to_string(mul_res.significand()) << std::endl;);
        TRACE("mpf_dbg", tout << "C' = " << m_mpz_manager.to_string(c.significand()) << std::endl;);

        // Significand addition
        if (sgn(mul_res) != sgn(c)) {
            TRACE("mpf_dbg", tout << "SUBTRACTING" << std::endl;);
            m_mpz_manager.sub(mul_res.significand(), c.significand(), o.significand);
        }
        else {
            TRACE("mpf_dbg", tout << "ADDING" << std::endl;);
            m_mpz_manager.add(mul_res.significand(), c.significand(), o.significand);
        }        

        TRACE("mpf_dbg", tout << "sum[-1:] = " << m_mpz_manager.to_string(o.significand) << std::endl;);

        bool neg = m_mpz_manager.is_neg(o.significand);
        TRACE("mpf_dbg", tout << "NEG=" << neg << std::endl;);
        if (neg) m_mpz_manager.abs(o.significand);
       
        o.exponent = mul_res.exponent();
        
        unsigned extra = x.sbits-4;
        // Result could overflow into 4.xxx ...
        SASSERT(m_mpz_manager.lt(o.significand, m_powers2(2 * x.sbits + 2)));
        if(m_mpz_manager.ge(o.significand, m_powers2(2 * x.sbits + 1))) 
        {
            extra++;
            o.exponent++;
            TRACE("mpf_dbg", tout << "Addition overflew!" << std::endl;);
        }        

        // Get rid of the extra bits.
        m_mpz_manager.machine_div_rem(o.significand, m_powers2(extra), o.significand, sticky_rem);
        if (!m_mpz_manager.is_zero(sticky_rem) && m_mpz_manager.is_even(o.significand))
            m_mpz_manager.inc(o.significand);
            
        TRACE("mpf_dbg", tout << "sum[-1:sbits+2] = " << m_mpz_manager.to_string(o.significand) << std::endl;);

        if (m_mpz_manager.is_zero(o.significand))
            mk_zero(x.ebits, x.sbits, rm == MPF_ROUND_TOWARD_NEGATIVE, o);
        else {            
            o.sign = ((!mul_res.sign() &&  c.sign() &&  neg) ||
                      ( mul_res.sign() && !c.sign() && !neg) ||
                      ( mul_res.sign() &&  c.sign()));            
            TRACE("mpf_dbg", tout << "before round = " << to_string(o) << std::endl <<
                             "fs[-1:sbits+2] = " << m_mpz_manager.to_string(o.significand) << std::endl;);
            round(rm, o);
        }
    }
       
}

void my_mpz_sqrt(unsynch_mpz_manager & m, unsigned sbits, bool odd_exp, mpz & in, mpz & o) {
    scoped_mpz lower(m), upper(m);
    scoped_mpz mid(m), product(m), diff(m);
    // we have lower <= a.significand <= upper and we need 1.[52+3 bits] in the bounds.
    // since we comapre upper*upper to a.significand further down, we need a.significand
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
                m.set(o, upper); // chosing upper is like a sticky bit here.
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

    if (is_nan(x) || is_ninf(x))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_pinf(x))
        set(o, x);
    else if (x.sign) {
        if (!m_mpz_manager.is_zero(x.significand))
            mk_nan(x.ebits, x.sbits, o);
        else
            mk_nzero(x.ebits, x.sbits, o);
    }
    else if (is_pzero(x))
        mk_pzero(x.ebits, x.sbits, o);
    else if (is_nzero(x))
        mk_nzero(x.ebits, x.sbits, o);
    else {
        o.ebits = x.ebits;
        o.sbits = x.sbits;
        o.sign = false;

        scoped_mpf a(*this);
        set(a, x);
        unpack(a, true);

        TRACE("mpf_dbg", tout << "A = " << to_string(a) << std::endl;);

        m_mpz_manager.mul2k(a.significand(), x.sbits + ((a.exponent() % 2)?6:5));        
        // my_mpz_sqrt(m_mpz_manager, x.sbits, a.exponent % 2 ? true : false, a.significand, o.significand);
        if (!m_mpz_manager.root(a.significand(), 2, o.significand))
        {
            // If the result is inexact, it is 1 too large.
            // We need a sticky bit in the last position here, so we fix that.
            if (m_mpz_manager.is_even(o.significand))
                m_mpz_manager.dec(o.significand);            
            TRACE("mpf_dbg", tout << "dec'ed " << m_mpz_manager.to_string(o.significand) << std::endl;);
        }
        o.exponent = a.exponent() >> 1;

        round_sqrt(rm, o);        
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
    else if (x.exponent < 0) 
        mk_zero(x.ebits, x.sbits, x.sign, o);
    else if (x.exponent >= x.sbits-1)
        set(o, x);
    else {
        SASSERT(x.exponent >= 0 && x.exponent < x.sbits-1);

        o.ebits = x.ebits;
        o.sbits = x.sbits;
        o.sign = x.sign;

        scoped_mpf a(*this);
        set(a, x);
        unpack(a, true);

        TRACE("mpf_dbg", tout << "A = " << to_string(a) << std::endl;);
                
        o.exponent = a.exponent();
        m_mpz_manager.set(o.significand, a.significand());

        unsigned q = (unsigned) o.exponent;
        unsigned shift = o.sbits-q-1;
        TRACE("mpf_dbg", tout << "Q = " << q << " shift=" << shift << std::endl;);
        m_mpz_manager.machine_div2k(o.significand, shift);
        m_mpz_manager.mul2k(o.significand, shift+3);

        round(rm, o);
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
        bool last = false, round = false, sticky = m_mpz_manager.is_odd(z);
        for (; e != 0; e++) {            
            m_mpz_manager.machine_div2k(z, 1);
            sticky |= round;
            round = last;
            last = m_mpz_manager.is_odd(z);
        }
        bool inc = false;
        switch (rm) {
        case MPF_ROUND_NEAREST_TEVEN: inc = round && (last || sticky); break;
        case MPF_ROUND_NEAREST_TAWAY: inc = round && (!last || sticky); break; // CMW: Check!
        case MPF_ROUND_TOWARD_POSITIVE: inc = (!x.sign && (round || sticky)); break;
        case MPF_ROUND_TOWARD_NEGATIVE: inc = (x.sign && (round || sticky)); break;
        case MPF_ROUND_TOWARD_ZERO: inc = false; break;
        default: UNREACHABLE();
        }
        if (inc) m_mpz_manager.inc(z);
    }
    else
        m_mpz_manager.mul2k(z, (unsigned) e);

    m_mpq_manager.set(o, z);
    if (x.sign) m_mpq_manager.neg(o);
}

void mpf_manager::rem(mpf const & x, mpf const & y, mpf & o) {
    SASSERT(x.sbits == y.sbits && x.ebits == y.ebits);

    TRACE("mpf_dbg", tout << "X = " << to_string(x) << std::endl;);
    TRACE("mpf_dbg", tout << "Y = " << to_string(y) << std::endl;);

    if (is_nan(x) || is_nan(y))
        mk_nan(x.ebits, x.sbits, o);
    else if (is_inf(x)) 
        mk_nan(x.ebits, x.sbits, o);
    else if (is_inf(y))
        set(o, x);
    else if (is_zero(x))        
        set(o, x);
    else if (is_zero(y))
        mk_nan(x.ebits, x.sbits, o);
    else {        
        o.ebits = x.ebits;
        o.sbits = x.sbits;
        o.sign = x.sign;

        scoped_mpf a(*this), b(*this);
        set(a, x);
        set(b, y);
        unpack(a, true);
        unpack(b, true);

        TRACE("mpf_dbg", tout << "A = " << to_string(a) << std::endl;);
        TRACE("mpf_dbg", tout << "B = " << to_string(b) << std::endl;);
        
        if (a.exponent() < b.exponent())
            set(o, x);
        else {            
            mpf_exp_t exp_diff = a.exponent() - b.exponent();
            SASSERT(exp_diff >= 0);
            TRACE("mpf_dbg", tout << "exp_diff = " << exp_diff << std::endl;);

            SASSERT(exp_diff < INT_MAX);
            // CMW: This requires rather a lot of memory. There are algorithms that trade space for time by
            // computing only a small chunk of the remainder bits at a time. 
            unsigned extra_bits = (unsigned) exp_diff;
            m_mpz_manager.mul2k(a.significand(), extra_bits);
            m_mpz_manager.rem(a.significand(), b.significand(), o.significand);        

            TRACE("mpf_dbg", tout << "REM' = " << to_string(o) << std::endl;);

            if (m_mpz_manager.is_zero(o.significand))
                mk_zero(o.ebits, o.sbits, o.sign, o);
            else {
                o.exponent = b.exponent();
                m_mpz_manager.mul2k(o.significand, 3); // rounding bits
                round(MPF_ROUND_NEAREST_TEVEN, o);
            }
        }
    }

    TRACE("mpf_dbg", tout << "REMAINDER = " << to_string(o) << std::endl;);
}

void mpf_manager::maximum(mpf const & x, mpf const & y, mpf & o) {
    if (is_nan(x) || (is_zero(x) && is_zero(y)))
        set(o, y);
    else if (is_nan(y))
        set(o, x);
    else if (gt(x, y))
        set(o, x);
    else
        set(o, y);
}

void mpf_manager::minimum(mpf const & x, mpf const & y, mpf & o) {
    if (is_nan(x) || (is_zero(x) && is_zero(y)))
        set(o, y);
    else if (is_nan(y))
        set(o, x);
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
    uint64 raw = 0;    
    int64 sig = 0, exp = 0;

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

    uint64 q = m_mpz_manager.get_uint64(x.significand);
    SASSERT(q < 4294967296ull);
    sig = q & 0x00000000FFFFFFFF;
    sig <<= 24 - x.sbits;

    if (has_top_exp(x))
        exp = +128;
    else if (has_bot_exp(x))
        exp = -127;
    else {
        int64 q = x.exponent;
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
    return !(has_top_exp(x) || is_denormal(x));
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
    // Insert the hidden bit or adjust the exponent of denormal numbers.    
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
    // Assumptions: o.significand is of the form f[-1:0] . f[1:sbits-1] [guard,round,sticky], 
    // i.e., it has 2 + (sbits-1) + 3 = sbits + 4 bits.

    TRACE("mpf_dbg", tout << "RND: " << to_string(o) << std::endl;);

    DEBUG_CODE({
        const mpz & p_m3 = m_powers2(o.sbits+5);
        SASSERT(m_mpz_manager.lt(o.significand, p_m3));
    });

    // Structure of the rounder:
    // (s, e_out, f_out) == (s, exprd(s, post(e, sigrd(s, f)))).

    bool UNFen = false; // Are these supposed to be persistent flags accross calls?
    bool OVFen = false;

    mpf_exp_t e_max_norm = mk_max_exp(o.ebits);
    mpf_exp_t e_min_norm = mk_min_exp(o.ebits);
    scoped_mpz temporary(m_mpq_manager);    

    TRACE("mpf_dbg", tout << "e_min_norm = " << e_min_norm << std::endl <<
                             "e_max_norm = " << e_max_norm << std::endl;);    

    const mpz & p_m1 = m_powers2(o.sbits+2);
    const mpz & p_m2 = m_powers2(o.sbits+3);    
    
    TRACE("mpf_dbg", tout << "p_m1 = " << m_mpz_manager.to_string(p_m1) << std::endl <<
                             "p_m2 = " << m_mpz_manager.to_string(p_m2) << std::endl;);    

    bool OVF1 = o.exponent > e_max_norm || // Exponent OVF
                (o.exponent == e_max_norm && m_mpz_manager.ge(o.significand, p_m2));

    TRACE("mpf_dbg", tout << "OVF1 = " << OVF1 << std::endl;);

    int lz = 0;
    scoped_mpz t(m_mpq_manager); 
    m_mpz_manager.set(t, p_m2);
    while (m_mpz_manager.gt(t, o.significand)) {
        m_mpz_manager.machine_div2k(t, 1);
        lz++;
    }

    TRACE("mpf_dbg", tout << "LZ = " << lz << std::endl;);

    m_mpz_manager.set(t, o.exponent);
    m_mpz_manager.inc(t);
    m_mpz_manager.sub(t, lz, t);
    m_mpz_manager.set(temporary, e_min_norm);
    m_mpz_manager.sub(t, temporary, t);
    bool TINY = m_mpz_manager.is_neg(t);

    TRACE("mpf_dbg", tout << "TINY = " << TINY << std::endl;);

    mpf_exp_t alpha = 3 << (o.ebits-2);
    mpf_exp_t beta = o.exponent - lz + 1;

    TRACE("mpf_dbg", tout << "alpha = " << alpha << std::endl <<
                             "beta = " << beta << std::endl; );

    scoped_mpz sigma(m_mpq_manager);
    sigma = 0;

    if (TINY && !UNFen) {
        m_mpz_manager.set(sigma, o.exponent);
        m_mpz_manager.sub(sigma, temporary, sigma);
        m_mpz_manager.inc(sigma);
    }
    else
        m_mpz_manager.set(sigma, lz);

    scoped_mpz limit(m_mpq_manager);
    limit = o.sbits + 2;
    m_mpz_manager.neg(limit);
    if (m_mpz_manager.lt(sigma, limit)) {
        m_mpz_manager.set(sigma, limit);
    }
        
    // Normalization shift    

    TRACE("mpf_dbg", tout << "Shift distance: " << m_mpz_manager.to_string(sigma) << " " << ((m_mpz_manager.is_nonneg(sigma))?"(LEFT)":"(RIGHT)") << std::endl;);

    bool sticky = !m_mpz_manager.is_even(o.significand);
    m_mpz_manager.machine_div2k(o.significand, 1); // Let f' = f_r/2
    
    if (!m_mpz_manager.is_zero(sigma)) {
        if (m_mpz_manager.is_neg(sigma)) { // Right shift
            unsigned sigma_uint = (unsigned) -m_mpz_manager.get_int64(sigma); // sigma is capped, this is safe.
            if (sticky)
                m_mpz_manager.machine_div2k(o.significand, sigma_uint);
            else
            {
                scoped_mpz sticky_rem(m_mpz_manager);                
                m_mpz_manager.machine_div_rem(o.significand, m_powers2(sigma_uint), o.significand, sticky_rem);
                sticky = !m_mpz_manager.is_zero(sticky_rem);
            }
        }
        else { // Left shift
            unsigned sh_m = static_cast<unsigned>(m_mpz_manager.get_int64(sigma));
            m_mpz_manager.mul2k(o.significand, sh_m, o.significand);
            m_mpz_manager.set(sigma, 0);
        }
    }

    TRACE("mpf_dbg", tout << "Before sticky: " << to_string(o) << std::endl;);

    // Make sure o.significand is a [sbits+2] bit number (i.e. f1[0:sbits+1] == f1[0:sbits-1][round][sticky])
    sticky = sticky || !m_mpz_manager.is_even(o.significand);
    m_mpz_manager.machine_div2k(o.significand, 1);    
    if (sticky && m_mpz_manager.is_even(o.significand))
        m_mpz_manager.inc(o.significand);

    if (OVF1 && OVFen) {
        o.exponent = beta;
        o.exponent -= alpha;
    }
    else if (TINY && UNFen) {
        o.exponent = beta;
        o.exponent += alpha;
    }
    else if (TINY && !UNFen)
        o.exponent = e_min_norm;
    else
        o.exponent = beta;

    TRACE("mpf_dbg", tout << "Shifted: " << to_string(o) << std::endl;);
    
    const mpz & p_sig = m_powers2(o.sbits);    
    SASSERT(TINY || (m_mpz_manager.ge(o.significand, p_sig)));

    // Significand rounding (sigrd)
    
    sticky = !m_mpz_manager.is_even(o.significand); // new sticky bit!
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
    // case MPF_ROUND_NEAREST_TAWAY: inc = round; break; // CMW: Check
    case MPF_ROUND_NEAREST_TAWAY: inc = round && (!last || sticky); break; // CMW: Fix ok?
    case MPF_ROUND_TOWARD_POSITIVE: inc = (!o.sign && (round || sticky)); break;
    case MPF_ROUND_TOWARD_NEGATIVE: inc = (o.sign && (round || sticky)); break;
    case MPF_ROUND_TOWARD_ZERO: inc = false; break;
    default: UNREACHABLE();
    }

    if (inc) {
        TRACE("mpf_dbg", tout << "Rounding increment -> significand +1" << std::endl;);
        m_mpz_manager.inc(o.significand);
    }
    else
        TRACE("mpf_dbg", tout << "Rounding increment -> significand +0" << std::endl;);

    TRACE("mpf_dbg", tout << "Rounded significand: " << to_string(o) << std::endl;);

    bool SIGovf = false;

    // Post normalization (post)
    
    if (m_mpz_manager.ge(o.significand, p_sig)) {            
        m_mpz_manager.machine_div2k(o.significand, 1);
        o.exponent++;
    }

    if (o.exponent > e_max_norm)
        SIGovf = true;

    TRACE("mpf_dbg", tout << "Post-normalized: " << to_string(o) << std::endl;);

    TRACE("mpf_dbg", tout << "SIGovf = " << SIGovf << std::endl;);
    
    // Exponent rounding (exprd)

    bool o_has_max_exp = (o.exponent > e_max_norm);
    bool OVF2 = SIGovf && o_has_max_exp;    

    TRACE("mpf_dbg", tout << "OVF2 = " << OVF2 << std::endl;);
    TRACE("mpf_dbg", tout << "o_has_max_exp = " << o_has_max_exp << std::endl;);

    if (!OVFen && OVF2)
        mk_round_inf(rm, o);
    else {        
        const mpz & p = m_powers2(o.sbits-1);
        TRACE("mpf_dbg", tout << "P: " << m_mpz_manager.to_string(p_m1) << std::endl;);            

        if (m_mpz_manager.ge(o.significand, p)) {
            TRACE("mpf_dbg", tout << "NORMAL: " << m_mpz_manager.to_string(o.significand) << std::endl;);
            m_mpz_manager.sub(o.significand, p, o.significand);
        }
        else {
            TRACE("mpf_dbg", tout << "DENORMAL: " << m_mpz_manager.to_string(o.significand) << std::endl;);
            o.exponent = mk_bot_exp(o.ebits);
        }
    }    

    TRACE("mpf_dbg", tout << "ROUNDED = " << to_string(o) << std::endl;);
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
