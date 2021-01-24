/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    mpbq.cpp

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
#include<sstream>
#include "util/mpbq.h"

#ifdef Z3DEBUG
#define MPBQ_DEBUG
#endif 

rational to_rational(mpbq const & v) {
    rational r(v.numerator());
    rational twok;
    twok = power(rational(2), v.k());
    return r/twok;
}

mpbq_manager::mpbq_manager(unsynch_mpz_manager & m):
    m_manager(m) {
}

mpbq_manager::~mpbq_manager() {
    del(m_addmul_tmp);
    m_manager.del(m_tmp);
    m_manager.del(m_tmp2);
    m_manager.del(m_select_int_tmp1);
    m_manager.del(m_select_int_tmp2);
    m_manager.del(m_select_small_tmp);
    del(m_select_small_tmp1);
    del(m_select_small_tmp2);
    m_manager.del(m_div_tmp1);
    m_manager.del(m_div_tmp2);
    m_manager.del(m_div_tmp3);
}

void mpbq_manager::reset(mpbq_vector & v) {
    for (auto & e : v) 
        reset(e);
    v.reset();
}

void mpbq_manager::normalize(mpbq & a) {
    if (a.m_k == 0)
        return;
    if (m_manager.is_zero(a.m_num)) {
        a.m_k = 0;
        return;
    }
#ifdef MPBQ_DEBUG
    rational r = to_rational(a);
#endif
    unsigned k = m_manager.power_of_two_multiple(a.m_num);
    if (k > a.m_k)
        k = a.m_k;
    m_manager.machine_div2k(a.m_num, k);
    a.m_k -= k;
#ifdef MPBQ_DEBUG
    rational new_r = to_rational(a);
    SASSERT(r == new_r);
#endif
}

int mpbq_manager::magnitude_lb(mpbq const & a) {
    if (m_manager.is_zero(a.m_num))
        return 0;
    if (m_manager.is_pos(a.m_num))
        return m_manager.log2(a.m_num) - a.m_k;
    return m_manager.mlog2(a.m_num) - a.m_k + 1;
}

int mpbq_manager::magnitude_ub(mpbq const & a) {
    if (m_manager.is_zero(a.m_num))
        return 0;
    if (m_manager.is_pos(a.m_num))
        return m_manager.log2(a.m_num) - a.m_k + 1;
    return m_manager.mlog2(a.m_num) - a.m_k;
}

void mpbq_manager::mul2(mpbq & a) {
    if (a.m_k == 0)
        m_manager.mul2k(a.m_num, 1);
    else
        a.m_k--;
}

void mpbq_manager::mul2k(mpbq & a, unsigned k) {
    if (k == 0)
        return;
    if (a.m_k < k) {
        m_manager.mul2k(a.m_num, k - a.m_k);
        a.m_k = 0;
    }
    else {
        SASSERT(a.m_k >= k);
        a.m_k -= k;
    }
}

void mpbq_manager::add(mpbq const & a, mpbq const & b, mpbq & r) {
#ifdef MPBQ_DEBUG
    rational _a = to_rational(a);
    rational _b = to_rational(b);
#endif
    if (a.m_k == b.m_k) {
        m_manager.add(a.m_num, b.m_num, r.m_num);
        r.m_k = a.m_k;
    }
    else if (a.m_k < b.m_k) {
        m_manager.mul2k(a.m_num, b.m_k - a.m_k, m_tmp);
        m_manager.add(b.m_num, m_tmp, r.m_num);
        r.m_k = b.m_k;
    }
    else {
        SASSERT(a.m_k > b.m_k);
        m_manager.mul2k(b.m_num, a.m_k - b.m_k, m_tmp);
        m_manager.add(a.m_num, m_tmp, r.m_num);
        r.m_k = a.m_k;
    }
    normalize(r);
#ifdef MPBQ_DEBUG
    rational _r = to_rational(r);
    SASSERT(_a + _b == _r);
#endif 
}

void mpbq_manager::add(mpbq const & a, mpz const & b, mpbq & r) {
#ifdef MPBQ_DEBUG
    rational _a = to_rational(a);
    rational _b(b);
#endif
    if (a.m_k == 0) {
        m_manager.add(a.m_num, b, r.m_num);
        r.m_k = a.m_k;
    }
    else {
        m_manager.mul2k(b, a.m_k, m_tmp);
        m_manager.add(a.m_num, m_tmp, r.m_num);
        r.m_k = a.m_k;
    }
    normalize(r);
#ifdef MPBQ_DEBUG
    rational _r = to_rational(r);
    TRACE("mpbq_bug", tout << "add a: " << _a << ", b: " << _b << ", r: " << _r << ", expected: " << (_a + _b) << "\n";);
    SASSERT(_a + _b == _r);
#endif 
}

void mpbq_manager::sub(mpbq const & a, mpbq const & b, mpbq & r) {
#ifdef MPBQ_DEBUG
    rational _a = to_rational(a);
    rational _b = to_rational(b);
#endif
    if (a.m_k == b.m_k) {
        m_manager.sub(a.m_num, b.m_num, r.m_num);
        r.m_k = a.m_k;
    }
    else if (a.m_k < b.m_k) {
        m_manager.mul2k(a.m_num, b.m_k - a.m_k, m_tmp);
        m_manager.sub(m_tmp, b.m_num, r.m_num);
        r.m_k = b.m_k;
    }
    else {
        SASSERT(a.m_k > b.m_k);
        m_manager.mul2k(b.m_num, a.m_k - b.m_k, m_tmp);
        m_manager.sub(a.m_num, m_tmp, r.m_num);
        r.m_k = a.m_k;
    }
    normalize(r);
#ifdef MPBQ_DEBUG
    rational _r = to_rational(r);
    TRACE("mpbq_bug", tout << "sub a: " << _a << ", b: " << _b << ", r: " << _r << ", expected: " << (_a - _b) << "\n";);
    SASSERT(_a - _b == _r);
#endif 
}

void mpbq_manager::sub(mpbq const & a, mpz const & b, mpbq & r) {
#ifdef MPBQ_DEBUG
    rational _a = to_rational(a);
    rational _b(b);
#endif
    if (a.m_k == 0) {
        m_manager.sub(a.m_num, b, r.m_num);
        r.m_k = a.m_k;
    }
    else {
        m_manager.mul2k(b, a.m_k, m_tmp);
        m_manager.sub(a.m_num, m_tmp, r.m_num);
        r.m_k = a.m_k;
    }
    normalize(r);
#ifdef MPBQ_DEBUG
    rational _r = to_rational(r);
    SASSERT(_a - _b == _r);
#endif 
}

void mpbq_manager::mul(mpbq const & a, mpbq const & b, mpbq & r) {
#ifdef MPBQ_DEBUG
    rational _a = to_rational(a);
    rational _b = to_rational(b);
#endif
    m_manager.mul(a.m_num, b.m_num, r.m_num);
    r.m_k = a.m_k + b.m_k;
    if (a.m_k == 0 || b.m_k == 0) {
        // if a.m_k and b.m_k are greater than 0, then there is no point in normalizing r.
        normalize(r);
    }
#ifdef MPBQ_DEBUG
    rational _r = to_rational(r);
    SASSERT(_a * _b == _r);
#endif 
}

void mpbq_manager::mul(mpbq const & a, mpz const & b, mpbq & r) {
#ifdef MPBQ_DEBUG
    rational _a = to_rational(a);
    rational _b(b);
#endif
    m_manager.mul(a.m_num, b, r.m_num);
    r.m_k = a.m_k;
    normalize(r);
#ifdef MPBQ_DEBUG
    rational _r = to_rational(r);
    SASSERT(_a * _b == _r);
#endif 
}

void mpbq_manager::power(mpbq & a, unsigned k) {
    SASSERT(static_cast<uint64_t>(k) * static_cast<uint64_t>(a.k()) <= static_cast<uint64_t>(UINT_MAX));
    // We don't need to normalize because:
    //   If a.m_k == 0, then a is an integer, and the result be an integer
    //   If a.m_k > 0, then a.m_num must be odd, and the (a.m_num)^k will also be odd
    a.m_k *= k;
    m_manager.power(a.m_num, k, a.m_num);
}

bool mpbq_manager::root_lower(mpbq & a, unsigned n) {
    bool r = m_manager.root(a.m_num, n);
    if (!r)
        m_manager.dec(a.m_num);
    if (a.m_k % n == 0) {
        a.m_k /= n;
        normalize(a);
        return r;
    }
    else if (m_manager.is_neg(a.m_num)) {
        a.m_k /= n;
        normalize(a);
        return false;
    }
    else {
        a.m_k /= n;
        a.m_k++;
        normalize(a);
        return false;
    }
}

bool mpbq_manager::root_upper(mpbq & a, unsigned n) {
    bool r = m_manager.root(a.m_num, n);
    if (a.m_k % n == 0) {
        a.m_k /= n;
        normalize(a);
        return r;
    }
    else if (m_manager.is_neg(a.m_num)) {
        a.m_k /= n;
        a.m_k++;
        normalize(a);
        return false;
    }
    else {
        a.m_k /= n;
        normalize(a);
        return false;
    }
}

bool mpbq_manager::lt(mpbq const & a, mpbq const & b) {
    // TODO: try the following trick when k1 != k2
    // Given, a = n1/2^k1    b = n2/2^k2
    // Suppose n1 > 0 and n2 > 0,
    // Then, we have, n1 <= 2^{log2(n1) - k1}  2^{log2(n2) - 1 - k2} <= n2
    // Thus, log2(n1) - k1 < log2(n2) - 1 - k2      implies a < b   
    // Similarly: log2(n2) - k2 < log2(n1) - 1 - k1 implies b < a
    // That is we compare the "magnitude" of the numbers before performing mul2k
    // 
    // If n1 < 0 and n2 < 0, a similar trick can be implemented using mlog2 instead log2. 
    //
    // It seems the trick is not useful when n1 and n2 are small
    // numbers, and k1 and k2 very small < 8.  Since, no bignumber
    // computation is needed for mul2k.

    if (a.m_k == b.m_k) {
        return m_manager.lt(a.m_num, b.m_num);
    }
    else if (a.m_k < b.m_k) {
        m_manager.mul2k(a.m_num, b.m_k - a.m_k, m_tmp);
        return m_manager.lt(m_tmp, b.m_num);
    }
    else {
        SASSERT(a.m_k > b.m_k);
        m_manager.mul2k(b.m_num, a.m_k - b.m_k, m_tmp);
        return m_manager.lt(a.m_num, m_tmp);
    }
}

bool mpbq_manager::lt_1div2k(mpbq const & a, unsigned k) {
    if (m_manager.is_nonpos(a.m_num))
        return true;
    if (a.m_k <= k) {
        // since a.m_num >= 1
        return false;
    }
    else {
        SASSERT(a.m_k > k);
        m_manager.mul2k(mpz(1), a.m_k - k, m_tmp);
        return m_manager.lt(a.m_num, m_tmp);
    }
}

bool mpbq_manager::eq(mpbq const & a, mpq const & b) {
    if (is_int(a) && m_manager.is_one(b.denominator()))
        return m_manager.eq(a.m_num, b.numerator());
    m_manager.mul2k(b.numerator(), a.m_k, m_tmp);
    m_manager.mul(a.m_num, b.denominator(), m_tmp2);
    return m_manager.eq(m_tmp, m_tmp2);
}

bool mpbq_manager::lt(mpbq const & a, mpq const & b) {
    if (is_int(a) && m_manager.is_one(b.denominator()))
        return m_manager.lt(a.m_num, b.numerator());
    m_manager.mul(a.m_num, b.denominator(), m_tmp);
    m_manager.mul2k(b.numerator(), a.m_k, m_tmp2);
    return m_manager.lt(m_tmp, m_tmp2);
}

bool mpbq_manager::le(mpbq const & a, mpq const & b) {
    if (is_int(a) && m_manager.is_one(b.denominator()))
        return m_manager.le(a.m_num, b.numerator());
    m_manager.mul(a.m_num, b.denominator(), m_tmp);
    m_manager.mul2k(b.numerator(), a.m_k, m_tmp2);
    return m_manager.le(m_tmp, m_tmp2);
}

bool mpbq_manager::lt(mpbq const & a, mpz const & b) {
    if (is_int(a))
        return m_manager.lt(a.m_num, b);
    m_manager.mul2k(b, a.m_k, m_tmp);
    return m_manager.lt(a.m_num, m_tmp);
}

bool mpbq_manager::le(mpbq const & a, mpz const & b) {
    if (is_int(a))
        return m_manager.le(a.m_num, b);
    m_manager.mul2k(b, a.m_k, m_tmp);
    return m_manager.le(a.m_num, m_tmp);
}

std::string mpbq_manager::to_string(mpbq const & a) {
    std::ostringstream buffer;
    buffer << m_manager.to_string(a.m_num);
    if (a.m_k == 1)
        buffer << "/2";
    else if (a.m_k > 1)
        buffer << "/2^" << a.m_k;
    return buffer.str();
}

std::ostream& mpbq_manager::display(std::ostream & out, mpbq const & a) {
    out << m_manager.to_string(a.m_num);
    if (a.m_k > 0)
        out << "/2";
    if (a.m_k > 1)
        out << "^" << a.m_k;
    return out;
}

std::ostream& mpbq_manager::display_pp(std::ostream & out, mpbq const & a) {
    out << m_manager.to_string(a.m_num);
    if (a.m_k > 0)
        out << "/2";
    if (a.m_k > 1)
        out << "<sup>" << a.m_k << "</sup>";
    return out;
}

std::ostream& mpbq_manager::display_smt2(std::ostream & out, mpbq const & a, bool decimal) {
    if (a.m_k == 0) {
        m_manager.display_smt2(out, a.m_num, decimal);
    }
    else {
        out << "(/ ";
        m_manager.display_smt2(out, a.m_num, decimal);
        out << " ";
        out << "(^ 2";
        if (decimal) out << ".0";
        out << " " << a.m_k;
        if (decimal) out << ".0";
        out << "))";
    }
    return out;
}

std::ostream& mpbq_manager::display_decimal(std::ostream & out, mpbq const & a, unsigned prec) {
    if (is_int(a)) {
        return out << m_manager.to_string(a.m_num);
    }
    mpz two(2);
    mpz ten(10);
    mpz two_k;
    mpz n1, v1;
    if (m_manager.is_neg(a.m_num))
        out << "-";
    m_manager.set(v1, a.m_num);
    m_manager.abs(v1);
    m_manager.power(two, a.m_k, two_k);
    m_manager.rem(v1, two_k, n1);
    m_manager.div(v1, two_k, v1);
    SASSERT(!m_manager.is_zero(n1));
    out << m_manager.to_string(v1);
    out << ".";
    for (unsigned i = 0; i < prec; i++) {
        m_manager.mul(n1, ten, n1);
        m_manager.div(n1, two_k, v1);
        m_manager.rem(n1, two_k, n1);
        out << m_manager.to_string(v1);
        if (m_manager.is_zero(n1)) 
            goto end;
    }
    out << "?";
 end:
    m_manager.del(n1);
    m_manager.del(v1);
    m_manager.del(two_k);
    return out;
}

std::ostream& mpbq_manager::display_decimal(std::ostream & out, mpbq const & a, mpbq const & b, unsigned prec) {
    mpz two(2);
    mpz ten(10);
    mpz two_k1, two_k2;
    mpz n1, v1, n2, v2;
    if (m_manager.is_neg(a.m_num) != m_manager.is_neg(b.m_num)) 
        return out << "?";
    if (m_manager.is_neg(a.m_num))
        out << "-";
    m_manager.set(v1, a.m_num);
    m_manager.abs(v1);
    m_manager.set(v2, b.m_num);
    m_manager.abs(v2);
    m_manager.power(two, a.m_k, two_k1);
    m_manager.power(two, b.m_k, two_k2);
    m_manager.rem(v1, two_k1, n1);
    m_manager.rem(v2, two_k2, n2);
    m_manager.div(v1, two_k1, v1);
    m_manager.div(v2, two_k2, v2);
    if (!m_manager.eq(v1, v2)) {
        out << "?";
        goto end;
    }
    
    out << m_manager.to_string(v1);
    if (m_manager.is_zero(n1) && m_manager.is_zero(n2))
        goto end; // number is an integer
    out << ".";
    for (unsigned i = 0; i < prec; i++) {
        m_manager.mul(n1, ten, n1);
        m_manager.mul(n2, ten, n2);
        m_manager.div(n1, two_k1, v1);
        m_manager.div(n2, two_k2, v2);
        if (m_manager.eq(v1, v2)) {
            out << m_manager.to_string(v1);
        }
        else {
            out << "?";
            goto end;
        }
        m_manager.rem(n1, two_k1, n1);
        m_manager.rem(n2, two_k2, n2);
        if (m_manager.is_zero(n1) && m_manager.is_zero(n2))
            goto end; // number is precise
    }
    out << "?";
 end:
    m_manager.del(n1);
    m_manager.del(v1);
    m_manager.del(n2);
    m_manager.del(v2);
    m_manager.del(two_k1);
    m_manager.del(two_k2);
    return out;
}

bool mpbq_manager::to_mpbq(mpq const & q, mpbq & bq) {
    mpz const & n = q.numerator();
    mpz const & d = q.denominator();
    unsigned shift;
    if (m_manager.is_one(d)) {
        set(bq, n);
        SASSERT(eq(bq, q));
        return true;
    }
    else if (m_manager.is_power_of_two(d, shift)) {
        SASSERT(shift>=1);
        unsigned k = shift;
        set(bq, n, k);
        SASSERT(eq(bq, q));
        return true;
    }
    else {
        unsigned k = m_manager.log2(d);
        set(bq, n, k+1);
        return false;
    }
}

void mpbq_manager::refine_upper(mpq const & q, mpbq & l, mpbq & u) {
    SASSERT(lt(l, q) && gt(u, q));
    SASSERT(!m_manager.is_power_of_two(q.denominator()));
    // l < q < u
    mpbq mid; 
    while (true) {
        add(l, u, mid);
        div2(mid);
        if (gt(mid, q)) {
            swap(u, mid);
            del(mid);
            SASSERT(lt(l, q) && gt(u, q));
            return;
        }
        swap(l, mid);
    }
}

void mpbq_manager::refine_lower(mpq const & q, mpbq & l, mpbq & u) {
    SASSERT(lt(l, q) && gt(u, q));
    SASSERT(!m_manager.is_power_of_two(q.denominator()));
    // l < q < u
    mpbq mid; 
    while (true) {
        add(l, u, mid);
        div2(mid);
        if (lt(mid, q)) {
            swap(l, mid);
            del(mid);
            SASSERT(lt(l, q) && gt(u, q));
            return;
        }
        swap(u, mid);
    }
}

// sectect integer in [lower, upper]
bool mpbq_manager::select_integer(mpbq const & lower, mpbq const & upper, mpz & r) {
    if (is_int(lower)) {
        m_manager.set(r, lower.m_num);
        return true;
    }
    if (is_int(upper)) {
        m_manager.set(r, upper.m_num);
        return true;
    }
    mpz & ceil_lower  = m_select_int_tmp1;
    mpz & floor_upper = m_select_int_tmp2;
    ceil(m_manager, lower, ceil_lower);
    floor(m_manager, upper, floor_upper);
    if (m_manager.le(ceil_lower, floor_upper)) {
        m_manager.set(r, ceil_lower);
        return true;
    }
    return false;
}

// select integer in (lower, upper]
bool mpbq_manager::select_integer(unsynch_mpq_manager & qm, mpq const & lower, mpbq const & upper, mpz & r) {
    if (is_int(upper)) {
        m_manager.set(r, upper.m_num);
        return true;
    }
    mpz & ceil_lower  = m_select_int_tmp1;
    mpz & floor_upper = m_select_int_tmp2;
    if (qm.is_int(lower)) {
        m_manager.set(ceil_lower, lower.numerator());
        m_manager.inc(ceil_lower);
    }
    else {
        scoped_mpz tmp(qm);
        qm.ceil(lower, tmp);
        m_manager.set(ceil_lower, tmp);
    }
    floor(m_manager, upper, floor_upper);
    if (m_manager.le(ceil_lower, floor_upper)) {
        m_manager.set(r, ceil_lower);
        return true;
    }
    return false;
}

// sectect integer in [lower, upper)
bool mpbq_manager::select_integer(unsynch_mpq_manager & qm, mpbq const & lower, mpq const & upper, mpz & r) {
    if (is_int(lower)) {
        m_manager.set(r, lower.m_num);
        return true;
    }
    mpz & ceil_lower  = m_select_int_tmp1;
    mpz & floor_upper = m_select_int_tmp2;
    ceil(m_manager, lower, ceil_lower);
    if (qm.is_int(upper)) {
        m_manager.set(floor_upper, upper.numerator());
        m_manager.dec(floor_upper);
    }
    else {
        scoped_mpz tmp(qm);
        qm.floor(upper, tmp);
        m_manager.set(floor_upper, tmp);
    }
    if (m_manager.le(ceil_lower, floor_upper)) {
        m_manager.set(r, ceil_lower);
        return true;
    }
    return false;
}

// sectect integer in (lower, upper)
bool mpbq_manager::select_integer(unsynch_mpq_manager & qm, mpq const & lower, mpq const & upper, mpz & r) {
    mpz & ceil_lower  = m_select_int_tmp1;
    mpz & floor_upper = m_select_int_tmp2;

    if (qm.is_int(lower)) {
        m_manager.set(ceil_lower, lower.numerator());
        m_manager.inc(ceil_lower);
    }
    else {
        scoped_mpz tmp(qm);
        qm.ceil(lower, tmp);
        m_manager.set(ceil_lower, tmp);
    }

    if (qm.is_int(upper)) {
        m_manager.set(floor_upper, upper.numerator());
        m_manager.dec(floor_upper);
    }
    else {
        scoped_mpz tmp(qm);
        qm.floor(upper, tmp);
        m_manager.set(floor_upper, tmp);
    }

    if (m_manager.le(ceil_lower, floor_upper)) {
        m_manager.set(r, ceil_lower);
        return true;
    }
    return false;
}

#define LINEAR_SEARCH_THRESHOLD 8

void mpbq_manager::select_small_core(mpbq const & lower, mpbq const & upper, mpbq & r) {
    SASSERT(le(lower, upper));
    mpz & aux = m_select_small_tmp;
    if (select_integer(lower, upper, aux)) {
        set(r, aux);
        return;
    }

    // At this point we know that k=0 does not work, since there is no integer 
    // in the interval [lower, upper]
    unsigned min_k = 0;
    unsigned max_k = std::min(lower.m_k, upper.m_k);
    
    if (max_k <= LINEAR_SEARCH_THRESHOLD) {
        unsigned k = 0;
        mpbq & l2k = m_select_small_tmp1;
        mpbq & u2k = m_select_small_tmp2;
        set(l2k, lower);
        set(u2k, upper);
        while (true) {
            k++;
            mul2(l2k);
            mul2(u2k);
            if (select_integer(l2k, u2k, aux)) {
                set(r, aux, k);
                break;
            }
        }
    }
    else {
        mpbq & l2k = m_select_small_tmp1;
        mpbq & u2k = m_select_small_tmp2;
        while (true) {
            unsigned mid_k = min_k + (max_k - min_k)/2;
            set(l2k, lower);
            set(u2k, upper);
            mul2k(l2k, mid_k);
            mul2k(u2k, mid_k);
            if (select_integer(l2k, u2k, aux))
                max_k = mid_k;
            else
                min_k = mid_k + 1;
            if (min_k == max_k) {
                if (max_k == mid_k) {
                    set(r, aux, max_k);
                }
                else {
                    set(l2k, lower);
                    set(u2k, upper);
                    mul2k(l2k, max_k);
                    mul2k(u2k, max_k);
                    VERIFY(select_integer(l2k, u2k, aux));
                    set(r, aux, max_k);
                }
                break;
            }
        }
    }
    SASSERT(le(lower, r));
    SASSERT(le(r, upper));
}

bool mpbq_manager::select_small(mpbq const & lower, mpbq const & upper, mpbq & r) {
    if (gt(lower, upper))
        return false;
    select_small_core(lower, upper, r);
    return true;
}


void mpbq_manager::select_small_core(unsynch_mpq_manager & qm, mpq const & lower, mpbq const & upper, mpbq & r) {
    TRACE("select_small", tout << "lower (q): " << qm.to_string(lower) << ", upper (bq): " << to_string(upper) << "\n";);
    SASSERT(gt(upper, lower));
    mpz & aux = m_select_small_tmp;
    if (select_integer(qm, lower, upper, aux)) {
        set(r, aux);
        return;
    }

    // At this point we know that k=0 does not work, since there is no integer 
    // in the interval [lower, upper]
    unsigned k = 0;
    scoped_mpq l2k(qm);
    mpq two(2);
    mpbq & u2k = m_select_small_tmp2;
    qm.set(l2k, lower);
    set(u2k, upper);
    while (true) {
        k++;
        qm.mul(l2k, two, l2k);
        mul2(u2k);
        if (select_integer(qm, l2k, u2k, aux)) {
            set(r, aux, k);
            break;
        }
    }
}

void mpbq_manager::select_small_core(unsynch_mpq_manager & qm, mpbq const & lower, mpq const & upper, mpbq & r) {
    SASSERT(lt(lower, upper));
    mpz & aux = m_select_small_tmp;
    if (select_integer(qm, lower, upper, aux)) {
        set(r, aux);
        return;
    }

    // At this point we know that k=0 does not work, since there is no integer 
    // in the interval [lower, upper]
    unsigned k = 0;
    mpbq & l2k = m_select_small_tmp2;
    scoped_mpq u2k(qm);
    mpq two(2);
    set(l2k, lower);
    qm.set(u2k, upper);
    while (true) {
        k++;
        mul2(l2k);
        qm.mul(u2k, two, u2k);
        if (select_integer(qm, l2k, u2k, aux)) {
            set(r, aux, k);
            break;
        }
    }
}

void mpbq_manager::select_small_core(unsynch_mpq_manager & qm, mpq const & lower, mpq const & upper, mpbq & r) {
    SASSERT(qm.lt(lower, upper));
    mpz & aux = m_select_small_tmp;
    if (select_integer(qm, lower, upper, aux)) {
        set(r, aux);
        return;
    }

    // At this point we know that k=0 does not work, since there is no integer 
    // in the interval [lower, upper]
    unsigned k = 0;
    scoped_mpq l2k(qm);
    scoped_mpq u2k(qm);
    mpq two(2);
    qm.set(l2k, lower);
    qm.set(u2k, upper);
    while (true) {
        k++;
        qm.mul(l2k, two, l2k);
        qm.mul(u2k, two, u2k);
        if (select_integer(qm, l2k, u2k, aux)) {
            set(r, aux, k);
            break;
        }
    }
}

void mpbq_manager::approx(mpbq & a, unsigned k, bool to_plus_inf) {
    if (a.m_k <= k)
        return;
#ifdef MPBQ_DEBUG
    scoped_mpbq old_a(*this);
    old_a = a;
#endif
    bool sgn  = m_manager.is_neg(a.m_num);
    bool _inc = (sgn != to_plus_inf);
    unsigned shift = a.m_k - k;
    m_manager.abs(a.m_num);
    m_manager.machine_div2k(a.m_num, shift);
    if (_inc)
        m_manager.inc(a.m_num);
    if (sgn)
        m_manager.neg(a.m_num);
    a.m_k = k;
    normalize(a);
#ifdef MPBQ_DEBUG
    if (to_plus_inf) {
        SASSERT(lt(old_a, a));
    }
    else {
        SASSERT(lt(a, old_a));
    }
#endif
}

void mpbq_manager::approx_div(mpbq const & a, mpbq const & b, mpbq & c, unsigned k, bool to_plus_inf) {
    SASSERT(!is_zero(b));
    unsigned k_prime;
    if (m_manager.is_power_of_two(b.m_num, k_prime)) {
        // The division is precise, so we ignore k and to_plus_inf
        SASSERT(b.m_k == 0 || k_prime == 0); // remark: b.m_num is odd when b.m_k > 0, since b.m_num is a power of two we have that b.m_k == 0 or b.m_num == 1.
        m_manager.set(c.m_num, a.m_num);
        if (b.m_k > 0) {
            SASSERT(k_prime == 0);
            mpz & pw2 = m_div_tmp1;
            m_manager.power(mpz(2), b.m_k, pw2);
            m_manager.mul(c.m_num, pw2, c.m_num);
        }
        c.m_k = a.m_k + k_prime;
        normalize(c);
    }
    else if (m_manager.divides(b.m_num, a.m_num)) {
        // result is also precise
        m_manager.div(a.m_num, b.m_num, c.m_num);
        if (a.m_k >= b.m_k) {
            c.m_k = a.m_k - b.m_k;
        }
        else {
            m_manager.mul2k(c.m_num, b.m_k - a.m_k);
            c.m_k = 0;
        }
        normalize(c);
    }
    else {
        bool sgn = is_neg(a) != is_neg(b);
        mpz & abs_a  = m_div_tmp1;
        mpz & norm_a = m_div_tmp2;
        mpz & abs_b  = m_div_tmp3;
        m_manager.set(abs_a, a.m_num);
        m_manager.abs(abs_a);
        m_manager.set(abs_b, b.m_num);
        m_manager.abs(abs_b);
        if (a.m_k > b.m_k) {
            if (k >= a.m_k - b.m_k)
                m_manager.mul2k(abs_a, k - (a.m_k - b.m_k), norm_a);
            else
                m_manager.machine_div2k(abs_a, (a.m_k - b.m_k) - k, norm_a);
        }
        else {
            m_manager.mul2k(abs_a, k + b.m_k - a.m_k, norm_a);
        }
        c.m_k = k;
        m_manager.div(norm_a, abs_b, c.m_num);
        if (sgn != to_plus_inf) 
            m_manager.inc(c.m_num);
        if (sgn)
            m_manager.neg(c.m_num);
        normalize(c);
    }
}
