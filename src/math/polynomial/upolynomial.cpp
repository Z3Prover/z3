/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    upolynomial.cpp

Abstract:

    Goodies for creating and handling univariate polynomials.

    A dense representation is much better for Root isolation algorithms,
    encoding algebraic numbers, factorization, etc.

    We also use integers as the coefficients of univariate polynomials.

Author:

    Leonardo (leonardo) 2011-11-29

Notes:

--*/
#include "math/polynomial/upolynomial.h"
#include "math/polynomial/upolynomial_factorization.h"
#include "math/polynomial/polynomial_primes.h"
#include "util/buffer.h"
#include "util/common_msgs.h"

namespace upolynomial {

    core_manager::factors::factors(core_manager & upm):
        m_upm(upm),
        m_total_factors(0),
        m_total_degree(0) {
        nm().set(m_constant, 1);
    }

    core_manager::factors::~factors() {
        clear();
        nm().del(m_constant);
    }

    void core_manager::factors::clear() {
        for (unsigned i = 0; i < m_factors.size(); ++ i) {
            m_upm.reset(m_factors[i]);
        }
        m_factors.reset();
        m_degrees.reset();
        nm().set(m_constant, 1);
        m_total_factors = 0;
        m_total_degree = 0;
    }

    void core_manager::factors::push_back(numeral_vector const & p, unsigned degree) {
        SASSERT(degree > 0);
        m_factors.push_back(numeral_vector());
        m_degrees.push_back(degree);
        m_upm.set(p.size(), p.c_ptr(), m_factors.back());
        m_total_factors += degree;
        m_total_degree += m_upm.degree(p)*degree;
    }

    void core_manager::factors::push_back_swap(numeral_vector & p, unsigned degree) {
        SASSERT(degree > 0);
        m_factors.push_back(numeral_vector());
        m_degrees.push_back(degree);
        p.swap(m_factors.back());
        m_total_factors += degree;
        m_total_degree += m_upm.degree(p)*degree;
    }

    void core_manager::factors::multiply(numeral_vector & out) const {
        // set the first one to be just the constant
        m_upm.reset(out);
        if (nm().is_zero(m_constant)) {
            SASSERT(m_factors.empty());
            return;
        }
        out.push_back(numeral());
        nm().set(out.back(), m_constant);

        // now multiply them all in
        for (unsigned i = 0; i < m_factors.size(); ++ i) {
            if (m_degrees[i] > 1) {
                numeral_vector power;
                m_upm.pw(m_factors[i].size(), m_factors[i].c_ptr(), m_degrees[i], power);
                m_upm.mul(out.size(), out.c_ptr(), power.size(), power.c_ptr(), out);
                m_upm.reset(power);
            } else {
                m_upm.mul(out.size(), out.c_ptr(), m_factors[i].size(), m_factors[i].c_ptr(), out);
            }
        }
    }

    void core_manager::factors::display(std::ostream & out) const {
        out << nm().to_string(m_constant);
        if (!m_factors.empty()) {
            for (unsigned i = 0; i < m_factors.size(); ++ i) {
                out << " * (";
                m_upm.display(out, m_factors[i]);
                out << ")^" << m_degrees[i];
            }
        }
    }

    numeral_manager & core_manager::factors::nm() const {
        return m_upm.m();
    }

    void core_manager::factors::set_constant(numeral const & constant) {
        nm().set(m_constant, constant);
    }

    void core_manager::factors::set_degree(unsigned i, unsigned degree) {
        m_total_degree -= m_upm.degree(m_factors[i])*m_degrees[i];
        m_total_factors -= m_degrees[i];
        m_degrees[i] = degree;
        m_total_factors += degree;
        m_total_degree += m_upm.degree(m_factors[i])*degree;
    }

    void core_manager::factors::swap_factor(unsigned i, numeral_vector & p) {
        m_total_degree -= m_upm.degree(m_factors[i])*m_degrees[i];
        m_total_degree += m_upm.degree(p)*m_degrees[i];
        m_factors[i].swap(p);
    }

    void core_manager::factors::swap(factors & other) {
        m_factors.swap(other.m_factors);
        m_degrees.swap(other.m_degrees);
        nm().swap(m_constant, other.m_constant);
        std::swap(m_total_factors, other.m_total_factors);
        std::swap(m_total_degree, other.m_total_degree);
    }

    core_manager::core_manager(reslimit& lim, unsynch_mpz_manager & m):
        m_limit(lim),
        m_manager(m) {
    }

    core_manager::~core_manager() {
        reset(m_basic_tmp);
        reset(m_div_tmp1);
        reset(m_div_tmp2);
        reset(m_exact_div_tmp);
        reset(m_gcd_tmp1);
        reset(m_gcd_tmp2);
        reset(m_CRA_tmp);
        for (unsigned i = 0; i < UPOLYNOMIAL_MGCD_TMPS; i++) reset(m_mgcd_tmp[i]);
        reset(m_sqf_tmp1);
        reset(m_sqf_tmp2);
        reset(m_pw_tmp);
    }

    void core_manager::checkpoint() {
        if (!m_limit.inc())
            throw upolynomial_exception(Z3_CANCELED_MSG);
    }

    // Eliminate leading zeros from buffer.
    void core_manager::trim(numeral_vector & buffer) {
        unsigned sz = buffer.size();
        while (sz > 0 && m().is_zero(buffer[sz - 1])) {
            m().del(buffer[sz - 1]); // 0 may be a big number when using GMP.
            sz--;
        }
        buffer.shrink(sz);
    }

    // Remove old entries from buffer [sz, buffer.size()), shrink size, and remove leading zeros.
    // buffer must have at least size sz.
    void core_manager::set_size(unsigned sz, numeral_vector & buffer) {
        unsigned old_sz = buffer.size();
        SASSERT(old_sz >= sz);
        // delete old entries
        for (unsigned i = sz; i < old_sz; i++) {
            m().del(buffer[i]);
        }
        buffer.shrink(sz);
        trim(buffer);
    }

    // Set size to zero.
    void core_manager::reset(numeral_vector & buffer) {
        set_size(0, buffer);
    }

    // Copy elements from p to buffer.
    void core_manager::set(unsigned sz, numeral const * p, numeral_vector & buffer) {
        if (p != nullptr && buffer.c_ptr() == p) {
            SASSERT(buffer.size() == sz);
            return;
        }
        buffer.reserve(sz);
        for (unsigned i = 0; i < sz; i++) {
            m().set(buffer[i], p[i]);
        }
        set_size(sz, buffer);
    }

    void core_manager::set(unsigned sz, rational const * p, numeral_vector & buffer) {
        buffer.reserve(sz);
        for (unsigned i = 0; i < sz; i++) {
            SASSERT(p[i].is_int());
            m().set(buffer[i], p[i].to_mpq().numerator());
        }
        set_size(sz, buffer);
    }

    void core_manager::get_primitive_and_content(unsigned f_sz, numeral const * f, numeral_vector & pp, numeral & cont) {
        SASSERT(f_sz > 0);
        m().gcd(f_sz, f, cont);
        SASSERT(m().is_pos(cont));
        if (m().is_one(cont)) {
            set(f_sz, f, pp);
        }
        else {
            pp.reserve(f_sz);
            for (unsigned i = 0; i < f_sz; i++) {
                if (!m().is_zero(f[i])) {
                    m().div(f[i], cont, pp[i]);
                }
                else {
                    m().set(pp[i], 0);
                }
            }
            set_size(f_sz, pp);
        }
    }

    // Negate coefficients of p.
    void core_manager::neg(unsigned sz, numeral * p) {
        for (unsigned i = 0; i < sz; i++) {
            m().neg(p[i]);
        }
    }

    // buffer := -p
    void core_manager::neg_core(unsigned sz, numeral const * p, numeral_vector & buffer) {
        SASSERT(!is_alias(p, buffer));
        buffer.reserve(sz);
        for (unsigned i = 0; i < sz; i++) {
            m().set(buffer[i], p[i]);
            m().neg(buffer[i]);
        }
        set_size(sz, buffer);
    }

    void core_manager::neg(unsigned sz, numeral const * p, numeral_vector & buffer) {
        neg_core(sz, p, m_basic_tmp);
        buffer.swap(m_basic_tmp);
    }

    // buffer := p1 + p2
    void core_manager::add_core(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer) {
        SASSERT(!is_alias(p1, buffer));
        SASSERT(!is_alias(p2, buffer));
        unsigned min_sz = std::min(sz1, sz2);
        unsigned max_sz = std::max(sz1, sz2);
        unsigned i = 0;
        buffer.reserve(max_sz);
        for (; i < min_sz; i++) {
            m().add(p1[i], p2[i], buffer[i]);
        }
        for (; i < sz1; i++) {
            m().set(buffer[i], p1[i]);
        }
        for (; i < sz2; i++) {
            m().set(buffer[i], p2[i]);
        }
        set_size(max_sz, buffer);
    }

    void core_manager::add(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer) {
        add_core(sz1, p1, sz2, p2, m_basic_tmp);
        buffer.swap(m_basic_tmp);
    }

    // buffer := p1 - p2
    void core_manager::sub_core(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer) {
        SASSERT(!is_alias(p1, buffer));
        SASSERT(!is_alias(p2, buffer));
        unsigned min_sz = std::min(sz1, sz2);
        unsigned max_sz = std::max(sz1, sz2);
        unsigned i = 0;
        buffer.reserve(max_sz);
        for (; i < min_sz; i++) {
            m().sub(p1[i], p2[i], buffer[i]);
        }
        for (; i < sz1; i++) {
            m().set(buffer[i], p1[i]);
        }
        for (; i < sz2; i++) {
            m().set(buffer[i], p2[i]);
            m().neg(buffer[i]);
        }

        set_size(max_sz, buffer);
    }

    void core_manager::sub(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer) {
        sub_core(sz1, p1, sz2, p2, m_basic_tmp);
        buffer.swap(m_basic_tmp);
    }

    // buffer := p1 * p2
    void core_manager::mul_core(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer) {
        SASSERT(!is_alias(p1, buffer));
        SASSERT(!is_alias(p2, buffer));
        if (sz1 == 0) {
            reset(buffer);
        }
        else if (sz2 == 0) {
            reset(buffer);
        }
        else {
            unsigned new_sz = sz1 + sz2 - 1;
            buffer.reserve(new_sz);
            for (unsigned i = 0; i < new_sz; i++) {
                m().reset(buffer[i]);
            }
            if (sz1 < sz2) {
                std::swap(sz1, sz2);
                std::swap(p1, p2);
            }
            for (unsigned i = 0; i < sz1; i++) {
                checkpoint();
                numeral const & a_i = p1[i];
                if (m().is_zero(a_i))
                    continue;
                for (unsigned j = 0; j < sz2; j++) {
                    numeral const & b_j = p2[j];
                    if (m().is_zero(b_j))
                        continue;
                    m().addmul(buffer[i+j], a_i, b_j, buffer[i+j]);
                }
            }
            set_size(new_sz, buffer);
        }
    }

    void core_manager::mul(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer) {
        mul_core(sz1, p1, sz2, p2, m_basic_tmp);
        buffer.swap(m_basic_tmp);
    }

    // buffer := dp/dx
    void core_manager::derivative(unsigned sz, numeral const * p, numeral_vector & buffer) {
        if (sz <= 1) {
            reset(buffer);
            return;
        }
        buffer.reserve(sz - 1);
        for (unsigned i = 1; i < sz; i++) {
            numeral d;
            m().set(d, i);
            m().mul(p[i], d, buffer[i-1]);
        }
        set_size(sz-1, buffer);
    }

    // Divide coefficients of p by their GCD
    void core_manager::normalize(unsigned sz, numeral * p) {
        if (sz == 0)
            return;
        if (sz == 1) {
            if (m().is_pos(p[0]))
                m().set(p[0], 1);
            else
                m().set(p[0], -1);
            return;
        }
        scoped_numeral g(m());
        m().gcd(sz, p, g);
        if (m().is_one(g))
            return;
        for (unsigned i = 0; i < sz; i++) {
#ifdef Z3DEBUG
            scoped_numeral old_p_i(m());
            old_p_i = p[i];
#endif
            // Actual code
            m().div(p[i], g, p[i]);

#ifdef Z3DEBUG
            scoped_numeral tmp(m());
            m().mul(g, p[i], tmp);
            CTRACE("div_bug", !m().eq(tmp, old_p_i), tout << "old(p[i]): " << m().to_string(old_p_i) << ", g: " << m().to_string(g) << ", p[i]: " <<
                   m().to_string(p[i]) << ", tmp: " << m().to_string(tmp) << "\n";);
            SASSERT(tmp == old_p_i);
#endif
        }
    }

    // Divide coefficients of p by their GCD
    void core_manager::normalize(numeral_vector & p) {
        normalize(p.size(), p.c_ptr());
    }

    void core_manager::div(unsigned sz, numeral * p, numeral const & b) {
        SASSERT(!m().is_zero(b));
        if (m().is_one(b))
            return;
        for (unsigned i = 0; i < sz; i++) {
            CTRACE("upolynomial", !m().divides(b, p[i]), tout << "b: " << m().to_string(b) << ", p[i]: " << m().to_string(p[i]) << "\n";);
            SASSERT(m().divides(b, p[i]));
            m().div(p[i], b, p[i]);
        }
    }

    void core_manager::mul(unsigned sz, numeral * p, numeral const & b) {
        SASSERT(!m().is_zero(b));
        if (m().is_one(b))
            return;
        for (unsigned i = 0; i < sz; i++) {
            m().mul(p[i], b, p[i]);
        }
    }

    void core_manager::mul(numeral_vector & p, numeral const & b) {
        if (m().is_zero(b)) {
            reset(p);
            return;
        }
        mul(p.size(), p.c_ptr(), b);
    }

    // Pseudo division
    void core_manager::div_rem_core(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2,
                                                     unsigned & d, numeral_vector & q, numeral_vector & r) {
        SASSERT(!is_alias(p1, q)); SASSERT(!is_alias(p2, q));
        SASSERT(!is_alias(p1, r)); SASSERT(!is_alias(p2, r));
        d = 0;
        SASSERT(sz2 > 0);
        if (sz2 == 1) {
            set(sz1, p1, q);
            if (field()) {
                div(q, *p2);
            }
            reset(r);
            return;
        }
        reset(q);
        set(sz1, p1, r);
        if (sz1 <= 1)
            return;
        unsigned qsz;
        if (sz1 >= sz2) {
            q.reserve(sz1 - sz2 + 1);
            qsz = sz1 - sz2 + 1;
        }
        else {
            qsz = 0;
        }
        numeral const & b_n = p2[sz2-1];
        SASSERT(!m().is_zero(b_n));
        scoped_numeral a_m(m());
        while (true) {
            checkpoint();
            sz1 = r.size();
            if (sz1 < sz2) {
                set_size(qsz, q);
                return;
            }
            unsigned m_n = sz1 - sz2; // m-n
            if (field()) {
                numeral & ratio = a_m;
                m().div(r[sz1 - 1], b_n, ratio);
                m().add(q[m_n], ratio, q[m_n]);
                for (unsigned i = 0; i < sz2 - 1; i++) {
                    m().submul(r[i + m_n], ratio, p2[i], r[i + m_n]);
                }
            }
            else {
                d++;
                m().set(a_m, r[sz1 - 1]);
                for (unsigned i = 0; i < sz1 - 1; i++) {
                    m().mul(r[i], b_n, r[i]);
                }
                for (unsigned i = 0; i < qsz; i++) {
                    m().mul(q[i], b_n, q[i]);
                }
                m().add(q[m_n], a_m, q[m_n]);
                for (unsigned i = 0; i < sz2 - 1; i++) {
                    m().submul(r[i + m_n], a_m, p2[i], r[i + m_n]);
                }
            }
            set_size(sz1 - 1, r);
        }
    }

    // Pseudo division
    void core_manager::div_rem(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, unsigned & d,
                                                numeral_vector & q, numeral_vector & r) {
        numeral_vector & _r = m_div_tmp1;
        numeral_vector & _q = m_div_tmp2;
        div_rem_core(sz1, p1, sz2, p2, d, _q, _r);
        r.swap(_r);
        q.swap(_q);
    }

    // Pseudo division
    void core_manager::div(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & q) {
        unsigned d;
        numeral_vector & _r = m_div_tmp1;
        numeral_vector & _q = m_div_tmp2;
        div_rem_core(sz1, p1, sz2, p2, d, _q, _r);
        reset(_r);
        q.swap(_q);
    }

    // Pseudo remainder
    void core_manager::rem(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, unsigned & d, numeral_vector & buffer) {
        SASSERT(!is_alias(p1, buffer)); SASSERT(!is_alias(p2, buffer));
        d = 0;
        SASSERT(sz2 > 0);
        if (sz2 == 1) {
            reset(buffer);
            return;
        }
        set(sz1, p1, buffer);
        if (sz1 <= 1)
            return;
		
        numeral const & b_n = p2[sz2-1];
        SASSERT(!m().is_zero(b_n));
        scoped_numeral a_m(m());
        while (m_limit.inc()) {			
            TRACE("rem_bug", tout << "rem loop, p2:\n"; display(tout, sz2, p2); tout << "\nbuffer:\n"; display(tout, buffer); tout << "\n";);
            sz1 = buffer.size();
            if (sz1 < sz2) {
                TRACE("rem_bug", tout << "finished\n";);
                return;
            }
            unsigned m_n = sz1 - sz2;
            if (field()) {
                numeral & ratio = a_m;
                m().div(buffer[sz1 - 1], b_n, ratio);
                for (unsigned i = 0; i < sz2 - 1; i++) {
                    m().submul(buffer[i + m_n], ratio, p2[i], buffer[i + m_n]);
                }
            }
            else {
                // buffer: a_m * x^m + a_{m-1} * x^{m-1} + ... + a_0
                // p2:     b_n * x^n + b_{n-1} * x^{n-1} + ... + b_0
                d++;
                m().set(a_m, buffer[sz1 - 1]);
                TRACE("rem_bug", tout << "a_m: " << m().to_string(a_m) << ", b_n: " << m().to_string(b_n) << "\n";);
                // don't need to update position sz1 - 1, since it will become 0
                for (unsigned i = 0; i < sz1 - 1; i++) {
                    m().mul(buffer[i], b_n, buffer[i]);
                }
                // buffer: a_m * x^m + b_n * a_{m-1} * x^{m-1} + ... + b_n * a_0
                // don't need to process i = sz2 - 1, because buffer[sz1 - 1] will become 0.
                for (unsigned i = 0; i < sz2 - 1; i++) {
                    m().submul(buffer[i + m_n], a_m, p2[i], buffer[i + m_n]);
                }
            }
            set_size(sz1 - 1, buffer);
        }
    }

    // Signed pseudo remainder
    void core_manager::srem(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer) {
        SASSERT(!is_alias(p1, buffer)); SASSERT(!is_alias(p2, buffer));
        unsigned d;
        rem(sz1, p1, sz2, p2, d, buffer);
        // We don't need to flip the sign if d is odd and leading coefficient of p2 is negative
        if (d % 2 == 0 || (sz2 > 0 && m().is_pos(p2[sz2-1])))
            neg(buffer.size(), buffer.c_ptr());
    }


    // Exact division for univariate polynomials.
    // Return false if p2 does not divide p1
    bool core_manager::divides(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2) {
        if (sz2 == 0)
            return false;
        if (sz1 == 0)
            return true;
        if (sz2 > sz1 || !m().divides(p2[sz2-1], p1[sz1-1]))
            return false;
        scoped_numeral b(m());
        numeral_vector & _p1 = m_div_tmp1;
        set(sz1, p1, _p1);
        while (true) {
            if (sz1 == 0)
                return true;
            if (sz2 > sz1 || !m().divides(p2[sz2-1], _p1[sz1-1]))
                return false;
            unsigned delta = sz1 - sz2;
            m().div(_p1[sz1-1], p2[sz2-1], b);
            for (unsigned i = 0; i < sz2 - 1; i++) {
                if (!m().is_zero(p2[i]))
                    m().submul(_p1[i+delta], b, p2[i], _p1[i+delta]);
            }
            m().reset(_p1[sz1-1]);
            trim(_p1);
            sz1 = _p1.size();
        }
        return true;
    }

    // Exact division for univariate polynomials.
    // Return false if p2 does not divide p1
    bool core_manager::exact_div(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & r) {
        if (sz2 == 0)
            return false;
        if (sz1 == 0) {
            reset(r);
            return true;
        }
        if (sz2 > sz1 || !m().divides(p2[sz2-1], p1[sz1-1]) || !m().divides(p2[0], p1[0]))
            return false;
        numeral_vector & _r = m_exact_div_tmp;
        reset(_r);
        unsigned deg = sz1 - sz2;
        _r.reserve(deg+1);
        numeral_vector & _p1 = m_div_tmp1;
        // std::cerr << "dividing with "; display(std::cerr, _p1); std::cerr << std::endl;
        TRACE("factor_bug", tout << "sz1: " << sz1 << " p1: " << p1 << ", _p1.c_ptr(): " << _p1.c_ptr() << ", _p1.size(): " << _p1.size() << "\n";);
        set(sz1, p1, _p1);
        SASSERT(_p1.size() == sz1);
        while (true) {
            TRACE("upolynomial", tout << "exact_div loop...\n"; display(tout, _p1); tout << "\n"; display(tout, _r); tout << "\n";);
            // std::cerr << "dividing with "; display(std::cerr, _p1); std::cerr << std::endl;
            if (sz1 == 0) {
                set_size(deg+1, _r);
                r.swap(_r);
                return true;
            }
            if (sz2 > sz1 || !m().divides(p2[sz2-1], _p1[sz1-1]) || !m().divides(p2[0], _p1[0])) {
                reset(r);
                return false;
            }
            unsigned delta = sz1 - sz2;
            numeral & a_r = _r[delta];
            m().div(_p1[sz1-1], p2[sz2-1], a_r);
            for (unsigned i = 0; i < sz2 - 1; i++) {
                if (!m().is_zero(p2[i]))
                    m().submul(_p1[i+delta], a_r, p2[i], _p1[i+delta]);
            }
            m().reset(_p1[sz1-1]);
            trim(_p1);
            sz1 = _p1.size();
        }
        return true;
    }

    void core_manager::flip_sign_if_lm_neg(numeral_vector & buffer) {
        unsigned sz = buffer.size();
        if (sz == 0)
            return;
        if (m().is_neg(buffer[sz - 1])) {
            for (unsigned i = 0; i < sz; i++)
                m().neg(buffer[i]);
        }
    }

    void core_manager::CRA_combine_images(numeral_vector const & C1, numeral const & b1, numeral_vector & C2, numeral & b2) {
        SASSERT(!m().m().is_even(b1));
        SASSERT(!m().m().is_even(b2));
        numeral_vector & R = m_CRA_tmp; reset(R);
        scoped_numeral inv1(m());
        scoped_numeral inv2(m());
        scoped_numeral g(m());
        m().gcd(b1, b2, inv1, inv2, g);
        SASSERT(m().is_one(g));
        // b1*inv1 + b2.inv2 = 1
        // inv1 is the inverse of b1 mod b2
        // inv2 is the inverse of b2 mod b1
        m().m().mod(inv1, b2, inv1);
        m().m().mod(inv2, b1, inv2);
        TRACE("CRA", tout << "inv1: " << inv1 << ", inv2: " << inv2 << "\n";);
        scoped_numeral a1(m());
        scoped_numeral a2(m());
        m().mul(b2, inv2, a1); // a1 is the multiplicator for coefficients of C1
        m().mul(b1, inv1, a2); // a2 is the multiplicator for coefficients of C2
        TRACE("CRA", tout << "a1: " << a1 << ", a2: " << a2 << "\n";);
        // new bound
        scoped_numeral new_bound(m());
        m().mul(b1, b2, new_bound);
        scoped_numeral lower(m());
        scoped_numeral upper(m());
        scoped_numeral new_a(m()), tmp1(m()), tmp2(m()), tmp3(m());
        m().div(new_bound, 2, upper);
        m().set(lower, upper);
        m().neg(lower);
        TRACE("CRA", tout << "lower: " << lower << ", upper: " << upper << "\n";);

        #define ADD(A1, A2) {                           \
            m().mul(A1, a1, tmp1);                      \
            m().mul(A2, a2, tmp2);                      \
            m().add(tmp1, tmp2, tmp3);                  \
            m().m().mod(tmp3, new_bound, new_a);        \
            if (m().gt(new_a, upper))                   \
                m().sub(new_a, new_bound, new_a);       \
            R.push_back(numeral());                     \
            m().set(R.back(), new_a);                   \
        }

        numeral zero(0);
        unsigned i   = 0;
        unsigned sz1 = C1.size();
        unsigned sz2 = C2.size();
        unsigned sz  = std::min(sz1, sz2);
        for (; i < sz; i++) {
            ADD(C1[i], C2[i]);
        }
        for (; i < sz1; i++) {
            ADD(C1[i], zero);
        }
        for (; i < sz2; i++) {
            ADD(zero, C2[i]);
        }
        m().set(b2, new_bound);
        R.swap(C2);
    }

    void core_manager::mod_gcd(unsigned sz_u, numeral const * u,
                               unsigned sz_v, numeral const * v,
                               numeral_vector & result) {
        TRACE("mgcd", tout << "u: "; display_star(tout, sz_u, u); tout << "\nv: "; display_star(tout, sz_v, v); tout << "\n";);
        SASSERT(sz_u > 0 && sz_v > 0);
        SASSERT(!m().modular());
        scoped_numeral c_u(m()), c_v(m());
        numeral_vector & pp_u = m_mgcd_tmp[0];
        numeral_vector & pp_v = m_mgcd_tmp[1];
        get_primitive_and_content(sz_u, u, pp_u, c_u);
        get_primitive_and_content(sz_v, v, pp_v, c_v);
        scoped_numeral c_g(m());
        m().gcd(c_u, c_v, c_g);
        unsigned d_u = sz_u - 1;
        unsigned d_v = sz_v - 1;
        numeral const & lc_u = pp_u[d_u];
        numeral const & lc_v = pp_v[d_v];
        scoped_numeral lc_g(m());
        m().gcd(lc_u, lc_v, lc_g);
        scoped_numeral p(m());
        scoped_numeral bound(m());

        numeral_vector & u_Zp = m_mgcd_tmp[2];
        numeral_vector & v_Zp = m_mgcd_tmp[3];
        numeral_vector & q    = m_mgcd_tmp[4];
        numeral_vector & C    = m_mgcd_tmp[5];

        for (unsigned i = 0; i < NUM_BIG_PRIMES; i++) {
            m().set(p, polynomial::g_big_primes[i]);
            TRACE("mgcd", tout << "trying prime: " << p << "\n";);
            {
                scoped_set_zp setZp(*this, p);
                set(pp_u.size(), pp_u.c_ptr(), u_Zp);
                set(pp_v.size(), pp_v.c_ptr(), v_Zp);
                if (degree(u_Zp) < d_u) {
                    TRACE("mgcd", tout << "bad prime, leading coefficient vanished\n";);
                    continue; // bad prime
                }
                if (degree(v_Zp) < d_v) {
                    TRACE("mgcd", tout << "bad prime, leading coefficient vanished\n";);
                    continue; // bad prime
                }
                euclid_gcd(u_Zp.size(), u_Zp.c_ptr(), v_Zp.size(), v_Zp.c_ptr(), q);
                // normalize so that lc_g is leading coefficient of q
                mk_monic(q.size(), q.c_ptr());
                scoped_numeral c(m());
                m().set(c, lc_g);
                mul(q, c);
            }
            TRACE("mgcd", tout << "new q:\n"; display_star(tout, q); tout << "\n";);
            if (is_const(q)) {
                TRACE("mgcd", tout << "done, modular gcd is one\n";);
                reset(result);
                result.push_back(numeral());
                m().set(result.back(), c_g);
                return;
            }
            if (i == 0) {
                set(q.size(), q.c_ptr(), C);
                m().set(bound, p);
            }
            else if (q.size() < C.size() || m().m().is_even(p) || m().m().is_even(bound)) {
                // discard accumulated image, it was affected by unlucky primes
                TRACE("mgcd", tout << "discarding image\n";);
                set(q.size(), q.c_ptr(), C);
                m().set(bound, p);
            }
            else {
                CRA_combine_images(q, p, C, bound);
                TRACE("mgcd", tout << "new combined:\n"; display_star(tout, C); tout << "\n";);
            }
            numeral_vector & candidate = q;
            get_primitive(C, candidate);
            TRACE("mgcd", tout << "candidate:\n"; display_star(tout, candidate); tout << "\n";);
            SASSERT(candidate.size() > 0);
            numeral const & lc_candidate = candidate[candidate.size() - 1];
            if (m().divides(lc_candidate, lc_g) &&
                divides(pp_u, candidate) &&
                divides(pp_v, candidate)) {
                TRACE("mgcd", tout << "found GCD\n";);
                mul(candidate, c_g);
                flip_sign_if_lm_neg(candidate);
                candidate.swap(result);
                TRACE("mgcd", tout << "r: "; display_star(tout, result); tout << "\n";);
                return;
            }
        }
        // Oops, modular GCD failed, not enough primes
        // fallback to euclid_gcd
        euclid_gcd(sz_u, u, sz_v, v, result);
    }

    void core_manager::euclid_gcd(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer) {
        SASSERT(!is_alias(p1, buffer)); SASSERT(!is_alias(p2, buffer));
        if (sz1 == 0) {
            set(sz2, p2, buffer);
            flip_sign_if_lm_neg(buffer);
            return;
        }
        if (sz2 == 0) {
            set(sz1, p1, buffer);
            flip_sign_if_lm_neg(buffer);
            return;
        }
        bool is_field = field();
        numeral_vector & A = m_gcd_tmp1;
        numeral_vector & B = m_gcd_tmp2;
        numeral_vector & R = buffer;
        set(sz1, p1, A);
        set(sz2, p2, B);
        TRACE("upolynomial", tout << "sz1: " << sz1 << ", p1: " << p1 << ", sz2: " << sz2 << ", p2: " << p2 << "\nB.size(): " << B.size() <<
              ", B.c_ptr(): " << B.c_ptr() << "\n";);
        while (m_limit.inc()) {
            TRACE("upolynomial", tout << "A: "; display(tout, A); tout <<"\nB: "; display(tout, B); tout << "\n";);
            if (B.empty()) {
                normalize(A);
                buffer.swap(A);
                // to be consistent, if in a field, we make gcd monic
                if (is_field) {
                    mk_monic(buffer.size(), buffer.c_ptr());
                }
                else {
                    flip_sign_if_lm_neg(buffer);
                }
                TRACE("upolynomial", tout << "GCD\n"; display(tout, sz1, p1); tout << "\n"; display(tout, sz2, p2); tout << "\n--->\n";
                      display(tout, buffer); tout << "\n";);
                return;
            }
            rem(A.size(), A.c_ptr(), B.size(), B.c_ptr(), R);
            normalize(R);
            A.swap(B);
            B.swap(R);
        }
        throw upolynomial_exception(Z3_CANCELED_MSG);
    }

    void core_manager::gcd(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer) {
        SASSERT(!is_alias(p1, buffer)); SASSERT(!is_alias(p2, buffer));
        if (sz1 == 0) {
            set(sz2, p2, buffer);
            flip_sign_if_lm_neg(buffer);
            return;
        }
        if (sz2 == 0) {
            set(sz1, p1, buffer);
            flip_sign_if_lm_neg(buffer);
            return;
        }
        if (!modular())
            mod_gcd(sz1, p1, sz2, p2, buffer);
        else
            euclid_gcd(sz1, p1, sz2, p2, buffer);
    }

    void core_manager::subresultant_gcd(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer) {
        SASSERT(!is_alias(p1, buffer)); SASSERT(!is_alias(p2, buffer));
        if (sz1 == 0) {
            set(sz2, p2, buffer);
            flip_sign_if_lm_neg(buffer);
            return;
        }
        if (sz2 == 0) {
            set(sz1, p1, buffer);
            flip_sign_if_lm_neg(buffer);
            return;
        }
        numeral_vector & A = m_gcd_tmp1;
        numeral_vector & B = m_gcd_tmp2;
        numeral_vector & R = buffer;
        scoped_numeral g(m());
        scoped_numeral h(m());
        scoped_numeral aux(m());
        m().set(g, 1);
        m().set(h, 1);
        unsigned d;
        set(sz1, p1, A);
        set(sz2, p2, B);
        if (A.size() < B.size())
            A.swap(B);
        while (true) {
            SASSERT(A.size() >= B.size());
            TRACE("upolynomial", tout << "A: "; display(tout, A); tout <<"\nB: "; display(tout, B); tout << "\n";
                  tout << "g: " << m().to_string(g) << ", h: " << m().to_string(h) << "\n";);
            if (B.empty()) {
                normalize(A);
                buffer.swap(A);
                // to be consistent, if in a field, we make gcd monic
                if (field()) {
                    mk_monic(buffer.size(), buffer.c_ptr());
                }
                else {
                    flip_sign_if_lm_neg(buffer);
                }
                TRACE("upolynomial", tout << "subresultant GCD\n"; display(tout, sz1, p1); tout << "\n"; display(tout, sz2, p2); tout << "\n--->\n";
                      display(tout, buffer); tout << "\n";);
                return;
            }
            rem(A.size(), A.c_ptr(), B.size(), B.c_ptr(), d, R);
            unsigned pseudo_div_d = A.size() - B.size();
            if (d < pseudo_div_d + 1) {
                // I used a standard subresultant implementation.
                // TODO: investigate how to avoid the following adjustment.
                //
                // adjust R to make sure the following equation holds:
                //  l(B)^{deg(A) - deg(B) + 1) * A = Q * B + R
                m().power(B[B.size() - 1], pseudo_div_d + 1 - d, aux);
                mul(R, aux);
            }
            d = pseudo_div_d;
            TRACE("upolynomial", tout << "R: "; display(tout, R); tout << "\nd: " << d << "\n";);
            // aux <- g*h^d
            m().power(h, d, aux);
            m().mul(g, aux, aux);
            div(R, aux);
            A.swap(B);
            B.swap(R);
            // g <- l(A)
            m().set(g, A[A.size() - 1]);
            m().power(g, d, aux);
            // h <- h^{1-d} * g^d
            if (d == 0) {
                // h <- h^1 * g^0
                // do nothing
            }
            else if (d == 1) {
                // h <- h^0 * g^1
                m().set(h, g);
            }
            else {
                // h <- (g^d)/(h^{d-1})
                SASSERT(d > 1);
                d--;
                m().power(h, d, h);
                SASSERT(m().divides(h, aux));
                m().div(aux, h, h);
            }
        }
    }

    // buffer := square-free(p)
    void core_manager::square_free(unsigned sz, numeral const * p, numeral_vector & buffer) {
        SASSERT(!is_alias(p, buffer));
        if (sz <= 1) {
            set(sz, p, buffer);
            return;
        }
        numeral_vector & p_prime = m_sqf_tmp1;
        numeral_vector & g       = m_sqf_tmp2;
        derivative(sz, p, p_prime);
        gcd(sz, p, p_prime.size(), p_prime.c_ptr(), g);
        // subresultant_gcd(sz, p, p_prime.size(), p_prime.c_ptr(), g);
        if (g.size() <= 1) {
            set(sz, p, buffer);
        }
        else {
            div(sz, p, g.size(), g.c_ptr(), buffer);
            normalize(buffer);
        }
    }

    bool core_manager::is_square_free(unsigned sz, numeral const * p) {
        if (sz <= 1) {
            return true;
        }
        numeral_vector & p_prime = m_sqf_tmp1;
        numeral_vector & g       = m_sqf_tmp2;
        derivative(sz, p, p_prime);
        gcd(sz, p, p_prime.size(), p_prime.c_ptr(), g);
        return g.size() <= 1;
    }

    void core_manager::pw(unsigned sz, numeral const * p, unsigned k, numeral_vector & r) {
        if (k == 0) {
            SASSERT(sz != 0);
            r.reserve(1);
            m().set(r[0], 1);
            set_size(1, r);
            return;
        }

        if (k == 1 || sz == 0 || (sz == 1 && m().is_one(p[0]))) {
            set(sz, p, r);
            return;
        }

        numeral_vector & result = m_pw_tmp;
        set(sz, p, result);
        for (unsigned i = 1; i < k; i++)
            mul(m_pw_tmp.size(), m_pw_tmp.c_ptr(), sz, p, m_pw_tmp);
        r.swap(result);
#if 0
        unsigned mask  = 1;
        numeral_vector & p2 = m_pw_tmp;
        set(sz, p, p2);
        reset(r);
        r.push_back(numeral(1));
        while (mask <= k) {
            if (mask & k) {
                // r := r * p2
                mul(r.size(), r.c_ptr(), p2.size(), p2.c_ptr(), r);
            }
            mul(p2.size(), p2.c_ptr(), p2.size(), p2.c_ptr(), p2);
            mask = mask << 1;
        }
#endif
    }

    void core_manager::mk_monic(unsigned sz, numeral * p, numeral & lc, numeral & lc_inv) {
        m().set(lc, 1);
        m().set(lc_inv, 1);
        if (sz > 0 && !m().is_one(p[sz-1])) {
            int d = sz-1;
            m().swap(lc, p[d--]);
            m().set(lc_inv, lc);
            m().inv(lc_inv);
            for (; d >= 0; -- d) {
                m().mul(p[d], lc_inv, p[d]);

            }
        }
    }

    // Extended GCD
    void core_manager::ext_gcd(unsigned szA, numeral const * A, unsigned szB, numeral const * B,
                                                numeral_vector & U, numeral_vector & V, numeral_vector & D) {
        SASSERT(!is_alias(A, U)); SASSERT(!is_alias(A, V)); SASSERT(!is_alias(A, D));
        SASSERT(!is_alias(B, U)); SASSERT(!is_alias(B, V)); SASSERT(!is_alias(B, D));

        SASSERT(field());
        scoped_numeral_vector V1(m()), V3(m()), Q(m()), R(m()), T(m()), V1Q(m());

        // since we are in a field define gcd(A, B) to be monic
        // if AU + BV = D and D is not monic we make it monic, and then divide U and V by the same inverse

        // initialization
        // U <- 1
        reset(U); U.push_back(numeral()); m().set(U.back(), 1);
        // D <- A
        set(szA, A, D);
        mk_monic(szA, D.c_ptr());
        // V1 <- 0
        reset(V1);
        // V3 <- B
        set(szB, B, V3);

        while (true) {
            if (V3.empty()) {
                // V3 is the zero polynomial
                numeral_vector & AU   = V1;
                numeral_vector & D_AU = V3;
                // V <- (D - AU)/B
                mul(szA, A, U.size(), U.c_ptr(), AU);
                sub(D.size(), D.c_ptr(), AU.size(), AU.c_ptr(), D_AU);
                div(D_AU.size(), D_AU.c_ptr(), szB, B, V);
                DEBUG_CODE({
                    scoped_numeral_vector BV(m());
                    scoped_numeral_vector expected_D(m());
                    mul(szB, B, V.size(), V.c_ptr(), BV);
                    add(AU.size(), AU.c_ptr(), BV.size(), BV.c_ptr(), expected_D);
                    SASSERT(eq(expected_D, D));
                });
                // if D is not monic, make it monic
                scoped_numeral lc_inv(m()), lc(m());
                mk_monic(D.size(), D.c_ptr(), lc, lc_inv);
                mul(U, lc_inv);
                mul(V, lc_inv);
                return;
            }

            // D = QV3 + R
            div_rem(D.size(), D.c_ptr(), V3.size(), V3.c_ptr(), Q, R);

            // T <- U - V1Q
            mul(V1.size(), V1.c_ptr(), Q.size(), Q.c_ptr(), V1Q);
            sub(U.size(), U.c_ptr(), V1Q.size(), V1Q.c_ptr(), T);
            // U <- V1
            U.swap(V1);
            // D <- V3
            D.swap(V3);
            // V1 <- T
            V1.swap(T);
            // V3 <- R
            V3.swap(R);
        }
    }

    // Display p
    std::ostream& core_manager::display(std::ostream & out, unsigned sz, numeral const * p, char const * var_name, bool use_star) const {
        bool displayed = false;
        unsigned i = sz;
        scoped_numeral a(m());
        while (i > 0) {
            --i;
            if (!m().is_zero(p[i])) {
                m().set(a, p[i]);
                if (displayed) {
                    m().abs(a);
                    if (m().is_pos(p[i]))
                        out << " + ";
                    else
                        out << " - ";
                }
                displayed = true;
                if (i == 0) {
                    out << m().to_string(a);
                }
                else {
                    SASSERT(i > 0);
                    if (!m().is_one(a)) {
                        out << m().to_string(a);
                        if (use_star)
                            out << "*";
                        else
                            out << " ";
                    }
                    out << var_name;
                    if (i > 1)
                        out << "^" << i;
                }
            }
        }
        if (!displayed)
            out << "0";
        return out;
    }

    static void display_smt2_mumeral(std::ostream & out, numeral_manager & m, mpz const & n) {
        if (m.is_neg(n)) {
            out << "(- ";
            mpz abs_n;
            m.set(abs_n, n);
            m.neg(abs_n);
            m.display(out, abs_n);
            m.del(abs_n);
            out << ")";
        }
        else {
            m.display(out, n);
        }
    }

    static void display_smt2_monomial(std::ostream & out, numeral_manager & m, mpz const & n,
                                      unsigned k, char const * var_name) {
        if (k == 0) {
            display_smt2_mumeral(out, m, n);
        }
        else if (m.is_one(n)) {
            if (k == 1)
                out << var_name;
            else
                out << "(^ " << var_name << " " << k << ")";
        }
        else {
            out << "(* ";
            display_smt2_mumeral(out, m, n);
            out << " ";
            if (k == 1)
                out << var_name;
            else
                out << "(^ " << var_name << " " << k << ")";
            out << ")";
        }
    }

    // Display p as an s-expression
    std::ostream& core_manager::display_smt2(std::ostream & out, unsigned sz, numeral const * p, char const * var_name) const {
        if (sz == 0) {
            out << "0";
            return out;
        }

        if (sz == 1) {
            display_smt2_mumeral(out, m(), p[0]);
            return out;
        }

        unsigned non_zero_idx  = UINT_MAX;
        unsigned num_non_zeros = 0;
        for (unsigned i = 0; i < sz; i++) {
            if (m().is_zero(p[i]))
                continue;
            non_zero_idx = i;
            num_non_zeros ++;
        }

        if (num_non_zeros == 1) {
            SASSERT(non_zero_idx != UINT_MAX && non_zero_idx >= 1);
            display_smt2_monomial(out, m(), p[non_zero_idx], non_zero_idx, var_name);
        }

        out << "(+";
        unsigned i = sz;
        while (i > 0) {
            --i;
            if (!m().is_zero(p[i])) {
                out << " ";
                display_smt2_monomial(out, m(), p[i], i, var_name);
            }
        }
        return out << ")";
    }

    bool core_manager::eq(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2) {
        if (sz1 != sz2)
            return false;
        for (unsigned i = 0; i < sz1; i++) {
            if (!m().eq(p1[i], p2[i]))
                return false;
        }
        return true;
    }

    void upolynomial_sequence::push(unsigned sz, numeral * p) {
        m_begins.push_back(m_seq_coeffs.size());
        m_szs.push_back(sz);
        for (unsigned i = 0; i < sz; i++) {
            m_seq_coeffs.push_back(numeral());
            swap(m_seq_coeffs.back(), p[i]);
        }
    }

    void upolynomial_sequence::push(numeral_manager & m, unsigned sz, numeral const * p) {
        m_begins.push_back(m_seq_coeffs.size());
        m_szs.push_back(sz);
        for (unsigned i = 0; i < sz; i++) {
            m_seq_coeffs.push_back(numeral());
            m.set(m_seq_coeffs.back(), p[i]);
        }
    }

    scoped_numeral_vector::scoped_numeral_vector(manager & m):
        _scoped_numeral_vector<numeral_manager>(m.m()) {
    }

    scoped_upolynomial_sequence::~scoped_upolynomial_sequence() {
        m_manager.reset(*this);
    }

    manager::~manager() {
        reset(m_db_tmp);
        reset(m_dbab_tmp1);
        reset(m_dbab_tmp2);
        reset(m_tr_tmp);
        reset(m_push_tmp);
    }

    void manager::reset(upolynomial_sequence & seq) {
        reset(seq.m_seq_coeffs);
        seq.m_szs.reset();
        seq.m_begins.reset();
    }

    // Remove zero roots from p
    void manager::remove_zero_roots(unsigned sz, numeral const * p, numeral_vector & buffer) {
        SASSERT(sz > 0);
        if (!m().is_zero(p[0])) {
            // zero is not a root of p
            set(sz, p, buffer);
            return;
        }
        unsigned i = 0;
        while (true) {
            // p must not be the zero polynomial
            SASSERT(i < sz);
            if (!m().is_zero(p[i]))
                break;
            i++;
        }
        unsigned new_sz = sz - i;
        buffer.reserve(new_sz);
        for (unsigned j = 0; j < new_sz; j++) {
            m().set(buffer[j], p[j + i]);
        }
        set_size(new_sz, buffer);
    }

    // Evaluate the sign of p(1/2)
    bool manager::has_one_half_root(unsigned sz, numeral const * p) {
        // Actually, given b = c/2^k, we compute the sign of 2^n*p(1/2)
        // Original Horner Sequence
        //     ((a_n * 1/2 + a_{n-1})*1/2 + a_{n-2})*1/2 + a_{n-3} ...
        // Variation of the Horner Sequence for 2^n*p(1/2)
        //     a_n + a_{n-1}*2 + a_{n-2}*(2^2) + a_{n-3}*(2^3) ...
        if (sz == 0)
            return true;
        if (sz == 1)
            return false;
        unsigned k   = 1;
        scoped_numeral r(m());
        scoped_numeral ak(m());
        m().set(r, p[sz-1]);
        unsigned i = sz - 1;
        while (i > 0) {
            --i;
            numeral const & a = p[i];
            m().mul2k(a, k, ak);
            m().add(r, ak, r);
            k++;
        }
        return m().is_zero(r);
    }

    // Remove 1/2 root from p
    void manager::remove_one_half_root(unsigned sz, numeral const * p, numeral_vector & buffer) {
        SASSERT(has_one_half_root(sz, p));
        numeral two_x_1[2] = { numeral(-1), numeral(2) };
        div(sz, p, 2, two_x_1, buffer);
    }

    int manager::sign_of(numeral const & c) {
        if (m().is_zero(c))
            return 0;
        if (m().is_pos(c))
            return 1;
        else
            return -1;
    }

    // Return the number of sign changes in the coefficients of p
    unsigned manager::sign_changes(unsigned sz, numeral const * p) {
        unsigned r = 0;
        int prev_sign = 0;
        unsigned i = 0;
        for (; i < sz; i++) {
            int sign = sign_of(p[i]);
            if (sign == 0)
                continue;
            if (sign != prev_sign && prev_sign != 0)
                r++;
            prev_sign = sign;
        }
        return r;
    }


    // Return the descartes bound for (0, +oo)
    unsigned manager::descartes_bound(unsigned sz, numeral const * p) {
        return sign_changes(sz, p);
    }

    // Return the descartes bound for the number of roots in the interval (0, 1)
    unsigned manager::descartes_bound_0_1(unsigned sz, numeral const * p) {
        if (sz <= 1)
            return 0;
        numeral_vector & Q = m_db_tmp;
        set(sz, p, Q);
#if 0
        // slow version
        unsigned n = Q.size() - 1;
        unsigned i;
        for (unsigned i = 1; i <= n; i++) {
            for (unsigned k = i; k >= 1; k--) {
                m().add(Q[k], Q[k-1], Q[k]);
            }
        }
        return sign_changes(Q.size(), Q.c_ptr());
#endif
        int prev_sign     = 0;
        unsigned num_vars = 0;
        //   a0 a1     a2         a3
        //   a0 a0+a1  a0+a1+a2   a0+a1+a2+a3
        //   a0 2a0+a1 3a0+2a1+a2
        //   a0 3a0+a1
        //   a0
        for (unsigned i = 0; i < sz; i++) {
            checkpoint();
            unsigned k;
            for (k = 1; k < sz - i; k++) {
                m().add(Q[k], Q[k-1], Q[k]);
            }
            int sign = sign_of(Q[k-1]);
            if (sign == 0)
                continue;
            if (sign != prev_sign && prev_sign != 0) {
                num_vars++;
                if (num_vars > 1)
                    return num_vars;
            }
            prev_sign = sign;
        }
        return num_vars;
    }

    // Return the descartes bound for the number of roots in the interval (a, b)
    unsigned manager::descartes_bound_a_b(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq const & a, mpbq const & b) {
        if (bqm.is_nonneg(a)) {
            // Basic idea: apply descartes_bound_0_1 to p2(x) where
            //   p1(x) = p(x+a)
            //   p2(x) = p1((b-a)*x)
            TRACE("upolynomial", tout << "pos interval... " << bqm.to_string(a) << ", " << bqm.to_string(b) << "\n"; display(tout, sz, p); tout << "\n";);
            numeral_vector & p_aux = m_dbab_tmp1;
            translate_bq(sz, p, a, p_aux);
            TRACE("upolynomial", tout << "after translation\n"; display(tout, p_aux); tout << "\n";);
            scoped_mpbq b_a(bqm);
            bqm.sub(b, a, b_a);
            compose_p_b_x(p_aux.size(), p_aux.c_ptr(), b_a);
            TRACE("upolynomial", tout << "after composition: " << bqm.to_string(b_a) << "\n"; display(tout, p_aux); tout << "\n";);
            unsigned result = descartes_bound_0_1(p_aux.size(), p_aux.c_ptr());
            return result;
        }
        else if (bqm.is_nonpos(b)) {
            // Basic idea: apply descartes_bound_a_b to p(-x) with intervals (-b, -a)
            numeral_vector & p_aux = m_dbab_tmp2;
            set(sz, p, p_aux);
            p_minus_x(p_aux.size(), p_aux.c_ptr());
            scoped_mpbq mb(bqm);
            scoped_mpbq ma(bqm);
            bqm.set(mb, b); bqm.neg(mb);
            bqm.set(ma, a); bqm.neg(ma);
            unsigned result = descartes_bound_a_b(p_aux.size(), p_aux.c_ptr(), bqm, mb, ma);
            return result;
        }
        else if (!has_zero_roots(sz, p)) {
            mpbq zero(0);
            unsigned r1 = descartes_bound_a_b(sz, p, bqm, a, zero);
            if (r1 > 1)
                return r1; // if p has more than 1 root in (a, zero), then we don't even evaluate (zero, b)
            unsigned r2 = descartes_bound_a_b(sz, p, bqm, zero, b);
            if (r1 == 0)
                return r2;
            if (r2 == 0)
                return r1;
            return 2; // p has more than one root in (a, b)
        }
        else {
            // zero is a root of p
            mpbq zero(0);
            if (descartes_bound_a_b(sz, p, bqm, a, zero) > 0)
                return 2; // p has more than one root in (a, b)
            if (descartes_bound_a_b(sz, p, bqm, zero, b) > 0)
                return 2; // p has more than one root in (a, b)
            return 1; // zero is the only root in (a, b)
        }
    }

    // p(x) := p(x+1)
    void manager::translate(unsigned sz, numeral * p) {
        if (sz <= 1)
            return;
        unsigned n = sz - 1;
        for (unsigned i = 1; i <= n; i++) {
            checkpoint();
            for (unsigned k = n-i; k <= n-1; k++)
                m().add(p[k], p[k+1], p[k]);
        }
    }

    // p(x) := p(x+2^k)
    void manager::translate_k(unsigned sz, numeral * p, unsigned k) {
        if (sz <= 1)
            return;
        scoped_numeral aux(m());
        unsigned n = sz - 1;
        for (unsigned i = 1; i <= n; i++) {
            checkpoint();
            for (unsigned k = n-i; k <= n-1; k++) {
                m().mul2k(p[k+1], k, aux);
                m().add(p[k], aux, p[k]);
            }
        }
    }

    // p(x) := p(x+c)
    void manager::translate_z(unsigned sz, numeral * p, numeral const & c) {
        if (sz <= 1)
            return;
        unsigned n = sz - 1;
        for (unsigned i = 1; i <= n; i++) {
            checkpoint();
            for (unsigned k = n-i; k <= n-1; k++)
                m().addmul(p[k], c, p[k+1], p[k]);
        }
    }

    // Given b of the form c/(2^k)
    // p(x) := (2^k)^n * p(x + c/(2^k)) where b = c/2^k
    //
    // Given p: a_n * x^n + ... + a_0
    //
    //       buffer := a_n * (2^k * x + c)^n + a_{n-1} * 2^k * (2^k * x + c)^{n-1} + ... + a_1 * (2^k)^{n-1} * (2^k * x + c) + a_0 * (2^k)^n
    //
    // We perform the transformation in two steps:
    //       1)   a_n * x^n + a_{n-1} * 2^k * x^{n-1} + ... + a_1 * (2^k)^{n-1} + a_0 * (2^k)^n
    //            Let d_n, ..., d_0 be the coefficients after this step
    //            Then, we have
    //            d_n * x^n + ... + d_0
    //       2)   d_n * (2^k * x + c)^n + ... + d_0
    //            This step is like the translation with integers, but the coefficients must be adjusted by 2^k in each iteration.
    //
    //            That is, it is a special translation such as:
    //               a_n*(b*x + c)^n + a_{n-1}*(b*x + c)^{n-1} + ... + a_1*(b*x + c) + a_0
    //            This kind of translation can be computed by applying the following recurrence:
    //            To simplify the notation, we fix n = 4
    //            Moreover we use a_i[k] to represent the coefficient a_i at iteration k
    //               a_i[0] = a_i
    //
    //               a_4*(b*x + c)^4 + a_3*(b*x + c)^3 + a_2*(b*x + c)^2 + a_1*(b*x + c) + a_0
    //               -->
    //               a_4*b*x*(b*x + c)^3 + (a_3 + a_4*c)*(b*x + c)^3 + a_2*(b*x + c)^2 + a_1*(b*x + c) + a_0
    //               Thus a_4[1] = a_4[0]*b,  a_3[1] = a_3[0] + a_4[0]*c, a_2[1] = a_2[0], a_1[1] = a_1[0], a_0[1] = a_0[0]
    //
    //               a_4[1]*x*(b*x + c)^3 + a_3[1]*(b*x + c)^3 + a_2[1]*(b*x + c)^2 + a_1[1]*(b*x + c) + a_0[1]
    //               -->
    //               a_4[1]*b*x^2*(b*x + c)^2 + (a_3[1]*b + a_4[1]*c)*x*(b*x + c)^2 + (a_2[1] + a_3[1]*c)*(b*x + c)^2 + a_1[1]*(b*x + c) + a_0[1]
    //               Thus a_4[2] = a_4[1]*b,   a_3[2] = a_3[1]*b + a_4[1]*c,   a_2[2] = a_2[1] + a_3[1]*c,  a_1[2] = a_1[1], a_0[2] = a_0[1]
    //
    //               a_4[2]*x^2*(b*x + c)^2 + a_3[2]*x*(b*x + c)^2 + a_2[2]*(b*x + c)^2 + a_1[2]*(b*x + c) + a_0[2]
    //               -->
    //               a_4[2]*b*x^3*(b*x + c) + (a_3[2]*b + a_4[2]*c)*x^2*(b*x + c) + (a_2[2]*b + a_3[2]*c)*x*(b*x + c) + (a_1[2] + a_2[2]*c)*(b*x + c) + a_0[2]
    //               Thus  a_4[3] = a_4[2]*b,  a_3[3] = a_3[2]*b + a_4[2]*c, a_2[3] = a_2[2]*b + a_3[2]*c, a_1[3] = a_1[2] + a_2[2]*c, a_0[3] = a_1[3]
    //
    //               a_4[3]*x^3*(b*x + c) + a_3[3]*x^2*(b*x + c) + a_2[3]*x*(b*x + c) + a_1[3]*(b*x + c) + a_0[3]
    //               --->
    //               a_4[3]*b*x^4 + (a_3[3]*b + a_4[3]*c)*x^3 + (a_2[3]*b + a_3[3]*c)*x^2  + (a_1[3]*b + a_2[3]*c)*x + (a_0[3] + a_1[3]*c)
    //
    void manager::translate_bq(unsigned sz, numeral * p, mpbq const & b) {
        if (sz <= 1)
            return;
        // Step 1
        compose_2kn_p_x_div_2k(sz, p, b.k());
        TRACE("upolynomial", tout << "after compose 2kn_p_x_div_2k\n"; display(tout, sz, p); tout << "\n";);
        // Step 2
        numeral const & c = b.numerator();
        unsigned n = sz - 1;
        for (unsigned i = 1; i <= n; i++) {
            checkpoint();
            m().addmul(p[n - i], c, p[n - i + 1], p[n - i]);
            for (unsigned k = n - i + 1; k <= n - 1; k++) {
                m().mul2k(p[k], b.k());
                m().addmul(p[k], c, p[k + 1], p[k]);
            }
            m().mul2k(p[n], b.k());
        }
        TRACE("upolynomial", tout << "after special translation\n"; display(tout, sz, p); tout << "\n";);
    }

    // Similar to translate_bq but for rationals
    void manager::translate_q(unsigned sz, numeral * p, mpq const & b) {
        if (sz <= 1)
            return;
        // Step 1
        compose_an_p_x_div_a(sz, p, b.denominator());
        TRACE("upolynomial", tout << "after compose_an_p_x_div_a\n"; display(tout, sz, p); tout << "\n";);
        // Step 2
        numeral const & c = b.numerator();
        unsigned n = sz - 1;
        for (unsigned i = 1; i <= n; i++) {
            checkpoint();
            m().addmul(p[n - i], c, p[n - i + 1], p[n - i]);
            for (unsigned k = n - i + 1; k <= n - 1; k++) {
                m().mul(p[k], b.denominator(), p[k]);
                m().addmul(p[k], c, p[k + 1], p[k]);
            }
            m().mul(p[n], b.denominator(), p[n]);
        }
        TRACE("upolynomial", tout << "after special translation\n"; display(tout, sz, p); tout << "\n";);
    }

    // p(x) := 2^n*p(x/2) where n = sz-1
    void manager::compose_2n_p_x_div_2(unsigned sz, numeral * p) {
        if (sz <= 1)
            return;
        // a_n * x^n + 2 * a_{n-1} * x^{n-1} + ... + (2^n)*a_0
        unsigned k = sz-1; // k = n
        for (unsigned i = 0; i < sz - 1; i++) {
            m().mul2k(p[i], k);
            k--;
        }
    }

    // p(x) := p(-x)
    void manager::p_minus_x(unsigned sz, numeral * p) {
        for (unsigned i = 0; i < sz; i++) {
            if (m().is_zero(p[i]))
                continue;
            if (i % 2 == 0)
                continue;
            m().neg(p[i]);
        }
    }

    // p(x) := x^n * p(1/x)
    void manager::p_1_div_x(unsigned sz, numeral * p) {
        if (sz <= 1)
            return;
        unsigned i = 0;
        unsigned j = sz-1;
        SASSERT(j >= 1);
        while (true) {
            swap(p[i], p[j]);
            i++; j--;
            if (i >= j)
                break;
        }
    }

    // p(x) := p(2^k * x)
    void manager::compose_p_2k_x(unsigned sz, numeral * p, unsigned k) {
        // (2^k)^n*a_n*x^n + (2^k)^(n-1)*x^{n-1} + ... + a_0
        if (sz <= 1)
            return;
        unsigned k_i = k;
        for (unsigned i = 1; i < sz; i++) {
            m().mul2k(p[i], k_i);
            k_i += k;
        }
    }

    // p(x) := (2^k)^n * p(x/2^k)
    //
    // Let old(p) be of the form:
    //  a_n * x^n + a_{n-1}*x^{n-1} + ... + a_1 * x + a_0
    //
    // Then p is of the form:
    //  a_n * x^n + a_{n-1} * 2^k * x^{n-1} + a_{n-2} * (2^k)^2 * x^{n-2} + ... + a_0 * (2^k)^n
    void manager::compose_2kn_p_x_div_2k(unsigned sz, numeral * p, unsigned k) {
        if (sz <= 1)
            return;
        unsigned k_i = k*sz;
        for (unsigned i = 0; i < sz; i++) {
            k_i -= k;
            if (!m().is_zero(p[i]))
                m().mul2k(p[i], k_i);
        }
    }

    // p(x) := a^n * p(x/a)
    // See compose_2kn_p_x_div_2k
    void manager::compose_an_p_x_div_a(unsigned sz, numeral * p, numeral const & a) {
        if (sz <= 1)
            return;
        unsigned i = sz-1;
        scoped_numeral a_i(m());
        m().set(a_i, a);
        while (i > 0) {
            --i;
            if (!m().is_zero(p[i]))
                m().mul(p[i], a_i, p[i]);
            m().mul(a_i, a, a_i);
        }
    }

    // p(x) := p(b * x)
    void manager::compose_p_b_x(unsigned sz, numeral * p, numeral const & b) {
        if (sz <= 1)
            return;
        scoped_numeral b_i(m());
        m().set(b_i, b);
        for (unsigned i = 1; i < sz; i++) {
            if (!m().is_zero(p[i]))
                m().mul(p[i], b_i, p[i]);
            m().mul(b_i, b, b_i);
        }
    }

    // Let b be of the form c/(2^k), then this operation is equivalent to:
    // (2^k)^n*p(c*x/(2^k))
    //
    // Let old(p) be of the form:
    //  a_n * x^n + a_{n-1}*x^{n-1} + ... + a_1 * x + a_0
    //
    // Then p is of the form:
    //  a_n * c^n * x^n + a_{n-1} * c^{n-1} * 2^k * x^{n-1}  + ... +  a_1 * c * (2^k)^(n-1) * x +  a_0 * (2^k)^n
    void manager::compose_p_b_x(unsigned sz, numeral * p, mpbq const & b) {
        if (sz <= 1)
            return;
        unsigned k = b.k();
        numeral const & c = b.numerator();
        scoped_numeral c_i(m());
        m().set(c_i, 1);
        unsigned k_i = k*sz;
        for (unsigned i = 0; i < sz; i++) {
            k_i -= k;
            if (!m().is_zero(p[i])) {
                m().mul2k(p[i], k_i);
                m().mul(p[i], c_i, p[i]);
            }
            m().mul(c_i, c, c_i);
        }
        SASSERT(k_i == 0);
    }

    // Let q be of the form b/c, then this operation is equivalent to:
    // p(x) := c^n*p(b*x/c)
    //
    // If u is a root of old(p), then u*(c/b) is a root of new p.
    //
    // Let old(p) be of the form:
    //  a_n * x^n + a_{n-1}*x^{n-1} + ... + a_1 * x + a_0
    //
    // Then p is of the form:
    //  a_n * b^n * x^n + a_{n-1} * b^{n-1} * c * x^{n-1}  + ... +  a_1 * b * c^(n-1) * x +  a_0 * c^n
    void manager::compose_p_q_x(unsigned sz, numeral * p, mpq const & q) {
        if (sz <= 1)
            return;
        numeral const & b = q.numerator();
        numeral const & c = q.denominator();
        scoped_numeral bc(m());
        m().power(c, sz-1, bc);  // bc = b^n
        for (unsigned i = 0; i < sz; i++) {
            if (!m().is_zero(p[i]))
                m().mul(p[i], bc, p[i]);
            if (i < sz - 1) {
                // bc <- (bc/b)*c
                m().div(bc, c, bc);
                m().mul(bc, b, bc);
            }
        }
    }

    // Evaluate the sign of p(b)
    int manager::eval_sign_at(unsigned sz, numeral const * p, mpbq const & b) {
        // Actually, given b = c/2^k, we compute the sign of (2^k)^n*p(b)
        // Original Horner Sequence
        //     ((a_n * b + a_{n-1})*b + a_{n-2})*b + a_{n-3} ...
        // Variation of the Horner Sequence for (2^k)^n*p(b)
        //     ((a_n * c + a_{n-1}*2_k)*c + a_{n-2}*(2_k)^2)*c + a_{n-3}*(2_k)^3 ... + a_0*(2_k)^n
        if (sz == 0)
            return 0;
        if (sz == 1)
            return sign_of(p[0]);
        numeral const & c = b.numerator();
        unsigned k   = b.k();
        unsigned k_i = k;
        scoped_numeral r(m());
        scoped_numeral ak(m());
        m().set(r, p[sz-1]);
        unsigned i = sz-1;
        while (i > 0) {
            --i;
            numeral const & a = p[i];
            if (m().is_zero(a)) {
                m().mul(r, c, r);
            }
            else {
                m().mul2k(a, k_i, ak);
                m().addmul(ak, r, c, r);
            }
            k_i += k;
        }
        return sign_of(r);
    }

    // Evaluate the sign of p(b)
    int manager::eval_sign_at(unsigned sz, numeral const * p, mpq const & b) {
        // Actually, given b = c/d, we compute the sign of (d^n)*p(b)
        // Original Horner Sequence
        //     ((a_n * b + a_{n-1})*b + a_{n-2})*b + a_{n-3} ...
        // Variation of the Horner Sequence for (d^n)*p(b)
        //     ((a_n * c + a_{n-1}*d)*c + a_{n-2}*d^2)*c + a_{n-3}*d^3 ... + a_0*d^n
        if (sz == 0)
            return 0;
        if (sz == 1)
            return sign_of(p[0]);
        numeral const & c = b.numerator();
        numeral const & d = b.denominator();
        scoped_numeral d_i(m());
        m().set(d_i, d);
        scoped_numeral r(m());
        scoped_numeral ak(m());
        m().set(r, p[sz-1]);
        unsigned i = sz-1;
        while (i > 0) {
            --i;
            numeral const & a = p[i];
            if (m().is_zero(a)) {
                m().mul(r, c, r);
            }
            else {
                m().mul(a, d_i, ak);
                m().addmul(ak, r, c, r);
            }
            m().mul(d_i, d, d_i);
        }
        return sign_of(r);
    }

    // Evaluate the sign of p(b)
    int manager::eval_sign_at(unsigned sz, numeral const * p, mpz const & b) {
        // Using Horner Sequence
        //     ((a_n * b + a_{n-1})*b + a_{n-2})*b + a_{n-3} ...
        if (sz == 0)
            return 0;
        if (sz == 1)
            return sign_of(p[0]);
        scoped_numeral r(m());
        m().set(r, p[sz-1]);
        unsigned i = sz-1;
        while (i > 0) {
            --i;
            numeral const & a = p[i];
            if (m().is_zero(a))
                m().mul(r, b, r);
            else
                m().addmul(a, r, b, r);
        }
        return sign_of(r);
    }

    int manager::eval_sign_at_zero(unsigned sz, numeral const * p) {
        if (sz == 0)
            return 0;
        return sign_of(p[0]);
    }

    int manager::eval_sign_at_plus_inf(unsigned sz, numeral const * p) {
        if (sz == 0)
            return 0;
        return sign_of(p[sz-1]);
    }

    int manager::eval_sign_at_minus_inf(unsigned sz, numeral const * p) {
        if (sz == 0)
            return 0;
        unsigned degree = sz - 1;
        if (degree % 2 == 0)
            return sign_of(p[sz-1]);
        else
            return -sign_of(p[sz-1]);
    }

    template<manager::location loc>
    unsigned manager::sign_variations_at_core(upolynomial_sequence const & seq, mpbq const & b) {
        unsigned sz = seq.size();
        if (sz <= 1)
            return 0;
        unsigned r = 0;
        int sign, prev_sign;
        sign = 0;
        prev_sign = 0;
        unsigned i = 0;
        for (; i < sz; i++) {
            // find next nonzero
            unsigned psz      = seq.size(i);
            numeral const * p = seq.coeffs(i);
            switch (loc) {
            case PLUS_INF:
                sign = eval_sign_at_plus_inf(psz, p);
                break;
            case MINUS_INF:
                sign = eval_sign_at_minus_inf(psz, p);
                break;
            case ZERO:
                sign  = eval_sign_at_zero(psz, p);
                break;
            case MPBQ:
                sign = eval_sign_at(psz, p, b);
                break;
            default:
                UNREACHABLE();
                break;
            }
            if (sign == 0)
                continue;
            SASSERT(sign == 1 || sign == -1);
            // in the first iteration prev_sign == 0, then r is never incremented.
            if (sign != prev_sign && prev_sign != 0)
                r++;
            // move to the next
            prev_sign = sign;
        }
        return r;
    }

    unsigned manager::sign_variations_at_minus_inf(upolynomial_sequence const & seq) {
        mpbq dummy(0);
        return sign_variations_at_core<MINUS_INF>(seq, dummy);
    }

    unsigned manager::sign_variations_at_plus_inf(upolynomial_sequence const & seq) {
        mpbq dummy(0);
        return sign_variations_at_core<PLUS_INF>(seq, dummy);
    }

    unsigned manager::sign_variations_at_zero(upolynomial_sequence const & seq) {
        mpbq dummy(0);
        return sign_variations_at_core<ZERO>(seq, dummy);
    }

    unsigned manager::sign_variations_at(upolynomial_sequence const & seq, mpbq const & b) {
        return sign_variations_at_core<MPBQ>(seq, b);
    }

    void manager::root_upper_bound(unsigned sz, numeral const * p, numeral & r) {
        // Using Cauchy's Inequality
        // We have that any root u of p must satisfy
        //         |u| < (max(p) + min(p))/min(p)
        //         |u| < (max(p) + |a_n|)/|a_n|
        // where: max(p) is the maximum coefficient in absolute value.
        //        min(p) is the minimum (nonzero) coefficient in absolute value
        SASSERT(sz > 0);
        SASSERT(!m().is_zero(p[sz - 1]));
        bool init = false;
        scoped_numeral max(m());
        scoped_numeral min(m());
        scoped_numeral a_n(m());
        scoped_numeral r2(m());
        m().set(a_n, p[sz - 1]);
        m().abs(a_n);
        scoped_numeral c(m());
        for (unsigned i = 0; i < sz; i++) {
            if (m().is_zero(p[i]))
                continue;
            m().set(c, p[i]);
            m().abs(c);
            if (!init) {
                m().set(max, c);
                m().set(min, c);
                init = true;
                continue;
            }
            if (m().gt(c, max))
                m().set(max, c);
            if (m().lt(c, min))
                m().set(min, c);
        }
        // first bound
        m().add(min, max, r);
        m().div(r, min, r);
        m().add(r, numeral(1), r);
        // second bound
        m().add(a_n, max, r2);
        m().div(r2, a_n, r2);
        m().add(r2, numeral(1), r2);
        // use the best bound
        if (m().lt(r2, r))
            swap(r, r2);
        SASSERT(m().le(r, r2));
    }

    /**
       \brief Find positive root upper bound using Knuth's approach.

       Given p(x) = a_n * x^n + a_{n-1} * x^{n-1} + ... + a_0

       If a_n is positive,
       Let B = max({ (-a_{n-k}/a_n)^{1/k} |  1 <= k <= n,   a_{n-k} < 0 })
       Then, 2*B is a bound for the positive roots

       Similarly, if a_n is negative
       Let B = max({ (-a_{n-k}/a_n)^{1/k} |  1 <= k <= n,   a_{n-k} > 0 })
       Then, 2*B is a bound for the positive roots

       This procedure returns a k s.t.  2*B <= 2^k

       The procedure actually computes

          max of  log2(abs(a_{n-k})) + 1 - log2(abs(a_n))/k

       Proof Sketch:

       Let u > 0 be a root of p(x).
       If u <= B, then we are done. So, let us assume u > B

       Assume, a_n > 0 (the proof is similar for a_n < 0)

       Then:   a_n * u^n + a_{n-1} * u^{n-1} + ... + a0 = 0
               u^n = 1/a_n (-a_{n-1} * u^{n-1} - ... - a_0)
               Note that, if we remove the monomials s.t. a_i is positive, then
               we are increasing the value of (-a_{n-1} * u^{n-1} - ... - a_0).
               Thus,
               u^n <= 1/a_n(SUM_{a_i < 0, 0 <= i < n} (-a_i * u^i))
               Dividing by u_n which is positive, we get
               1   <= 1/a_n(SUM_{a_i < 0, 0 <= i < n} (-a_i * u^i))
               By replacing, i = n - k
               we have
               1   <= 1/a_n(SUM_{a_{n-k} < 0, n >= k > 0} (-a_{n-k} * u^{n-k})) = 1/a_n(SUM_{a_{n-k} < 0, 1 <= k <= n} (-a_i * u^{n-k})) < Sum_{1 <= k < +oo}(B/u)^k
               Since u > B, we have that Sum_{1 <= k < +oo}(B/u)^k = B/(u - B)
               Thus, we have
               1 < B/(u - B)
               and u < 2B
    */
    unsigned manager::knuth_positive_root_upper_bound(unsigned sz, numeral const * p) {
        if (sz == 0)
            return 0;
        unsigned max = 0;
        unsigned n = sz - 1;
        bool pos_a_n = m().is_pos(p[n]);
        unsigned log2_a_n = pos_a_n ? m().log2(p[n]) : m().mlog2(p[n]);
        for (unsigned k = 1; k <= n; k++) {
            numeral const & a_n_k = p[n - k];
            if (m().is_zero(a_n_k))
                continue;
            bool pos_a_n_k = m().is_pos(a_n_k);
            if (pos_a_n_k == pos_a_n)
                continue; // must have opposite signs
            unsigned log2_a_n_k = pos_a_n_k ? m().log2(a_n_k) : m().mlog2(a_n_k);
            if (log2_a_n > log2_a_n_k)
                continue;
            unsigned curr = log2_a_n_k + 1 - log2_a_n;
            if (curr % k == 0) {
                curr /= k;
            }
            else {
                curr /= k;
                curr ++;
            }
            if (curr > max)
                max = curr;
        }
        return max + 1;
    }

    /**
       It is essentially applying knuth_positive_root_upper_bound for p(-x)
    */
    unsigned manager::knuth_negative_root_upper_bound(unsigned sz, numeral const * p) {
        numeral * _p = const_cast<numeral *>(p);
        p_minus_x(sz, _p);
        unsigned r = knuth_positive_root_upper_bound(sz, _p);
        p_minus_x(sz, _p);
        return r;
    }

    /**
        Return a lower bound for the nonzero roots of p(x).
        Let k be the result of this procedure,
        Then for any nonzero root alpha of p(x), we have that
                   |alpha| > 1/2^k

        We essentially compute the upper bound for the roots of x^n*p(1/x) where n is the degree of p.
        Remark: alpha is a nonzero root of p(x) iff 1/alpha is a root of x^n*p(1/x).
        Thus, if 2^k is upper bound for the root of x^n*p(1/x). Then we have that
             -2^k < 1/alpha < 2^k
        and consequently
             alpha < -1/2^k   or  1/2^k < alpha

        /pre p is not the zero polynomial.
    */
    unsigned manager::nonzero_root_lower_bound(unsigned sz, numeral const * p) {
        SASSERT(sz > 0);
        // consume zeros
        unsigned i = 0;
        while (true) {
            SASSERT(i < sz);
            if (!m().is_zero(p[i]))
                break;
            i++;
        }
        SASSERT(i < sz);
        SASSERT(!m().is_zero(p[i]));
        unsigned nz_sz = sz - i;
        numeral const * nz_p = p + i;
        // nz_p does not have zero roots;
        numeral * _nz_p = const_cast<numeral *>(nz_p);
        // destructive update for quickly computing x^n*nz_p(1/x)
        std::reverse(_nz_p, _nz_p + nz_sz);
        unsigned k1 = knuth_positive_root_upper_bound(nz_sz, _nz_p);
        unsigned k2 = knuth_negative_root_upper_bound(nz_sz, _nz_p);
        // undo destructive update
        std::reverse(_nz_p, _nz_p + nz_sz);
        return std::max(k1, k2);
    }

    // Frames for implementing drs_isolate_0_1_roots.
    // The frames are used to avoid recursive calls and potential stack overflows.
    // Each frame has a polynomial associated with it. The polynomials
    // are stored in a separate stack.
    struct manager::drs_frame {
        unsigned    m_parent_idx; // position of the parent frame, UINT_MAX if it doesn't have a parent frame
        unsigned    m_size:30;    // size of the polynomial associated with this frame
        unsigned    m_first:1;    // first time visiting the frame?
        unsigned    m_left:1;     // true if the frame is the left child of the parent frame.
        drs_frame(unsigned pidx, unsigned sz, bool left):
            m_parent_idx(pidx),
            m_size(sz),
            m_first(true),
            m_left(left) {
        }
    };

    // Pop the top frame from the frame_stack, remove the coefficients of the polynomial associated with the top frame from p_stack.
    void manager::pop_top_frame(numeral_vector & p_stack, svector<drs_frame> & frame_stack) {
        SASSERT(!frame_stack.empty());
        unsigned sz = frame_stack.back().m_size;
        SASSERT(sz <= p_stack.size());
        for (unsigned i = 0; i < sz; i++) {
            m().del(p_stack.back());
            p_stack.pop_back();
        }
        frame_stack.pop_back();
    }

    // Auxiliary method for isolating the roots of p in the interval (0, 1).
    // The basic idea is to split the interval in: (0, 1/2) and (1/2, 1).
    // This is accomplished by analyzing the roots in the interval (0, 1) of the following polynomials.
    //   p1(x) := 2^n * p(x/2)   where n = sz-1
    //   p2(x) := p1(x+1)
    // We say p1(x) is the left child, and p2 the right child. The coefficients p1 and p2 are stored in p_stack.
    // A new frame is created for each child.
    void manager::push_child_frames(unsigned sz, numeral const * p, numeral_vector & p_stack, svector<drs_frame> & frame_stack) {
        // I don't really need the following test, because 0 - 1 == UINT_MAX
        unsigned parent_idx = frame_stack.empty() ? UINT_MAX : frame_stack.size() - 1;
        numeral_vector & p_aux = m_push_tmp;

        // Possible optimization: the coefficients of the parent frame are not needed anymore.
        // So, we could reuse/steal them.

        // left child
        set(sz, p, p_aux);
        compose_2n_p_x_div_2(p_aux.size(), p_aux.c_ptr());
        normalize(p_aux);
        for (unsigned i = 0; i < sz; i++) {
            p_stack.push_back(numeral());
            m().set(p_stack.back(), p_aux[i]);
        }
        frame_stack.push_back(drs_frame(parent_idx, sz, true));
        // right child
        translate(sz, p_stack.end() - sz, p_aux);
        normalize(p_aux);
        for (unsigned i = 0; i < sz; i++) {
            p_stack.push_back(numeral());
            swap(p_stack.back(), p_aux[i]);
        }
        frame_stack.push_back(drs_frame(parent_idx, sz, false));
    }

    // (0,1) is an isolating interval for the polynomial associated with the top frame.
    // Apply transformations for obtaining isolating interval for the original polynomial:
    // We use the following transformations:
    //    Left child:   (l, u) -> (l/2, u/2)
    //    Right child:  (l, u) -> ((l+1)/2, (u+1)/2)
    void manager::add_isolating_interval(svector<drs_frame> const & frame_stack, mpbq_manager & bqm, mpbq_vector & lowers, mpbq_vector & uppers) {
        mpbq l(0);
        mpbq u(1);
        unsigned idx = frame_stack.size() - 1;
        while (idx != UINT_MAX) {
            drs_frame const & fr = frame_stack[idx];
            TRACE("upolynomial",
                  tout << "normalizing...\n";
                  tout << "idx: " << idx << ", left: " << fr.m_left << ", l: " << bqm.to_string(l) << ", u: " << bqm.to_string(u) << "\n";);
            if (fr.m_left) {
                bqm.div2(l);
                bqm.div2(u);
            }
            else {
                bqm.add(l, mpz(1), l);
                bqm.add(u, mpz(1), u);
                bqm.div2(l);
                bqm.div2(u);
            }
            idx = fr.m_parent_idx;
        }
        TRACE("upolynomial", tout << "adding normalized interval (" << bqm.to_string(l) << ", " << bqm.to_string(u) << ")\n";);
        lowers.push_back(mpbq());
        uppers.push_back(mpbq());
        swap(lowers.back(), l);
        swap(uppers.back(), u);
    }

    // 1/2 is a root of the polynomial associated with the top frame.
    // Apply transformations for obtaining root of the original polynomial:
    // We use the following transformations:
    //    Left child:   u -> u/2
    //    Right child:  u -> (u+1)/2
    void manager::add_root(svector<drs_frame> const & frame_stack, mpbq_manager & bqm, mpbq_vector & roots) {
        mpbq u(1,1);
        unsigned idx = frame_stack.size() - 1;
        while (idx != UINT_MAX) {
            drs_frame const & fr = frame_stack[idx];
            if (fr.m_left) {
                bqm.div2(u);
            }
            else {
                bqm.add(u, mpz(1), u);
                bqm.div2(u);
            }
            idx = fr.m_parent_idx;
        }
        TRACE("upolynomial", tout << "adding normalized root: " << bqm.to_string(u) << "\n";);
        roots.push_back(mpbq());
        swap(roots.back(), u);
    }

    // Isolate roots in the interval (0, 1)
    void manager::drs_isolate_0_1_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers) {
        TRACE("upolynomial", tout << "isolating (0,1) roots of:\n"; display(tout, sz, p); tout << "\n";);
        unsigned k = descartes_bound_0_1(sz, p);
        // easy cases...
        if (k == 0) {
            TRACE("upolynomial", tout << "polynomial does not have any roots\n";);
            return;
        }
        if (k == 1) {
            TRACE("upolynomial", tout << "polynomial has one root in (0, 1)\n";);
            lowers.push_back(mpbq(0));
            uppers.push_back(mpbq(1));
            return;
        }
        TRACE("upolynomial", tout << "polynomial has more than one root in (0, 1), starting search...\n";);
        scoped_numeral_vector  q(m());
        scoped_numeral_vector  p_stack(m());
        svector<drs_frame> frame_stack;
        if (has_one_half_root(sz, p)) {
            TRACE("upolynomial", tout << "polynomial has a 1/2 root\n";);
            roots.push_back(mpbq(1, 1));
            remove_one_half_root(sz, p, q);
            push_child_frames(q.size(), q.c_ptr(), p_stack, frame_stack);
        }
        else {
            push_child_frames(sz, p, p_stack, frame_stack);
        }
        SASSERT(!frame_stack.empty());
        while (!frame_stack.empty()) {
            checkpoint();
            drs_frame & fr    = frame_stack.back();
            unsigned sz       = fr.m_size;
            SASSERT(sz <= p_stack.size());
            numeral const * p = p_stack.end() - sz;
            TRACE("upolynomial", tout << "processing frame #" << frame_stack.size() - 1 << "\n"
                  << "first: " << fr.m_first << ", left: " << fr.m_left << ", sz: " << fr.m_size << ", parent_idx: ";
                  if (fr.m_parent_idx == UINT_MAX) tout << "<null>"; else tout << fr.m_parent_idx;
                  tout << "\np: "; display(tout, sz, p); tout << "\n";);
            if (!fr.m_first) {
                pop_top_frame(p_stack, frame_stack);
                continue;
            }
            fr.m_first = false;
            unsigned k = descartes_bound_0_1(sz, p);
            if (k == 0) {
                TRACE("upolynomial", tout << "(0, 1) does not have roots\n";);
                pop_top_frame(p_stack, frame_stack);
                continue;
            }
            if (k == 1) {
                TRACE("upolynomial", tout << "(0, 1) is isolating interval\n";);
                add_isolating_interval(frame_stack, bqm, lowers, uppers);
                pop_top_frame(p_stack, frame_stack);
                continue;
            }
            TRACE("upolynomial", tout << "polynomial has more than one root in (0, 1) creating child frames...\n";);
            if (has_one_half_root(sz, p)) {
                TRACE("upolynomial", tout << "1/2 is a root\n";);
                add_root(frame_stack, bqm, roots);
                remove_one_half_root(sz, p, q);
                push_child_frames(q.size(), q.c_ptr(), p_stack, frame_stack);
            }
            else {
                push_child_frames(sz, p, p_stack, frame_stack);
            }
        }
    }

    // Foreach i in [starting_at, v.size())  v[i] := 2^k*v[i]
    static void adjust_pos(mpbq_manager & bqm, mpbq_vector & v, unsigned starting_at, unsigned k) {
        unsigned sz = v.size();
        for (unsigned i = starting_at; i < sz; i++)
            bqm.mul2k(v[i], k);
    }

    // Foreach i in [starting_at, v.size())  v[i] := -2^k*v[i]
    static void adjust_neg(mpbq_manager & bqm, mpbq_vector & v, unsigned starting_at, unsigned k) {
        unsigned sz = v.size();
        for (unsigned i = starting_at; i < sz; i++) {
            bqm.mul2k(v[i], k);
            bqm.neg(v[i]);
        }
    }

    static void swap_lowers_uppers(unsigned starting_at, mpbq_vector & lowers, mpbq_vector & uppers) {
        SASSERT(lowers.size() == uppers.size());
        unsigned sz = lowers.size();
        for (unsigned i = starting_at; i < sz; i++) {
            swap(lowers[i], uppers[i]);
        }
    }

    // Isolate roots in an interval (-2^neg_k, 2^pos_k) using an approach based on Descartes rule of signs.
    void manager::drs_isolate_roots(unsigned sz, numeral * p, unsigned neg_k, unsigned pos_k,
                                    mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers) {
        scoped_numeral_vector aux_p(m());
        set(sz, p, aux_p);
        pos_k = std::max(neg_k, pos_k);
        compose_p_2k_x(sz, aux_p.c_ptr(), pos_k);

        // p(x) := p(2^{pos_k} * x)
        // Since the desired positive roots of p(x) are in (0, 2^pos_k),
        TRACE("upolynomial", tout << "searching at (0, 1)\n";);
        unsigned old_roots_sz  = roots.size();
        unsigned old_lowers_sz = lowers.size();
        drs_isolate_0_1_roots(sz, aux_p.c_ptr(), bqm, roots, lowers, uppers);
        SASSERT(lowers.size() == uppers.size());
        adjust_pos(bqm, roots,  old_roots_sz,  pos_k);
        adjust_pos(bqm, lowers, old_lowers_sz, pos_k);
        adjust_pos(bqm, uppers, old_lowers_sz, pos_k);

        // Isolate roots in (-2^{neg_k}, 0)
        // p(x) := p(-x)
        p_minus_x(sz, p);
        compose_p_2k_x(sz, p, neg_k);
        TRACE("upolynomial", tout << "searching at (-1, 0) using:\n"; display(tout, sz, p); tout << "\n";);
        old_roots_sz  = roots.size();
        old_lowers_sz = lowers.size();
        drs_isolate_0_1_roots(sz, p, bqm, roots, lowers, uppers);
        SASSERT(lowers.size() == uppers.size());
        adjust_neg(bqm, roots,  old_roots_sz,  neg_k);
        adjust_neg(bqm, lowers, old_lowers_sz, neg_k);
        adjust_neg(bqm, uppers, old_lowers_sz, neg_k);
        swap_lowers_uppers(old_lowers_sz, lowers, uppers);
    }

    // Isolate roots using an approach based on Descartes rule of signs.
    void manager::drs_isolate_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers) {
        SASSERT(lowers.size() == uppers.size());
        SASSERT(!has_zero_roots(sz, p));

        scoped_numeral_vector p1(m());
        set(sz, p, p1);
        normalize(p1);

        TRACE("upolynomial",
              scoped_numeral U(m());
              root_upper_bound(p1.size(), p1.c_ptr(), U);
              unsigned U_k = m().log2(U) + 1;
              tout << "Cauchy     U: 2^" << U_k << "\n";
              tout << "Knuth  pos U: 2^" << knuth_positive_root_upper_bound(sz, p) << "\n";
              tout << "Knuth  neg U: 2^" << knuth_negative_root_upper_bound(sz, p) << "\n";);

#if 1
        unsigned pos_k = knuth_positive_root_upper_bound(sz, p);
        unsigned neg_k = knuth_negative_root_upper_bound(sz, p);
#else
        scoped_numeral U(m());
        root_upper_bound(p1.size(), p1.c_ptr(), U);
        std::cout << "U: " << U << "\n";
        unsigned pos_k = m().log2(U) + 1;
        unsigned neg_k = pos_k;
#endif
        drs_isolate_roots(p1.size(), p1.c_ptr(), neg_k, pos_k, bqm, roots, lowers, uppers);
    }

    // Frame for root isolation in sturm_isolate_roots.
    // It stores (lower, upper, num. sign variations at lower, num. sign variations at upper)
    struct ss_frame {
        mpbq     m_lower;
        mpbq     m_upper;
        unsigned m_lower_sv; // number of sign variations in the sturm sequence at the lower bound
        unsigned m_upper_sv; // number of sign variations in the sturm sequence at the upper bound
    };

    class ss_frame_stack : public svector<ss_frame> {
        mpbq_manager & m;
    public:
        ss_frame_stack(mpbq_manager & _m):m(_m) {}
        ~ss_frame_stack() {
            iterator it = begin();
            iterator e  = end();
            for (; it != e; ++it) {
                ss_frame & f = *it;
                m.del(f.m_lower);
                m.del(f.m_upper);
            }
        }
    };

    inline void pop_ss_frame(mpbq_manager & m, ss_frame_stack & s) {
        m.del(s.back().m_lower);
        m.del(s.back().m_upper);
        s.pop_back();
    }

    void ss_add_isolating_interval(mpbq_manager & m, mpbq const & lower, mpbq const & upper, mpbq_vector & lowers, mpbq_vector & uppers) {
        lowers.push_back(mpbq());
        uppers.push_back(mpbq());
        m.set(lowers.back(), lower);
        m.set(uppers.back(), upper);
    }

    // Isolate roots in an interval (-2^neg_k, 2^pos_k) using an approach based on Descartes rule of signs.
    void manager::sturm_isolate_roots_core(unsigned sz, numeral * p, unsigned neg_k, unsigned pos_k,
                                           mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers) {
        SASSERT(!has_zero_roots(sz, p));
        scoped_upolynomial_sequence seq(*this);
        scoped_mpbq mid(bqm);
        scoped_mpbq curr_lower(bqm);
        scoped_mpbq curr_upper(bqm);
        sturm_seq(sz, p, seq);
        ss_frame_stack s(bqm);
        TRACE("upolynomial", tout << "p: "; display(tout, sz, p); tout << "\nSturm seq:\n"; display(tout, seq); tout << "\n";);

        unsigned lower_sv = sign_variations_at_minus_inf(seq);
        unsigned zero_sv  = sign_variations_at_zero(seq);
        unsigned upper_sv = sign_variations_at_plus_inf(seq);
        if (upper_sv >= lower_sv)
            return; // no roots

        bqm.power(mpbq(2), neg_k, curr_lower);
        bqm.neg(curr_lower);
        bqm.power(mpbq(2), pos_k, curr_upper);

#define PUSH_SS_FRAME(LOWER_SV, UPPER_SV, LOWER, UPPER) {                                       \
            SASSERT(!bqm.eq(LOWER, UPPER));                                                     \
            if (LOWER_SV == UPPER_SV) {                                                         \
                                                                                                \
            }                                                                                   \
            else if (LOWER_SV == UPPER_SV + 1) {                                                \
                /* Sturm is for half-open intervals (a, b] */                                   \
                /* We must check if upper is the root */                                        \
                if (eval_sign_at(sz, p, UPPER) == 0) {                                          \
                    /* found precise root */                                                    \
                    roots.push_back(mpbq());                                                    \
                    bqm.set(roots.back(), UPPER);                                               \
                }                                                                               \
                else {                                                                          \
                    ss_add_isolating_interval(bqm, LOWER, UPPER, lowers, uppers);               \
                }                                                                               \
            }                                                                                   \
            else {                                                                              \
                s.push_back(ss_frame());                                                        \
                ss_frame & f = s.back();                                                        \
                bqm.set(f.m_lower, LOWER);                                                      \
                bqm.set(f.m_upper, UPPER);                                                      \
                f.m_lower_sv = LOWER_SV;                                                        \
                f.m_upper_sv = UPPER_SV;                                                        \
            }                                                                                   \
        } ((void) 0)

        mpbq zero(0);
        PUSH_SS_FRAME(lower_sv, zero_sv, curr_lower, zero);
        PUSH_SS_FRAME(zero_sv, upper_sv, zero, curr_upper);

        while (!s.empty()) {
            checkpoint();
            ss_frame & f = s.back();
            lower_sv = f.m_lower_sv;
            upper_sv = f.m_upper_sv;
            bqm.swap(curr_lower, f.m_lower);
            bqm.swap(curr_upper, f.m_upper);
            pop_ss_frame(bqm, s);
            SASSERT(lower_sv > upper_sv + 1);
            bqm.add(curr_lower, curr_upper, mid);
            bqm.div2(mid);
            TRACE("upolynomial",
                  tout << "depth: " << s.size() << "\n";
                  tout << "lower_sv: " << lower_sv << "\n";
                  tout << "upper_sv: " << upper_sv << "\n";
                  tout << "curr_lower: " << curr_lower << "\n";
                  tout << "curr_upper: " << curr_upper << "\n";
                  tout << "mid: " << mid << "\n";);
            unsigned mid_sv = sign_variations_at(seq, mid);
            PUSH_SS_FRAME(lower_sv, mid_sv, curr_lower, mid);
            PUSH_SS_FRAME(mid_sv, upper_sv, mid, curr_upper);
        }
    }

    void manager::sturm_isolate_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers) {
        SASSERT(lowers.size() == uppers.size());

        scoped_numeral_vector p1(m());
        set(sz, p, p1);
        normalize(p1);
#if 1
        unsigned pos_k = knuth_positive_root_upper_bound(sz, p);
        unsigned neg_k = knuth_negative_root_upper_bound(sz, p);
#else
        scoped_numeral U(m());
        root_upper_bound(p1.size(), p1.c_ptr(), U);
        unsigned pos_k = m().log2(U) + 1;
        unsigned neg_k = pos_k;
#endif
        sturm_isolate_roots_core(p1.size(), p1.c_ptr(), neg_k, pos_k, bqm, roots, lowers, uppers);
    }

    // Isolate roots of a square free polynomial that does not have zero roots
    void manager::sqf_nz_isolate_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers) {
        SASSERT(!has_zero_roots(sz, p));
        drs_isolate_roots(sz, p, bqm, roots, lowers, uppers);
        // sturm_isolate_roots(sz, p, bqm, roots, lowers, uppers);
    }

    void manager::sqf_isolate_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers) {
        bqm.reset(roots);
        bqm.reset(lowers);
        bqm.reset(uppers);
        if (has_zero_roots(sz, p)) {
            roots.push_back(mpbq(0));
            scoped_numeral_vector nz_p(m());
            remove_zero_roots(sz, p, nz_p);
            TRACE("upolynomial", tout << "after removing zero root:\n"; display(tout, nz_p); tout << "\n";);
            SASSERT(!has_zero_roots(nz_p.size(), nz_p.c_ptr()));
            sqf_nz_isolate_roots(nz_p.size(), nz_p.c_ptr(), bqm, roots, lowers, uppers);
        }
        else {
            sqf_nz_isolate_roots(sz, p, bqm, roots, lowers, uppers);
        }
    }

    void manager::isolate_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers) {
        SASSERT(sz > 0);
        TRACE("upolynomial", tout << "isolating roots of:\n"; display(tout, sz, p); tout << "\n";);
        scoped_numeral_vector sqf_p(m());
        square_free(sz, p, sqf_p);
        TRACE("upolynomial", tout << "square free part:\n"; display(tout, sqf_p); tout << "\n";);
        sqf_isolate_roots(sqf_p.size(), sqf_p.c_ptr(), bqm, roots, lowers, uppers);
    }

    // Keep expanding the Sturm sequence starting at seq
    void manager::sturm_seq_core(upolynomial_sequence & seq) {
        scoped_numeral_vector r(m());
        while (m_limit.inc()) {
            unsigned sz = seq.size();
            srem(seq.size(sz-2), seq.coeffs(sz-2), seq.size(sz-1), seq.coeffs(sz-1), r);
            if (is_zero(r))
                return;
            normalize(r);
            seq.push(r.size(), r.c_ptr());
        }
    }

    void manager::sturm_seq(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, upolynomial_sequence & seq) {
        reset(seq);
        seq.push(m(), sz1, p1);
        seq.push(m(), sz2, p2);
        sturm_seq_core(seq);
    }

    void manager::sturm_seq(unsigned sz, numeral const * p, upolynomial_sequence & seq) {
        reset(seq);
        scoped_numeral_vector p_prime(m());
        seq.push(m(), sz, p);
        derivative(sz, p, p_prime);
        seq.push(p_prime.size(), p_prime.c_ptr());
        sturm_seq_core(seq);
    }

    void manager::sturm_tarski_seq(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, upolynomial_sequence & seq) {
        reset(seq);
        scoped_numeral_vector p1p2(m());
        seq.push(m(), sz1, p1);
        derivative(sz1, p1, p1p2);
        mul(p1p2.size(), p1p2.c_ptr(), sz2, p2, p1p2);
        seq.push(p1p2.size(), p1p2.c_ptr());
        sturm_seq_core(seq);
    }

    void manager::fourier_seq(unsigned sz, numeral const * p, upolynomial_sequence & seq) {
        reset(seq);
        scoped_numeral_vector p_prime(m());
        seq.push(m(), sz, p);
        if (sz == 0)
            return;
        unsigned degree = sz - 1;
        for (unsigned i = 0; i < degree; i++) {
            unsigned sz = seq.size();
            derivative(seq.size(sz-1), seq.coeffs(sz-1), p_prime);
            normalize(p_prime);
            seq.push(p_prime.size(), p_prime.c_ptr());
        }
    }

    /**
       We say an interval (a, b) of a polynomial p is ISOLATING if p has only one root in the
       interval (a, b).

       We say an isolating interval (a, b) of a square free polynomial p is REFINABLE if
         sign(p(a)) = -sign(p(b))

       Not every isolating interval (a, b) of a square free polynomial p is refinable, because
       sign(p(a)) or sign(p(b)) may be zero.

       Refinable intervals of square free polynomials are useful, because we can increase precision
       ("squeeze" the interval) by just evaluating p at (a+b)/2

       This procedure converts an isolating interval of a square free polynomial p, into
       a refinable interval, or an actual root.

       The method returns TRUE if it produced a REFINABLE interval (a', b'). The new interval
       is stored in input variables a and b.

       The method returns FALSE if it found the root a' in the interval (a, b). The root is
       stored in the input variable a.

       \pre p MUST BE SQUARE FREE.

       \warning This method may loop if p is not square free or if (a,b) is not an isolating interval.
    */
    bool manager::isolating2refinable(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq & a, mpbq & b) {
        int sign_a = eval_sign_at(sz, p, a);
        int sign_b = eval_sign_at(sz, p, b);
        TRACE("upolynomial", tout << "sign_a: " << sign_a << ", sign_b: " << sign_b << "\n";);
        if (sign_a != 0 && sign_b != 0) {
            // CASE 1
            SASSERT(sign_a == -sign_b); // p is square free
            return true;
        }
        if (sign_a == 0 && sign_b != 0) {
            // CASE 2
            scoped_mpbq new_a(bqm);
            // new_a <- (a+b)/2
            bqm.add(a, b, new_a);
            bqm.div2(new_a);
            while (true) {
                TRACE("upolynomial", tout << "CASE 2, a: " << bqm.to_string(a) << ", b: " << bqm.to_string(b) << ", new_a: " << bqm.to_string(new_a) << "\n";);
                int sign_new_a = eval_sign_at(sz, p, new_a);
                if (sign_new_a != sign_b) {
                    swap(new_a, a);
                    SASSERT(sign_new_a == 0 ||  // found the actual root
                            sign_new_a == -sign_b); // found refinable interval
                    return sign_new_a != 0;
                }
                else {
                    SASSERT(sign_new_a == sign_b);
                    // b     <- new_a
                    // new_a <- (a+b)/2
                    swap(b, new_a);
                    bqm.add(b, a, new_a);
                    bqm.div2(new_a);
                }
            }
        }
        if (sign_a != 0 && sign_b == 0 ) {
            // CASE 3
            scoped_mpbq new_b(bqm);
            // new_b <- (a+b)/2
            bqm.add(a, b, new_b);
            bqm.div2(new_b);
            while (true) {
                TRACE("upolynomial", tout << "CASE 3, a: " << bqm.to_string(a) << ", b: " << bqm.to_string(b) << ", new_b: " << bqm.to_string(new_b) << "\n";);
                int sign_new_b = eval_sign_at(sz, p, new_b);
                if (sign_new_b != sign_a) {
                    SASSERT(sign_new_b == 0 ||      // found the actual root
                            sign_new_b == -sign_a); // found refinable interval
                    if (sign_new_b == 0)
                        swap(new_b, a); // store root in a
                    else
                        swap(new_b, b);
                    return sign_new_b != 0;
                }
                else {
                    SASSERT(sign_new_b == sign_a);
                    // a     <- new_b
                    // new_b <- (a+b)/2
                    swap(a, new_b);
                    bqm.add(b, a, new_b);
                    bqm.div2(new_b);
                }
            }
        }
        SASSERT(sign_a == 0 && sign_b == 0);
        // CASE 4
        // we do cases 3 and 4 in "parallel"
        mpbq & a1 = a;
        scoped_mpbq b1(bqm);
        scoped_mpbq a2(bqm);
        mpbq & b2 = b;
        scoped_mpbq new_a1(bqm);
        scoped_mpbq new_b2(bqm);
        // b1 <- (a+b)/2
        bqm.add(a, b, b1);
        bqm.div2(b1);
        // a2 <- (a+b)/2
        bqm.set(a2, b1);
        int sign_b1 = eval_sign_at(sz, p, b1);
        int sign_a2 = sign_b1;
        bool result;
        if (sign_b1 == 0) {
            // found root
            swap(b1, a);
            result = false;
            goto end;
        }

        // new_a1 <- (a1+b1)/2
        bqm.add(a1, b1, new_a1);
        bqm.div2(new_a1);
        // new_b2 <- (a2+b2)/2
        bqm.add(a2, b2, new_b2);
        bqm.div2(new_b2);

        while (true) {
            TRACE("upolynomial",
                  tout << "CASE 4\na1: " << bqm.to_string(a1) << ", b1: " << bqm.to_string(b1) << ", new_a1: " << bqm.to_string(new_a1) << "\n";
                  tout << "a2: " << bqm.to_string(a2) << ", b2: " << bqm.to_string(b2) << ", new_b2: " << bqm.to_string(new_b2) << "\n";);
            int sign_new_a1 = eval_sign_at(sz, p, new_a1);
            if (sign_new_a1 == 0) {
                // found root
                swap(new_a1, a);
                result = false;
                goto end;
            }
            if (sign_new_a1 == -sign_b1) {
                // found interval
                swap(new_a1, a);
                swap(b1, b);
                result = true;
                goto end;
            }

            int sign_new_b2 = eval_sign_at(sz, p, new_b2);
            if (sign_new_b2 == 0) {
                // found root
                swap(new_b2, a);
                result = false;
                goto end;
            }

            if (sign_new_b2 == -sign_a2) {
                // found interval
                swap(a2, a);
                swap(new_b2, b);
                result = true;
                goto end;
            }

            SASSERT(sign_new_a1 == sign_b1);
            // b1     <- new_a1
            // new_a1 <- (a1+b1)/2
            swap(b1, new_a1);
            bqm.add(b1, a1, new_a1);
            bqm.div2(new_a1);

            SASSERT(sign_new_b2 == sign_a2);
            // a2     <- new_b2
            // new_b2 <- (a2+b2)/2
            swap(a2, new_b2);
            bqm.add(b2, a2, new_b2);
            bqm.div2(new_b2);
        }

    end:
        return result;
    }

    /**
       Given a square-free polynomial p, and a refinable interval (a,b), then "squeeze" (a,b).
       That is, return a new interval (a',b') s.t. b' - a' = (b - a)/2
       See isolating2refinable for a definition of refinable interval.

       Return TRUE, if interval was squeezed, and new interval is stored in (a,b).
       Return FALSE, if the actual root was found, it is stored in a.

       The arguments sign_a and sign_b must contain the values returned by
       eval_sign_at(sz, p, a) and eval_sign_at(sz, p, b).
    */
    bool manager::refine_core(unsigned sz, numeral const * p, int sign_a, mpbq_manager & bqm, mpbq & a, mpbq & b) {
        SASSERT(sign_a == eval_sign_at(sz, p, a));
        int sign_b = -sign_a;
        (void)sign_b;
        SASSERT(sign_b == eval_sign_at(sz, p, b));
        SASSERT(sign_a == -sign_b);
        SASSERT(sign_a != 0 && sign_b != 0);
        scoped_mpbq mid(bqm);
        bqm.add(a, b, mid);
        bqm.div2(mid);
        int sign_mid = eval_sign_at(sz, p, mid);
        if (sign_mid == 0) {
            swap(mid, a);
            return false;
        }
        if (sign_mid == sign_a) {
            swap(mid, a);
            return true;
        }
        SASSERT(sign_mid == sign_b);
        swap(mid, b);
        return true;
    }

    // See refine_core
    bool manager::refine(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq & a, mpbq & b) {
        int sign_a = eval_sign_at(sz, p, a);
        SASSERT(sign_a != 0);
        return refine_core(sz, p, sign_a, bqm, a, b);
    }

    // Keeps reducing the interval until b - a < 1/2^k or a root is found.
    // See comments in refine_core above.
    //
    // Return TRUE, if interval was squeezed, and new interval is stored in (a,b).
    // Return FALSE, if the actual root was found, it is stored in a.
    bool manager::refine_core(unsigned sz, numeral const * p, int sign_a, mpbq_manager & bqm, mpbq & a, mpbq & b, unsigned prec_k) {
        SASSERT(sign_a != 0);
        SASSERT(sign_a  == eval_sign_at(sz, p, a));
        SASSERT(-sign_a == eval_sign_at(sz, p, b));
        scoped_mpbq w(bqm);
        while (true) {
            checkpoint();
            bqm.sub(b, a, w);
            if (bqm.lt_1div2k(w, prec_k)) {
                return true;
            }
            if (!refine_core(sz, p, sign_a, bqm, a, b)) {
                return false; // found root
            }
        }
    }

    bool manager::refine(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq & a, mpbq & b, unsigned prec_k) {
        int sign_a = eval_sign_at(sz, p, a);
        SASSERT(eval_sign_at(sz, p, b) == -sign_a);
        SASSERT(sign_a != 0);
        return refine_core(sz, p, sign_a, bqm, a, b, prec_k);
    }

    bool manager::convert_q2bq_interval(unsigned sz, numeral const * p, mpq const & a, mpq const & b, mpbq_manager & bqm, mpbq & c, mpbq & d) {
        int sign_a = eval_sign_at(sz, p, a);
        int sign_b = eval_sign_at(sz, p, b);
        SASSERT(sign_a != 0 && sign_b != 0);
        SASSERT(sign_a == -sign_b);
        bool found_d = false;
        TRACE("convert_bug",
              tout << "a: " << m().to_string(a.numerator()) << "/" << m().to_string(a.denominator()) << "\n";
              tout << "b: " << m().to_string(b.numerator()) << "/" << m().to_string(b.denominator()) << "\n";
              tout << "sign_a: " << sign_a << "\n";
              tout << "sign_b: " << sign_b << "\n";);
        scoped_mpbq lower(bqm), upper(bqm);
        if (bqm.to_mpbq(a, lower)) {
            TRACE("convert_bug", tout << "found c: " << lower << "\n";);
            // found c
            swap(c, lower);
            SASSERT(bqm.eq(c, a));
        }
        else {
            // lower = a.numerator()/2^(k+1) where k is log2(a)
            bqm.set(upper, lower);
            bqm.mul2(upper);
            if (m_manager.is_neg(a.numerator()))
                ::swap(lower, upper);
            TRACE("convert_bug",
                  tout << "a: "; m().display(tout, a.numerator()); tout << "/"; m().display(tout, a.denominator()); tout << "\n";
                  tout << "lower: "; bqm.display(tout, lower); tout << ", upper: "; bqm.display(tout, upper); tout << "\n";);
            SASSERT(bqm.lt(lower, a));
            SASSERT(bqm.gt(upper, a));
            while (bqm.ge(upper, b)) {
                bqm.refine_upper(a, lower, upper);
            }
            SASSERT(bqm.lt(upper, b));
            while (true) {
                int sign_upper = eval_sign_at(sz, p, upper);
                if (sign_upper == 0) {
                    // found root
                    bqm.swap(c, upper);
                    bqm.del(lower); bqm.del(upper);
                    return false;
                }
                else if (sign_upper == sign_a) {
                    // found c
                    bqm.swap(c, upper);
                    break;
                }
                else {
                    SASSERT(sign_upper == sign_b);
                    // found d
                    if (!found_d) {
                        found_d = true;
                        bqm.set(d, upper);
                    }
                }
                bqm.refine_upper(a, lower, upper);
            }
        }

        if (!found_d) {
            if (bqm.to_mpbq(b, lower)) {
                // found d
                swap(d, lower);
                SASSERT(bqm.eq(d, b));
            }
            else {
                // lower = b.numerator()/2^(k+1) where k is log2(b)
                bqm.set(upper, lower);
                bqm.mul2(upper);
                if (m_manager.is_neg(b.numerator()))
                    ::swap(lower, upper);
                SASSERT(bqm.gt(upper, b));
                SASSERT(bqm.lt(lower, b));
                while (bqm.le(lower, c)) {
                    bqm.refine_lower(b, lower, upper);
                }
                SASSERT(bqm.lt(c, lower));
                SASSERT(bqm.lt(lower, upper));
                SASSERT(bqm.lt(lower, b));
                while (true) {
                    int sign_lower = eval_sign_at(sz, p, lower);
                    if (sign_lower == 0) {
                        // found root
                        bqm.swap(c, lower);
                        bqm.del(lower); bqm.del(upper);
                        return false;
                    }
                    else if (sign_lower == sign_b) {
                        // found d
                        bqm.swap(d, lower);
                        break;
                    }
                    bqm.refine_lower(b, lower, upper);
                }
            }
        }
        SASSERT(bqm.lt(c, d));
        SASSERT(eval_sign_at(sz, p, c) == -eval_sign_at(sz, p, d));
        SASSERT(bqm.ge(c, a));
        SASSERT(bqm.le(d, b));
        return true;
    }

    bool manager::normalize_interval_core(unsigned sz, numeral const * p, int sign_a, mpbq_manager & m, mpbq & a, mpbq & b) {
        if (m.is_neg(a) && m.is_pos(b)) {
            // See bool manager::normalize_interval(unsigned sz, numeral const * p, mpbq_manager & m, mpbq const & a, mpbq const & b) {
            if (sign_a == INT_MIN) {
                sign_a = eval_sign_at(sz, p, a);
            }
            else {
                SASSERT(sign_a == eval_sign_at(sz, p, a));
            }
            int sign_b = -sign_a;
            (void) sign_b;
            SASSERT(sign_b == eval_sign_at(sz, p, b));
            SASSERT(sign_a != 0 && sign_b != 0);
            if (has_zero_roots(sz, p)) {
                return false; // zero is the root
            }
            int sign_zero = eval_sign_at_zero(sz, p);
            if (sign_a == sign_zero) {
                m.reset(a);
            }
            else {
                m.reset(b);
            }
            SASSERT(eval_sign_at(sz, p, a) == -eval_sign_at(sz, p, b));
        }
        return true;
    }

    bool manager::normalize_interval(unsigned sz, numeral const * p, mpbq_manager & m, mpbq & a, mpbq & b) {
        return normalize_interval_core(sz, p, INT_MIN, m, a, b);
    }

    unsigned manager::get_root_id(unsigned sz, numeral const * p, mpbq const & l) {
        scoped_upolynomial_sequence seq(*this);
        sturm_seq(sz, p, seq);
        unsigned s0 = sign_variations_at_minus_inf(seq);
        unsigned s1 = sign_variations_at(seq, l);
        SASSERT(s0 >= s1);
        return s0 - s1;
    }

    void manager::flip_sign(factors & r) {
        scoped_numeral new_c(m_manager);
        m_manager.set(new_c, r.get_constant());
        m_manager.neg(new_c);
        r.set_constant(new_c);
    }

    void manager::factor_2_sqf_pp(numeral_vector & p, factors & r, unsigned k) {
        SASSERT(p.size() == 3); // p has degree 2
        TRACE("factor", tout << "factor square free (degree == 2):\n"; display(tout, p); tout << "\n";);

        numeral const & a = p[2];
        numeral const & b = p[1];
        numeral const & c = p[0];
        TRACE("factor", tout << "a: " << m().to_string(a) << "\nb: " << m().to_string(b) << "\nc: " << m().to_string(c) << "\n";);
        // Create the discriminant: b^2 - 4*a*c
        scoped_numeral b2(m());
        scoped_numeral ac(m());
        scoped_numeral disc(m());
        m().power(b, 2, b2);
        m().mul(a, c, ac);
        m().addmul(b2, numeral(-4), ac, disc);
        // discriminant must be different from 0, since p is square free
        SASSERT(!m().is_zero(disc));
        scoped_numeral disc_sqrt(m());
        if (!m().is_perfect_square(disc, disc_sqrt)) {
            // p is irreducible
            r.push_back(p, k);
            return;
        }
        TRACE("factor", tout << "disc_sqrt: " << m().to_string(disc_sqrt) << "\n";);
        // p = cont*(2*a*x + b - disc_sqrt)*(2*a*x + b + disc_sqrt)
        scoped_numeral_vector f1(m());
        scoped_numeral_vector f2(m());
        f1.reserve(2); f2.reserve(2);
        m().sub(b, disc_sqrt, f1[0]);
        m().add(b, disc_sqrt, f2[0]);
        m().mul(a, numeral(2), f1[1]);
        m().mul(a, numeral(2), f2[1]);
        set_size(2, f1);
        set_size(2, f2);
        normalize(f1);
        normalize(f2);
        TRACE("factor", tout << "f1: "; display(tout, f1); tout << "\nf2: "; display(tout, f2); tout << "\n";);
        DEBUG_CODE({
            scoped_numeral_vector f1f2(m());
            mul(f1, f2, f1f2);
            SASSERT(eq(f1f2, p));
        });
        r.push_back(f1, k);
        r.push_back(f2, k);
    }

    bool manager::factor_sqf_pp(numeral_vector & p, factors & r, unsigned k, factor_params const & params) {
        unsigned sz = p.size();
        SASSERT(sz == 0 || m().is_pos(p[sz-1]));
        if (sz <= 2) {
            // linear or constant
            r.push_back(p, k);
            return true;
        }
        else if (sz == 3) {
            factor_2_sqf_pp(p, r, k);
            return true;
        }
        else {
            return factor_square_free(*this, p, r, k, params);
        }
    }

    void manager::flip_factor_sign_if_lm_neg(numeral_vector & p, factors & r, unsigned k) {
        unsigned sz = p.size();
        if (sz == 0)
            return;
        if (m().is_neg(p[sz - 1])) {
            for (unsigned i = 0; i < sz; i++)
                m().neg(p[i]);
            if (k % 2 == 1)
                flip_sign(r);
        }
    }

    bool manager::factor_core(unsigned sz, numeral const * p, factors & r, factor_params const & params) {
        if (sz == 0) {
            r.set_constant(numeral(0));
            return true;
        }
        if (sz == 1) {
            r.set_constant(p[0]);
            return true;
        }
        // extract content & primitive part
        scoped_numeral content(m());
        scoped_numeral_vector pp(m());
        get_primitive_and_content(sz, p, pp, content);
        r.set_constant(content);
        //
        scoped_numeral_vector & C = pp;
        // Let C be a primitive polynomial of the form: P_1^1 * P_2^2 * ... * P_k^k, where each P_i is square free
        scoped_numeral_vector C_prime(m());
        derivative(C, C_prime);
        scoped_numeral_vector A(m()), B(m()), D(m());
        gcd(C, C_prime, B);

        bool result = true;
        if (is_const(B)) {
            // C must be of the form P_1 (square free)
            SASSERT(!is_const(C));
            flip_factor_sign_if_lm_neg(C, r, 1);
            if (!factor_sqf_pp(C, r, 1, params))
                result = false;
        }
        else {
            // B is of the form P_2 * P_3^2 * ... * P_k^{k-1}
            VERIFY(exact_div(C, B, A));
            TRACE("factor_bug", tout << "C: "; display(tout, C); tout << "\nB: "; display(tout, B); tout << "\nA: "; display(tout, A); tout << "\n";);
            // A is of the form P_1 * P_2 * ... * P_k
            unsigned j = 1;
            while (!is_const(A)) {
                checkpoint();
                TRACE("factor", tout << "factor_core main loop j: " << j << "\nA: "; display(tout, A); tout << "\nB: "; display(tout, B); tout << "\n";);
                // A is of the form       P_j * P_{j+1} * P_{j+2}   * ... * P_k
                // B is of the form             P_{j+1} * P_{j+2}^2 * ... * P_k^{k - j - 2}
                gcd(A, B, D);
                // D is of the form             P_{j+1} * P_{j+2}   * ... * P_k
                VERIFY(exact_div(A, D, C));
                // C is of the form P_j
                if (!is_const(C)) {
                    flip_factor_sign_if_lm_neg(C, r, j);
                    if (!factor_sqf_pp(C, r, j, params))
                        result = false;
                }
                else {
                    TRACE("factor", tout << "const C: "; display(tout, C); tout << "\n";);
                    SASSERT(C.size() == 1);
                    SASSERT(m().is_one(C[0]) || m().is_minus_one(C[0]));
                    if (m().is_minus_one(C[0]) && j % 2 == 1)
                        flip_sign(r);
                }
                TRACE("factor_bug", tout << "B: "; display(tout, B); tout << "\nD: "; display(tout, D); tout << "\n";);
                VERIFY(exact_div(B, D, B));
                // B is of the form                       P_{j+2}   * ... * P_k^{k - j - 3}
                A.swap(D);
                // D is of the form             P_{j+1} * P_{j+2}   * ... * P_k
                j++;
            }
            TRACE("factor_bug", tout << "A: "; display(tout, A); tout << "\n";);
            SASSERT(A.size() == 1 && m().is_one(A[0]));
        }
        return result;
    }

    bool manager::factor(unsigned sz, numeral const * p, factors & r, factor_params const & params) {
        bool result = factor_core(sz, p, r, params);
#ifndef _EXTERNAL_RELEASE
        IF_VERBOSE(FACTOR_VERBOSE_LVL, verbose_stream() << "(polynomial-factorization :distinct-factors " << r.distinct_factors() << ")" << std::endl;);
#endif
        return result;
    }

    std::ostream& manager::display(std::ostream & out, upolynomial_sequence const & seq, char const * var_name) const {
        for (unsigned i = 0; i < seq.size(); i++) {
            display(out, seq.size(i), seq.coeffs(i), var_name);
            out << "\n";
        }
        return out;
    }
};

