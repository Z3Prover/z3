/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    mpq.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-06-21.

Revision History:

--*/
#include"mpq.h"
#include"warning.h"
#include"z3_exception.h"

template<bool SYNCH>
mpq_manager<SYNCH>::mpq_manager() {
}

template<bool SYNCH>
mpq_manager<SYNCH>::~mpq_manager() {
    del(m_n_tmp);
    del(m_add_tmp1);
    del(m_add_tmp2);
    del(m_lt_tmp1);
    del(m_lt_tmp2);
    del(m_addmul_tmp);
}


template<bool SYNCH>
bool mpq_manager<SYNCH>::rat_lt(mpq const & a, mpq const & b) {
    mpz const & na = a.numerator();
    mpz const & nb = b.numerator();
    int sign_a = this->sign(na);
    int sign_b = this->sign(nb);
    if (sign_a < 0) {
        if (sign_b >= 0) return true;
    }
    else if (sign_a == 0) {
        if (sign_b > 0)       return true;
        SASSERT(sign_b <= 0); return false;
    }
    else {
        SASSERT(sign_a > 0);
        if (sign_b <= 0) return false;
    }
    SASSERT((sign_a > 0 && sign_b > 0) ||
            (sign_a < 0 && sign_b < 0));
    mpz const & da = a.denominator();
    mpz const & db = b.denominator();

    if (SYNCH) {
        mpq tmp1;
        mpq tmp2;
        mul(na, db, tmp1);
        mul(nb, da, tmp2);
        bool r = lt(tmp1, tmp2);
        del(tmp1);
        del(tmp2);
        return r;
    }
    else {
        mul(na, db, m_lt_tmp1);
        mul(nb, da, m_lt_tmp2);
        return lt(m_lt_tmp1, m_lt_tmp2);
    }
}

template<bool SYNCH>
void mpq_manager<SYNCH>::floor(mpq const & a, mpz & f) {
    if (is_int(a)) {
        set(f, a.m_num);
        return;
    }
    bool is_neg_num = is_neg(a.m_num);
    machine_div(a.m_num, a.m_den, f);
    if (is_neg_num)
        sub(f, this->mk_z(1), f);
}

template<bool SYNCH>
void mpq_manager<SYNCH>::ceil(mpq const & a, mpz & c) {
    if (is_int(a)) {
        set(c, a.m_num);
        return;
    }
    bool is_pos_num = is_pos(a.m_num);
    machine_div(a.m_num, a.m_den, c);
    if (is_pos_num)
        add(c, this->mk_z(1), c);
}

template<bool SYNCH>
void mpq_manager<SYNCH>::gcd(unsigned sz, mpq const * as, mpq & g) {
    switch (sz) {
    case 0:
        reset(g);
        return;
    case 1:
        set(g, as[0]);
        abs(g);
        return;
    default:
        break;
    }
    gcd(as[0], as[1], g);
    for (unsigned i = 2; i < sz; i++) {
        if (is_one(g))
            return;
        gcd(g, as[i], g);
    }
}

template<bool SYNCH>
std::string mpq_manager<SYNCH>::to_string(mpq const & a) const {
    if (is_int(a))
        return to_string(a.m_num);
    return to_string(a.m_num) + "/" + to_string(a.m_den);
}

template<bool SYNCH>
void mpq_manager<SYNCH>::display(std::ostream & out, mpq const & a) const {
    if (is_int(a)) {
        display(out, a.m_num);
    }
    else {
        display(out, a.m_num);
        out << "/";
        display(out, a.m_den);
    }
}

template<bool SYNCH>
void mpq_manager<SYNCH>::display_smt2(std::ostream & out, mpq const & a, bool decimal) const {
    if (is_int(a)) {
        display_smt2(out, a.m_num, decimal);
    }
    else {
        out << "(/ ";
        display_smt2(out, a.m_num, decimal);
        out << " ";
        display_smt2(out, a.m_den, decimal);
        out << ")";
    }
}

template<bool SYNCH>
void mpq_manager<SYNCH>::display_decimal(std::ostream & out, mpq const & a, unsigned prec, bool truncate) {
    mpz n1, d1, v1;
    get_numerator(a, n1);
    get_denominator(a, d1);
    if (is_neg(a)) {
        out << "-";
        neg(n1);
    }
    mpz ten(10);
    div(n1, d1, v1);
    display(out, v1);
    rem(n1, d1, n1);
    if (is_zero(n1))
        goto end; // number is an integer
    out << ".";
    for (unsigned i = 0; i < prec; i++) {
        mul(n1, ten, n1);
        div(n1, d1, v1);
        SASSERT(lt(v1, ten));
        display(out, v1);
        rem(n1, d1, n1);
        if (is_zero(n1))
            goto end; // number is precise
    }
    if (!truncate) out << "?";
 end:
    del(ten); del(n1); del(d1); del(v1);
}

template<bool SYNCH>
void mpq_manager<SYNCH>::set(mpq & a, char const * val) {
    reset(a.m_num);
    mpz ten(10);
    _scoped_numeral<mpz_manager<SYNCH> > tmp(*this);
    char const * str = val;
    bool sign = false;
    while (str[0] == ' ') ++str;
    if (str[0] == '-') 
        sign = true;
    while (str[0] && (str[0] != '/') && (str[0] != '.') && (str[0] != 'e') && (str[0] != 'E')) {
        if ('0' <= str[0] && str[0] <= '9') {
            SASSERT(str[0] - '0' <= 9);
            mul(a.m_num, ten, tmp);
            add(tmp, this->mk_z(str[0] - '0'), a.m_num); 
        }
        ++str;
    }
    TRACE("mpq_set", tout << "[before] a: " << to_string(a) << "\n";);
    if (str[0] == '/' || str[0] == '.' || str[0] == 'e' || str[0] == 'E') {
        bool is_rat = str[0] == '/';
        _scoped_numeral<mpz_manager<SYNCH> > tmp2(*this);
        set(tmp2, 1);
        bool has_den = false;
        if (str[0] == '/' || str[0] == '.') {
            has_den  = true;
            ++str;
            reset(a.m_den);
            while (str[0] && (str[0] != 'e') && (str[0] != 'E')) {
                if ('0' <= str[0] && str[0] <= '9') {
                    mul(a.m_den, ten, tmp);
                    add(tmp, this->mk_z(str[0] - '0'), a.m_den); 
                    if (!is_rat) 
                        mul(tmp2, ten, tmp2);
                }
                ++str;
            }
        }
        unsigned long long exp = 0;
        bool exp_sign = false;
        if (str[0] == 'e' || str[0] == 'E') {
            if (is_rat)
                throw default_exception("mixing rational/scientific notation");
            ++str;
            if (str[0] == '-') {
                exp_sign = true;
                ++str;
            }
            while (str[0]) {
                if ('0' <= str[0] && str[0] <= '9') {
                    SASSERT(str[0] - '0' <= 9);
                    exp = (10*exp) + (str[0] - '0');
                }
                else if ('/' == str[0]) {
                    throw default_exception("mixing rational/scientific notation");
                }
                TRACE("mpq_set", tout << "[exp]: " << exp << ", str[0]: " << (str[0] - '0') << std::endl;);
                ++str;
            }
        }
        if (!is_rat) {
            // a <- a.m_num + a.m_den/tmp2
            if (exp > static_cast<unsigned long long>(UINT_MAX))
                throw default_exception("exponent is too big");
            _scoped_numeral<mpq_manager<SYNCH> > b(*this);
            if (has_den) {
                set(b, a.m_den, tmp2);
                set(a.m_den, 1);
                add(a, b, a);
            }
            if (exp > 0) {
                _scoped_numeral<mpq_manager<SYNCH> > _exp(*this);
                _scoped_numeral<mpq_manager<SYNCH> > _ten(*this);
                set(_ten, 10);
                power(_ten, static_cast<unsigned>(exp), _exp);
                TRACE("mpq_set", tout << "a: " << to_string(a) << ", exp_sign:" << exp_sign << ", exp: " << exp << " " << to_string(_exp) << std::endl;);
                if (exp_sign)
                    div(a, _exp, a);
                else
                    mul(a, _exp, a);
            }
        }
        else {
            // rational case
            if (is_zero(a.m_den))
                throw default_exception("division by zero");
        }
    }
    else {
        reset_denominator(a);
    }
    if (sign)
        neg(a.m_num);
    normalize(a);
}

template<bool SYNCH>
void mpq_manager<SYNCH>::power(mpq const & a, unsigned p, mpq & b) {
    unsigned mask = 1;
    mpq power;
    set(power, a);
    set(b, 1);
    while (mask <= p) {
        if (mask & p)
            mul(b, power, b);
        mul(power, power, power);
        mask = mask << 1;
    }
    del(power);
}

template<bool SYNCH>
double mpq_manager<SYNCH>::get_double(mpq const & a) const {
    double   n;
    double   d;
    n = get_double(a.m_num);
    d = get_double(a.m_den);
    SASSERT(d > 0.0);
    return n/d;
}

template<bool SYNCH>
bool mpq_manager<SYNCH>::root(mpq const & a, unsigned n, mpq & r) {
    return root(a.m_num, n, r.m_num) && root(a.m_den, n, r.m_den);
}

template<bool SYNCH>
unsigned mpq_manager<SYNCH>::prev_power_of_two(mpq const & a) { 
    _scoped_numeral<mpz_manager<SYNCH> > _tmp(*this);
    floor(a, _tmp);
    return prev_power_of_two(_tmp);
}

template class mpq_manager<true>;
template class mpq_manager<false>;

