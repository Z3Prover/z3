/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sexpr2upolynomial.cpp

Abstract:

    sexpr to upolynomial converter
    
Author:

    Leonardo (leonardo) 2011-12-28

Notes:

--*/
#include"sexpr2upolynomial.h"
#include"sexpr.h"

sexpr2upolynomial_exception::sexpr2upolynomial_exception(char const * msg, sexpr const * s):
    cmd_exception(msg, s->get_line(), s->get_pos()) {
}

#define MAX_POLYNOMIAL_DEPTH 1 << 16

// Simple recursive parser
void sexpr2upolynomial(upolynomial::manager & m, sexpr const * s, upolynomial::numeral_vector & p, unsigned depth) {
    if (depth > MAX_POLYNOMIAL_DEPTH)
        throw sexpr2upolynomial_exception("invalid univariate polynomial, too complex", s);
    if (s->is_composite()) {
        unsigned num = s->get_num_children();
        if (num == 0)
            throw sexpr2upolynomial_exception("invalid univariate polynomial, symbol expected", s);
        sexpr * h = s->get_child(0);
        if (!h->is_symbol())
            throw sexpr2upolynomial_exception("invalid univariate polynomial, symbol expected", s);
        symbol op = h->get_symbol();
        if (op == "+") {
            if (num <= 1)
                throw sexpr2upolynomial_exception("invalid univariate polynomial, '+' operator expects at least one argument", s);
            sexpr2upolynomial(m, s->get_child(1), p, depth+1);
            upolynomial::scoped_numeral_vector arg(m);
            for (unsigned i = 2; i < num; i++) {
                m.reset(arg);
                sexpr2upolynomial(m, s->get_child(i), arg, depth+1);
                m.add(arg.size(), arg.c_ptr(), p.size(), p.c_ptr(), p);
            }
        }
        else if (op == "-") {
            if (num <= 1)
                throw sexpr2upolynomial_exception("invalid univariate polynomial, '-' operator expects at least one argument", s);
            sexpr2upolynomial(m, s->get_child(1), p, depth+1);
            if (num == 2) {
                m.neg(p);
                return;
            }
            upolynomial::scoped_numeral_vector arg(m);
            for (unsigned i = 2; i < num; i++) {
                m.reset(arg);
                sexpr2upolynomial(m, s->get_child(i), arg, depth+1);
                m.sub(p.size(), p.c_ptr(), arg.size(), arg.c_ptr(), p);
            }
        }
        else if (op == "*") {
            if (num <= 1)
                throw sexpr2upolynomial_exception("invalid univariate polynomial, '*' operator expects at least one argument", s);
            sexpr2upolynomial(m, s->get_child(1), p, depth+1);
            upolynomial::scoped_numeral_vector arg(m);
            for (unsigned i = 2; i < num; i++) {
                m.reset(arg);
                sexpr2upolynomial(m, s->get_child(i), arg, depth+1);
                m.mul(arg.size(), arg.c_ptr(), p.size(), p.c_ptr(), p);
            }
        }
        else if (op == "^") {
            if (num != 3)
                throw sexpr2upolynomial_exception("invalid univariate polynomial, '^' operator expects two arguments", s);
            sexpr2upolynomial(m, s->get_child(1), p, depth+1);
            sexpr * arg2 = s->get_child(2);
            if (!arg2->is_numeral() || !arg2->get_numeral().is_unsigned())
                throw sexpr2upolynomial_exception("invalid univariate polynomial, exponent must be an unsigned integer", arg2);
            unsigned k = arg2->get_numeral().get_unsigned();
            m.pw(p.size(), p.c_ptr(), k, p);
        }
        else {
            throw sexpr2upolynomial_exception("invalid univariate polynomial, '+', '-', '^' or '*' expected", s);
        }
    }
    else if (s->is_numeral()) {
        // make constant polynomial
        rational a = s->get_numeral();
        if (!a.is_int())
            throw sexpr2upolynomial_exception("invalid univariate polynomial, integer coefficient expected", s);
        m.set(1, &a, p);
    }
    else if (s->is_symbol()) {
        if (s->get_symbol() != "x") 
            throw sexpr2upolynomial_exception("invalid univariate polynomial, variable 'x' expected", s);
        // make identity
        rational as[2] = { rational(0), rational(1) };
        m.set(2, as, p);
    }
    else {
        throw sexpr2upolynomial_exception("invalid univariate polynomial, unexpected ", s);
    }
} 

void sexpr2upolynomial(upolynomial::manager & m, sexpr const * s, upolynomial::numeral_vector & p) {
    sexpr2upolynomial(m, s, p, 0);
}
