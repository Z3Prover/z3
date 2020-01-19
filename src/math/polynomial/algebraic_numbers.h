/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    algebraic_numbers.h

Abstract:

    Real Algebraic Numbers

Author:

    Leonardo (leonardo) 2011-11-22

Notes:

--*/
#ifndef ALGEBRAIC_NUMBERS_H_
#define ALGEBRAIC_NUMBERS_H_

#include "util/rational.h"
#include "util/mpq.h"
#include "math/polynomial/polynomial.h"
#include "util/z3_exception.h"
#include "util/scoped_numeral.h"
#include "util/scoped_numeral_vector.h"
#include "util/tptr.h"
#include "util/statistics.h"
#include "util/params.h"
#include "util/rlimit.h"

class small_object_allocator;
class mpbq_manager;
class mpbq;

namespace algebraic_numbers {
    class anum;
    class manager;

    class algebraic_exception : public default_exception {
    public:
        algebraic_exception(char const * msg):default_exception(msg) {}
    };

    class manager {
    public:
        struct imp;
    private:
        imp *  m_imp;
        small_object_allocator * m_allocator;
        bool   m_own_allocator;
    public:
        static bool precise() { return true; }
        static bool field() { return true; }
        typedef anum numeral;
        typedef svector<numeral> numeral_vector;
        typedef _scoped_numeral<manager> scoped_numeral;
        typedef _scoped_numeral_vector<manager> scoped_numeral_vector;

        manager(reslimit& rl, unsynch_mpq_manager & m, params_ref const & p = params_ref(), small_object_allocator * a = nullptr);
        ~manager();

        static void get_param_descrs(param_descrs & r);
        static void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }

        void updt_params(params_ref const & p);

        unsynch_mpq_manager & qm() const;

        mpbq_manager & bqm() const;

        void del(numeral & a);
        
        /**
           \brief a <- 0
        */
        void reset(numeral & a);
        
        /**
           \brief Return true if a is zero.
        */
        bool is_zero(numeral const & a);
        
        /**
           \brief Return true if a is positive.
        */
        bool is_pos(numeral const & a);

        /**
           \brief Return true if a is negative.
        */
        bool is_neg(numeral const & a);

        /**
           \brief Return true if a is a rational number.
        */
        bool is_rational(numeral const & a);

        /**
           \brief Return true if a is an integer.
        */
        bool is_int(numeral const & a);
        
        /**
           \brief Degree of the algebraic number.
           That is, degree of the polynomial that is used to encode \c a.
        */
        unsigned degree(numeral const & a);

        /**
           \brief Convert a into a rational number.
           
           \pre is_rational(a)
        */
        void to_rational(numeral const & a, mpq & r);

        /**
           \brief Convert a into a rational number.
           
           \pre is_rational(a)
        */
        void to_rational(numeral const & a, rational & r);

        /**
           \brief a <- n
        */
        void set(numeral & a, int n);
        void set(numeral & a, mpz const & n);
        void set(numeral & a, mpq const & n);
        void set(numeral & a, numeral const & n);

        void swap(numeral & a, numeral & b);

        /**
           \brief Store in b an integer value smaller than 'a'.

           Remark: this is not the floor, but b <= floor(a)
        */
        void int_lt(numeral const & a, numeral & b);

        /**
           \brief Store in b an integer value bigger than 'a'

           Remark: this is not the ceil, but b >= ceil(a)
        */
        void int_gt(numeral const & a, numeral & b);
        
        /**
           \brief Store in result a value in the interval (prev, next)

           \pre lt(pre,v next)
        */
        void select(numeral const & prev, numeral const & curr, numeral & result);

        /**
           \brief Isolate the roots of (an univariate polynomial) p, and store them as algebraic numbers in \c root.
           That is, p is in Z[x].
        */
        void isolate_roots(polynomial_ref const & p, numeral_vector & roots);

        /**
           \brief Isolate the roots of a multivariate polynomial p such that all but one variable of p is fixed by x2v, and 
           store them as algebraic numbers in \c root.
           
           That is, we are viewing p as a polynomial in Z[y_1, ..., y_n][x]: 
                       q_n(y_1, ..., y_n)x^n + ... + q_1(y_1, ..., y_n)*x + q_0
           And we are returning the roots of 
                       q_n(x2v(y_1), ..., x2v(y_n))x^n + ... + q_1(x2v(y_1), ..., x2v(y_n))*x + q_0
        */
        void isolate_roots(polynomial_ref const & p, polynomial::var2anum const & x2v, numeral_vector & roots);

        /**
           \brief Isolate the roots of the given polynomial, and compute its sign between them.
        */
        void isolate_roots(polynomial_ref const & p, polynomial::var2anum const & x2v, numeral_vector & roots, svector<sign> & signs);

        /**
           \brief Store in r the i-th root of p.
           
           This method throws an exception if p does not have at least i roots.
           
           This method is not really used in the nonlinear procedure.
           It is mainly used for debugging purposes, and creating regression tests

           \pre i > 0
        */
        void mk_root(polynomial_ref const & p, unsigned i, numeral & r);
        
        /**
           \brief Store in r the i-th root of p.
           This method throws an exception if the s-expression p does not represent
           an univariate polynomial, of if p does not have at least i roots.

           This method is not really used in the nonlinear procedure.
           It is mainly used for debugging purposes, and "reading" root objects in the SMT 2.0 front-end.
           
           \pre i > 0
        */
        void mk_root(sexpr const * p, unsigned i, numeral & r);
        
        /**
           \brief Return a^{1/k}
           
           Throws an exception if the result is not a real.
           That is, (a is negative and k is even) or (k is zero).
        */           
        void root(numeral const & a, unsigned k, numeral & b);
        
        /**
           \brief Return a^k
           
           Throws an exception if 0^0.
        */
        void power(numeral const & a, unsigned k, numeral & b);

        /**
           \brief c <- a + b
        */
        void add(numeral const & a, numeral const & b, numeral & c);
        void add(numeral const & a, mpz const & b, numeral & c);

        /**
           \brief c <- a - b
        */
        void sub(numeral const & a, numeral const & b, numeral & c);

        /**
           \brief c <- a * b
        */
        void mul(numeral const & a, numeral const & b, numeral & c);

        /**
           \brief a <- -a
        */
        void neg(numeral & a);

        /**
           \brief a <- 1/a  if a != 0
        */
        void inv(numeral & a);

        /**
           \brief c <- a/b if b != 0
        */
        void div(numeral const & a, numeral const & b, numeral & c);

        /**
           Return -1 if a < b
           Return 0  if a == b
           Return 1  if a > b
        */
        sign compare(numeral const & a, numeral const & b);
        
        /**
           \brief a == b
        */
        bool eq(numeral const & a, numeral const & b);
        bool eq(numeral const & a, mpq const & b);
        bool eq(numeral const & a, mpz const & b);

        /**
           \brief a != b
        */
        bool neq(numeral const & a, numeral const & b) { return !eq(a, b); }
        bool neq(numeral const & a, mpq const & b) { return !eq(a, b); }
        bool neq(numeral const & a, mpz const & b) { return !eq(a, b); }

        /**
           \brief a < b
        */
        bool lt(numeral const & a, numeral const & b);
        bool lt(numeral const & a, mpq const & b);
        bool lt(numeral const & a, mpz const & b);

        /**
           \brief a > b
        */
        bool gt(numeral const & a, numeral const & b) { return lt(b, a); }
        bool gt(numeral const & a, mpq const & b);
        bool gt(numeral const & a, mpz const & b);

        /**
           \brief a <= b
        */
        bool le(numeral const & a, numeral const & b) { return !gt(a, b); }
        bool le(numeral const & a, mpq const & b) { return !gt(a, b); }
        bool le(numeral const & a, mpz const & b) { return !gt(a, b); }

        /**
           \brief a >= b
        */
        bool ge(numeral const & a, numeral const & b) { return !lt(a, b); }
        bool ge(numeral const & a, mpq const & b) { return !lt(a, b); }
        bool ge(numeral const & a, mpz const & b) { return !lt(a, b); }

        /**
           \brief Evaluate the sign of a multivariate polynomial p(x_1, ..., x_n)
           at assignment x2v: [x_1 -> alpha_1, ..., x_n -> alpha_n].

           \remark forall variable x in p, we have that x2v.contains(x) is true

           Return negative number  if p(alpha_1, ..., alpha_n) <  0
           Return 0                if p(alpha_1, ..., alpha_n) == 0
           Return positive number  if p(alpha_1, ..., alpha_n) >  0
        */
        sign eval_sign_at(polynomial_ref const & p, polynomial::var2anum const & x2v);

        void get_polynomial(numeral const & a, svector<mpz> & r);
        
        // Procedures for getting lower and upper bounds for irrational numbers
        void get_lower(numeral const & a, mpbq & l);
        void get_lower(numeral const & a, mpq & l);
        void get_lower(numeral const & a, rational & l);
        void get_lower(numeral const & a, mpq & l, unsigned precision);
        void get_lower(numeral const & a, rational & l, unsigned precision);

        void get_upper(numeral const & a, mpbq & u);
        void get_upper(numeral const & a, mpq & u);
        void get_upper(numeral const & a, rational & u);
        void get_upper(numeral const & a, mpq & l, unsigned precision);
        void get_upper(numeral const & a, rational & l, unsigned precision);

        /**
           \brief Display algebraic number as a rational if is_rational(n)
           Otherwise, display it as an interval.
        */
        void display_interval(std::ostream & out, numeral const & a) const;

        /**
           \brief Display algebraic number in decimal notation.
           A question mark is added based on the precision requested.
        */
        void display_decimal(std::ostream & out, numeral const & a, unsigned precision = 10) const;

        /**
           \brief Display algebraic number as a root object: (p, i)
           That is, 'a' is the i-th root of p.
        */
        void display_root(std::ostream & out, numeral const & a) const;
        
        /**
           \brief Display algebraic number as a root object in SMT 2.0 style: (root-obj p i)
           That is, 'a' is the i-th root of p.
        */
        void display_root_smt2(std::ostream & out, numeral const & a) const;

        /**
           \brief Display algebraic number in Mathematica format.
        */
        void display_mathematica(std::ostream & out, numeral const & a) const;

        void display(std::ostream & out, numeral const & a) { return display_decimal(out, a); }

        void reset_statistics();
        
        void collect_statistics(statistics & st) const;
    };

    struct basic_cell;
    struct algebraic_cell;

    enum anum_kind { BASIC = 0, ROOT };

    class anum {
        friend struct manager::imp;
        friend class manager;
        void * m_cell;
        anum(basic_cell * cell):m_cell(TAG(void*, cell, BASIC)) {}
        anum(algebraic_cell * cell):m_cell(TAG(void*, cell, ROOT)) {}
        bool is_basic() const { return GET_TAG(m_cell) == BASIC; }
        basic_cell * to_basic() const { SASSERT(is_basic()); return UNTAG(basic_cell*, m_cell); }
        algebraic_cell * to_algebraic() const { SASSERT(!is_basic()); return UNTAG(algebraic_cell*, m_cell); }
    public:
        anum():m_cell(nullptr) {}
    };
};

typedef algebraic_numbers::manager anum_manager;
typedef algebraic_numbers::manager::numeral anum;
typedef algebraic_numbers::manager::numeral_vector anum_vector;
typedef algebraic_numbers::manager::scoped_numeral scoped_anum;
typedef algebraic_numbers::manager::scoped_numeral_vector scoped_anum_vector;

#define AN_MK_COMPARISON_CORE(EXTERNAL, INTERNAL, TYPE)         \
inline bool EXTERNAL(scoped_anum const & a, TYPE const & b) {   \
    anum_manager & m = a.m();                                   \
    scoped_anum _b(m);                                          \
    m.set(_b, b);                                               \
    return m.INTERNAL(a, _b);                                   \
}

#define AN_MK_COMPARISON(EXTERNAL, INTERNAL)       \
AN_MK_COMPARISON_CORE(EXTERNAL, INTERNAL, int)     \
AN_MK_COMPARISON_CORE(EXTERNAL, INTERNAL, mpz)     \
AN_MK_COMPARISON_CORE(EXTERNAL, INTERNAL, mpq)

AN_MK_COMPARISON(operator==, eq);
AN_MK_COMPARISON(operator!=, neq);
AN_MK_COMPARISON(operator<,  lt);
AN_MK_COMPARISON(operator<=, le);
AN_MK_COMPARISON(operator>,  gt);
AN_MK_COMPARISON(operator>=, ge);

#undef AN_MK_COMPARISON
#undef AN_MK_COMPARISON_CORE

#define AN_MK_BINARY_CORE(EXTERNAL, INTERNAL, TYPE)                     \
inline scoped_anum EXTERNAL(scoped_anum const & a, TYPE const & b) {    \
    anum_manager & m = a.m();                                           \
    scoped_anum _b(m);                                                  \
    m.set(_b, b);                                                       \
    scoped_anum r(m);                                                   \
    m.INTERNAL(a, _b, r);                                               \
    return r;                                                           \
}

#define AN_MK_BINARY(EXTERNAL, INTERNAL)        \
AN_MK_BINARY_CORE(EXTERNAL, INTERNAL, int)      \
AN_MK_BINARY_CORE(EXTERNAL, INTERNAL, mpz)      \
AN_MK_BINARY_CORE(EXTERNAL, INTERNAL, mpq)

AN_MK_BINARY(operator+, add)
AN_MK_BINARY(operator-, sub)
AN_MK_BINARY(operator*, mul)
AN_MK_BINARY(operator/, div)

#undef AN_MK_BINARY
#undef AN_MK_BINARY_CORE

inline scoped_anum root(scoped_anum const & a, unsigned k) {
    scoped_anum r(a.m());
    a.m().root(a, k, r);
    return r;
}

inline scoped_anum power(scoped_anum const & a, unsigned k) {
    scoped_anum r(a.m());
    a.m().power(a, k, r);
    return r;
}

inline scoped_anum operator^(scoped_anum const & a, unsigned k) {
    return power(a, k);
}

inline bool is_int(scoped_anum const & a) {
    return a.m().is_int(a);
}

inline bool is_rational(scoped_anum const & a) {
    return a.m().is_rational(a);
}

struct root_obj_pp {
    anum_manager & m;
    anum const &   n;
    root_obj_pp(anum_manager & _m, anum const & _n):m(_m), n(_n) {}
    root_obj_pp(scoped_anum const & _n):m(_n.m()), n(_n.get()) {}
};

inline std::ostream & operator<<(std::ostream & out, root_obj_pp const & n) {
    n.m.display_root(out, n.n);
    return out;
}

struct decimal_pp {
    anum_manager & m;
    anum const &   n;
    unsigned       prec;
    decimal_pp(anum_manager & _m, anum const & _n, unsigned p):m(_m), n(_n), prec(p) {}
    decimal_pp(scoped_anum const & _n, unsigned p):m(_n.m()), n(_n.get()), prec(p) {}
};

inline std::ostream & operator<<(std::ostream & out, decimal_pp const & n) {
    n.m.display_decimal(out, n.n, n.prec);
    return out;
}

struct interval_pp {
    anum_manager & m;
    anum const &   n;
    interval_pp(anum_manager & _m, anum const & _n):m(_m), n(_n) {}
    interval_pp(scoped_anum const & _n):m(_n.m()), n(_n.get()) {}
};

inline std::ostream & operator<<(std::ostream & out, interval_pp const & n) {
    n.m.display_interval(out, n.n);
    return out;
}

#endif
