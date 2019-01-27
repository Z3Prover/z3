/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    realclosure.h

Abstract:

    Package for computing with elements of the realclosure of a field containing
       - all rationals
       - extended with computable transcendental real numbers (e.g., pi and e)
       - infinitesimals

Author:

    Leonardo (leonardo) 2013-01-02

Notes:

--*/
#ifndef REALCLOSURE_H_
#define REALCLOSURE_H_

#include "util/mpq.h"
#include "util/params.h"
#include "util/scoped_numeral.h"
#include "util/scoped_numeral_vector.h"
#include "math/interval/interval.h"
#include "util/z3_exception.h"
#include "util/rlimit.h"

namespace realclosure {
    class num;

    typedef interval_manager<im_default_config> mpqi_manager;
    typedef default_exception exception;

    class mk_interval {
    public:
        virtual void operator()(unsigned k, mpqi_manager & im, mpqi_manager::interval & r) = 0;
    };

    class manager {
    public:
        struct imp;
    private:
        friend class save_interval_ctx;
        imp * m_imp;
    public:
        manager(reslimit& lim, unsynch_mpq_manager & m, params_ref const & p = params_ref(), small_object_allocator * a = nullptr);
        ~manager();
        typedef num                             numeral;
        typedef svector<numeral>                numeral_vector;
        typedef _scoped_numeral<manager>        scoped_numeral;
        typedef _scoped_numeral_vector<manager> scoped_numeral_vector;

        static void get_param_descrs(param_descrs & r);
        static void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }


        void updt_params(params_ref const & p);

        unsynch_mpq_manager & qm() const;

        void del(numeral & a);

        /**
           \brief Add a new infinitesimal to the current field. The new infinitesimal is smaller than any positive element in the field.
        */
        void mk_infinitesimal(char const * name, char const * pp_name, numeral & r);
        void mk_infinitesimal(numeral & r);
        
        /**
           \brief Add a new transcendental real value to the field. 
           The functor \c mk_interval is used to compute approximations of the transcendental value.
           This procedure should be used with care, if the value is not really transcendental with respect to the current
           field, computations with the new numeral may not terminate.
           Example: we extended the field with Pi. Pi is transcendental with respect to a field that contains only algebraic real numbers.
           So, this step is fine. Let us call the resultant field F. 
           Then, we extend the field F with 1 - Pi. 1 - Pi is transcendental with respect to algebraic real numbers, but it is NOT transcendental
           with respect to F, since F contains Pi.
        */
        void mk_transcendental(char const * name, char const * pp_name, mk_interval & proc, numeral & r);
        void mk_transcendental(mk_interval & proc, numeral & r);

        /**
           \brief r <- pi
        */
        void mk_pi(numeral & r);

        /**
           \brief r <- e (Euler's constant)
        */
        void mk_e(numeral & r);

        /**
           \brief Isolate the roots of the univariate polynomial as[0] + as[1]*x + ... + as[n-1]*x^{n-1}
           The roots are stored in \c roots.
        */
        void isolate_roots(unsigned n, numeral const * as, numeral_vector & roots);

        /**
           \brief a <- 0
        */
        void reset(numeral & a);

        /**
           \brief Return the sign of a.
        */
        int sign(numeral const & a);
        
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
           \brief Return true if a is an integer.
        */
        bool is_int(numeral const & a);
        
        /**
           \brief Return true if the representation of \c a depends on
           infinitesimal extensions.
        */
        bool depends_on_infinitesimals(numeral const & a);
        
        /**
           \brief a <- n
        */
        void set(numeral & a, int n);
        void set(numeral & a, mpz const & n);
        void set(numeral & a, mpq const & n);
        void set(numeral & a, numeral const & n);

        void swap(numeral & a, numeral & b);

        /**
           \brief Return a^{1/k}
           
           Throws an exception if (a is negative and k is even) or (k is zero).
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
           \brief b <- -a
        */
        void neg(numeral const & a, numeral & b);

        /**
           \brief a <- 1/a  if a != 0
        */
        void inv(numeral & a);
        
        /**
           \brief b <- 1/a if a != 0
        */
        void inv(numeral const & a, numeral & b);

        /**
           \brief c <- a/b if b != 0
        */
        void div(numeral const & a, numeral const & b, numeral & c);

        /**
           Return -1 if a < b
           Return 0  if a == b
           Return 1  if a > b
        */
        int compare(numeral const & a, numeral const & b);
        
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
        
        void display(std::ostream & out, numeral const & a, bool compact=false, bool pp=false) const;

        /**
           \brief Display a real number in decimal notation.
           A question mark is added based on the precision requested.
           This procedure throws an exception if the \c a is not a real.
        */
        void display_decimal(std::ostream & out, numeral const & a, unsigned precision = 10) const;

        
        void display_interval(std::ostream & out, numeral const & a) const;
    
        void clean_denominators(numeral const & a, numeral & p, numeral & q);
    };

    struct value;
    class num {
        friend class manager;
        friend struct manager::imp;
        value * m_value;
    public:
        num():m_value(nullptr) {}

        // Low level functions for implementing the C API
        void * c_ptr() { return m_value; }
        static num mk(void * ptr) { num r; r.m_value = reinterpret_cast<value*>(ptr); return r; }
    };
};

typedef realclosure::manager             rcmanager;
typedef rcmanager::numeral               rcnumeral;
typedef rcmanager::numeral_vector        rcnumeral_vector;
typedef rcmanager::scoped_numeral        scoped_rcnumeral;
typedef rcmanager::scoped_numeral_vector scoped_rcnumeral_vector;


#define RCF_MK_COMPARISON_CORE(EXTERNAL, INTERNAL, TYPE)                \
inline bool EXTERNAL(scoped_rcnumeral const & a, TYPE const & b) {      \
    rcmanager & m = a.m();                                              \
    scoped_rcnumeral _b(m);                                             \
    m.set(_b, b);                                                       \
    return m.INTERNAL(a, _b);                                           \
}

#define RCF_MK_COMPARISON(EXTERNAL, INTERNAL)       \
RCF_MK_COMPARISON_CORE(EXTERNAL, INTERNAL, int)     \
RCF_MK_COMPARISON_CORE(EXTERNAL, INTERNAL, mpz)     \
RCF_MK_COMPARISON_CORE(EXTERNAL, INTERNAL, mpq)

RCF_MK_COMPARISON(operator==, eq);
RCF_MK_COMPARISON(operator!=, neq);
RCF_MK_COMPARISON(operator<,  lt);
RCF_MK_COMPARISON(operator<=, le);
RCF_MK_COMPARISON(operator>,  gt);
RCF_MK_COMPARISON(operator>=, ge);

#undef RCF_MK_COMPARISON
#undef RCF_MK_COMPARISON_CORE

#define RCF_MK_BINARY_CORE(EXTERNAL, INTERNAL, TYPE)                    \
inline scoped_rcnumeral EXTERNAL(scoped_rcnumeral const & a, TYPE const & b) { \
    rcmanager & m = a.m();                                              \
    scoped_rcnumeral _b(m);                                             \
    m.set(_b, b);                                                       \
    scoped_rcnumeral r(m);                                              \
    m.INTERNAL(a, _b, r);                                               \
    return r;                                                           \
}

#define RCF_MK_BINARY(EXTERNAL, INTERNAL)        \
RCF_MK_BINARY_CORE(EXTERNAL, INTERNAL, int)      \
RCF_MK_BINARY_CORE(EXTERNAL, INTERNAL, mpz)      \
RCF_MK_BINARY_CORE(EXTERNAL, INTERNAL, mpq)

RCF_MK_BINARY(operator+, add)
RCF_MK_BINARY(operator-, sub)
RCF_MK_BINARY(operator*, mul)
RCF_MK_BINARY(operator/, div)

#undef RCF_MK_BINARY
#undef RCF_MK_BINARY_CORE

inline scoped_rcnumeral root(scoped_rcnumeral const & a, unsigned k) {
    scoped_rcnumeral r(a.m());
    a.m().root(a, k, r);
    return r;
}

inline scoped_rcnumeral power(scoped_rcnumeral const & a, unsigned k) {
    scoped_rcnumeral r(a.m());
    a.m().power(a, k, r);
    return r;
}

inline scoped_rcnumeral operator^(scoped_rcnumeral const & a, unsigned k) {
    return power(a, k);
}

inline bool is_int(scoped_rcnumeral const & a) {
    return a.m().is_int(a);
}

struct rc_sym_pp {
    rcmanager & m;
    rcnumeral const &   n;
    rc_sym_pp(rcmanager & _m, rcnumeral const & _n):m(_m), n(_n) {}
    rc_sym_pp(scoped_rcnumeral const & _n):m(_n.m()), n(_n.get()) {}
};

inline rc_sym_pp sym_pp(scoped_rcnumeral const & _n) {
    return rc_sym_pp(_n);
}

inline std::ostream & operator<<(std::ostream & out, rc_sym_pp const & n) {
    n.m.display(out, n.n);
    return out;
}

struct rc_decimal_pp {
    rcmanager & m;
    rcnumeral const &   n;
    unsigned       prec;
    rc_decimal_pp(rcmanager & _m, rcnumeral const & _n, unsigned p):m(_m), n(_n), prec(p) {}
    rc_decimal_pp(scoped_rcnumeral const & _n, unsigned p):m(_n.m()), n(_n.get()), prec(p) {}
};

inline std::ostream & operator<<(std::ostream & out, rc_decimal_pp const & n) {
    n.m.display_decimal(out, n.n, n.prec);
    return out;
}

inline rc_decimal_pp decimal_pp(scoped_rcnumeral const & n, unsigned prec = 10) {
    return rc_decimal_pp(n, prec);
}

struct rc_interval_pp {
    rcmanager & m;
    rcnumeral const &   n;
    rc_interval_pp(rcmanager & _m, rcnumeral const & _n):m(_m), n(_n) {}
    rc_interval_pp(scoped_rcnumeral const & _n):m(_n.m()), n(_n.get()) {}
};

inline std::ostream & operator<<(std::ostream & out, rc_interval_pp const & n) {
    n.m.display_interval(out, n.n);
    return out;
}

inline rc_interval_pp interval_pp(scoped_rcnumeral const & n) {
    return rc_interval_pp(n);
}

#endif
