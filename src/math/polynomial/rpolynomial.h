/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    rpolynomial.h

Abstract:

    Goodies for creating and handling polynomials in dense recursive representation.

Author:

    Leonardo (leonardo) 2012-06-11

Notes:

--*/
#ifndef RPOLYNOMIAL_H_
#define RPOLYNOMIAL_H_

#include"mpz.h"
#include"rational.h"
#include"obj_ref.h"
#include"ref_vector.h"
#include"z3_exception.h"
#include"polynomial.h"

namespace rpolynomial {
    
    typedef polynomial::var var;
    const var null_var = polynomial::null_var;
    typedef polynomial::var_vector var_vector;
    typedef polynomial::display_var_proc display_var_proc;
    typedef polynomial::polynomial som_polynomial;
   
    class polynomial;
    class manager;
    typedef obj_ref<polynomial, manager>     polynomial_ref;
    typedef ref_vector<polynomial, manager>  polynomial_ref_vector;
    typedef ptr_vector<polynomial>           polynomial_vector;
    
    class manager {
    public:
        typedef unsynch_mpz_manager                     numeral_manager;
        typedef numeral_manager::numeral                numeral;
        typedef svector<numeral>                        numeral_vector;
        typedef _scoped_numeral<numeral_manager>        scoped_numeral;
        typedef _scoped_numeral_vector<numeral_manager> scoped_numeral_vector;
        struct imp;
    private:
        imp * m_imp;
    public:
        manager(numeral_manager & m, small_object_allocator * a = 0);
        ~manager();

        numeral_manager & m() const;
        small_object_allocator & allocator() const;

        void set_cancel(bool f);

        /**
           \brief Create a new variable.
        */
        var mk_var();

        /**
           \brief Return the number of variables in the manager.
        */
        unsigned num_vars() const;

        /**
           \brief Return true if x is a valid variable in this manager.
        */
        bool is_valid(var x) const { return x < num_vars(); }

        /**
           \brief Increment reference counter.
        */
        void inc_ref(polynomial * p);
        
        /**
           \brief Decrement reference counter.
        */
        void dec_ref(polynomial * p);

        /**
           \brief Return true if \c p is the zero polynomial.
        */
        bool is_zero(polynomial const * p);

        /**
           \brief Return true if p1 == p2.
        */
        bool eq(polynomial const * p1, polynomial const * p2);
        
        /**
           \brief Return true if \c p is the constant polynomial.
        */
        static bool is_const(polynomial const * p);

        /**
           \brief Return true if \c p is an univariate polynomial.
        */
        static bool is_univariate(polynomial const * p);

        /**
           \brief Return true if \c p is a monomial.
        */
        bool is_monomial(polynomial const * p) const;

        /**
           \brief Return the maximal variable occurring in p.
           
           Return null_var if p is a constant polynomial.
        */
        static var max_var(polynomial const * p);

        /**
           \brief Return the size of the polynomail p. 
           It is the degree(p) on max_var(p) + 1.
        */
        static unsigned size(polynomial const * p);

        /**
           \brief Return a polynomial h that is the coefficient of max_var(p)^k in p.
           if p does not contain any monomial containing max_var(p)^k, then return 0.
        */
        polynomial * coeff(polynomial const * p, unsigned k);
        
        /**
           \brief Create the zero polynomial.
        */
        polynomial * mk_zero(); 
        
        /**
           \brief Create the constant polynomial \c r.
           
           \warning r is a number managed by the numeral_manager in the polynomial manager

           \warning r is reset.
        */
        polynomial * mk_const(numeral const & r);
        
        /**
           \brief Create the constant polynomial \c r.
           
           \pre r must be an integer
        */
        polynomial * mk_const(rational const & r);

        /**
           \brief Create the polynomial x^k
        */
        polynomial * mk_polynomial(var x, unsigned k = 1);

        polynomial * mul(numeral const & r, polynomial const * p);

        polynomial * neg(polynomial const * p);

        polynomial * add(numeral const & r, polynomial const * p);

        polynomial * add(int c, polynomial const * p);

        polynomial * add(polynomial const * p1, polynomial const * p2);

        /**
           \brief Convert the given polynomial in sum-of-monomials form into a polynomial in dense recursive form.
        */
        polynomial * translate(som_polynomial const * p);
        
        void display(std::ostream & out, polynomial const * p, display_var_proc const & proc = display_var_proc(), bool use_star = false) const;
        
        void display_smt2(std::ostream & out, polynomial const * p, display_var_proc const & proc = display_var_proc()) const;

        friend std::ostream & operator<<(std::ostream & out, polynomial_ref const & p) {
            p.m().display(out, p);
            return out;
        }
    };
};

typedef rpolynomial::polynomial_ref          rpolynomial_ref;
typedef rpolynomial::polynomial_ref_vector   rpolynomial_ref_vector;

inline rpolynomial_ref neg(rpolynomial_ref const & p) {
    rpolynomial::manager & m = p.m();
    return rpolynomial_ref(m.neg(p), m);
}

inline rpolynomial_ref operator-(rpolynomial_ref const & p) {
    rpolynomial::manager & m = p.m();
    return rpolynomial_ref(m.neg(p), m);
}

inline rpolynomial_ref operator+(int a, rpolynomial_ref const & p) {
    rpolynomial::manager & m = p.m();
    return rpolynomial_ref(m.add(a, p), m);
}

inline rpolynomial_ref operator+(rpolynomial_ref const & p, int a) {
    rpolynomial::manager & m = p.m();
    return rpolynomial_ref(m.add(a, p), m);
}



#endif
