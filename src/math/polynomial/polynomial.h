/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    polynomial.h

Abstract:

    Goodies for creating and handling polynomials.

Author:

    Leonardo (leonardo) 2011-11-15

Notes:

--*/
#ifndef POLYNOMIAL_H_
#define POLYNOMIAL_H_

#include "util/mpz.h"
#include "util/rational.h"
#include "util/obj_ref.h"
#include "util/ref_vector.h"
#include "util/z3_exception.h"
#include "util/scoped_numeral.h"
#include "util/scoped_numeral_vector.h"
#include "util/params.h"
#include "util/mpbqi.h"
#include "util/rlimit.h"
#include "util/lbool.h"

class small_object_allocator;

namespace algebraic_numbers {
    class anum;
    class manager;
};

namespace polynomial {
    typedef unsigned var;
    const var null_var = UINT_MAX;
    typedef svector<var> var_vector;
    class monomial;

    int lex_compare(monomial const * m1, monomial const * m2);
    int lex_compare2(monomial const * m1, monomial const * m2, var min_var);
    int graded_lex_compare(monomial const * m1, monomial const * m2);
    int rev_lex_compare(monomial const * m1, monomial const * m2);
    int graded_rev_lex_compare(monomial const * m1, monomial const * m2);

    // It is used only for signing cancellation.
    class polynomial_exception : public default_exception {
    public:
        polynomial_exception(char const * msg):default_exception(msg) {}
    };

    /**
       \brief A mapping from variables to degree
    */
    class var2degree {
        unsigned_vector m_var2degree;
    public:
        void set_degree(var x, unsigned d) { m_var2degree.setx(x, d, 0); }
        unsigned degree(var x) const { return m_var2degree.get(x, 0); }
        void display(std::ostream & out) const;
        friend std::ostream & operator<<(std::ostream & out, var2degree const & ideal) { ideal.display(out); return out; }
    };

    template<typename ValManager, typename Value = typename ValManager::numeral>
    class var2value {
    public:
        virtual ValManager & m() const = 0;
        virtual bool contains(var x) const = 0;
        virtual Value const & operator()(var x) const = 0;
    };

    typedef var2value<unsynch_mpq_manager>        var2mpq;
    typedef var2value<mpbqi_manager>              var2mpbqi;
    typedef var2value<algebraic_numbers::manager, algebraic_numbers::anum> var2anum;

    class monomial_manager;

    /**
       \brief Parameters for polynomial factorization.
    */
    struct factor_params {
        unsigned m_max_p;              //!< factor in GF_p using primes p <= m_max_p (default UINT_MAX)
        unsigned m_p_trials;           //!< Number of different finite factorizations: G_p1 ... G_pk, where k < m_p_trials
        unsigned m_max_search_size;    //!< Threshold on the search space. 
        factor_params();
        factor_params(unsigned max_p, unsigned p_trials, unsigned max_search_size);
        void updt_params(params_ref const & p);
        /*
          REG_MODULE_PARAMS('factor', polynomial::factor_params::get_param_descrs')
        */
        static void get_param_descrs(param_descrs & r);
    };

    struct display_var_proc {
        virtual std::ostream& operator()(std::ostream & out, var x) const { return out << "x" << x; }
    };

    class polynomial;
    class manager;
    typedef obj_ref<monomial, manager>       monomial_ref;
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
        
        /**
           \brief Contains a factorization of a polynomial of the form c * (f_1)^k_1 * ... (f_n)^k_n
        */
        class factors {
            vector<polynomial *>       m_factors;
            svector<unsigned>          m_degrees;
            manager &                  m_manager;
            numeral                    m_constant;
            unsigned                   m_total_factors;
        public:
            factors(manager & m);
            ~factors();
            
            /**
               \brief Number of distinct factors (not counting multiplicities).
            */
            unsigned distinct_factors() const { return m_factors.size(); }
            
            /**
               \brief Number of distinct factors (counting multiplicities).
            */
            unsigned total_factors() const { return m_total_factors; }

            /**
               \brief Returns the factor at given position.
            */    
            polynomial_ref operator[](unsigned i) const;
            
            /**
               \brief Returns the constant (c above).
            */
            numeral const & get_constant() const { return m_constant; }
            
            /**
               \brief Sets the constant.
            */
            void set_constant(numeral const & constant);
            
            /**
               \brief Returns the degree of a factor (k_i above).
            */
            unsigned get_degree(unsigned i) const { return m_degrees[i]; }
            
            /**
               \brief Sets the degree of a factor.
            */
            void set_degree(unsigned i, unsigned degree);
            
            /**
               \brief Adds a polynomial to the factorization.
            */
            void push_back(polynomial * p, unsigned degree);
            
            /**
               \brief Returns the polynomial that this factorization represents.
            */
            void multiply(polynomial_ref & out) const; 
            
            manager & m() const { return m_manager; }
            manager & pm() const { return m_manager; }

            void display(std::ostream& out) const;

            void reset();

            friend std::ostream & operator<<(std::ostream & out, factors const & f) {
                f.display(out);
                return out;
            }
        };
        
        struct imp;
    private:
        imp * m_imp;
    public:
        manager(reslimit& lim, numeral_manager & m, monomial_manager * mm = nullptr);
        manager(reslimit& lim, numeral_manager & m, small_object_allocator * a);
        ~manager();

        numeral_manager & m() const;
        monomial_manager & mm() const;
        small_object_allocator & allocator() const;

        /**
           \brief Return true if Z_p[X1, ..., Xn]
        */
        bool modular() const;
        /**
           \brief Return p in Z_p[X1, ..., Xn]
           \pre modular
        */
        numeral const & p() const;
        
        /**
           \brief Set manager as Z[X1, ..., Xn]
        */
        void set_z();
        /**
           \brief Set manager as Z_p[X1, ..., Xn]
        */
        void set_zp(numeral const & p);
        void set_zp(uint64_t p);

        /**
           \brief Abstract event handler.
        */
        class del_eh {
            friend class manager;
            del_eh * m_next;
        public:
            del_eh():m_next(nullptr) {}
            virtual void operator()(polynomial * p) = 0;
        };

        /**
           \brief Install a "delete polynomial" event handler.
           The event handler is not owned by the polynomial manager.
           If eh = 0, then it uninstall the event handler.
        */
        void add_del_eh(del_eh * eh);
        void remove_del_eh(del_eh * eh);

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
        void inc_ref(monomial * m);
        
        /**
           \brief Decrement reference counter.
        */
        void dec_ref(polynomial * p);
        void dec_ref(monomial * m);

        /**
           \brief Return an unique id associated with \c m.
           This id can be used to implement efficient mappings from monomial to data.
        */
        static unsigned id(monomial const * m);

        /**        
           \brief Return an unique id associated with \c m.
           This id can be used to implement efficient mappings from polynomial to data.
        */
        static unsigned id(polynomial const * p);
        
        /**
           \brief Return true if \c m is the unit monomial.
        */
        static bool is_unit(monomial const * m);

        /**
           \brief Return true if \c p is the zero polynomial.
        */
        static bool is_zero(polynomial const * p);
        
        /**
           \brief Return true if \c p is the constant polynomial.
        */
        static bool is_const(polynomial const * p);

        /**
           \brief Return true if \c m is univariate.
        */
        static bool is_univariate(monomial const * m);

        /**
           \brief Return true if \c p is an univariate polynomial.
        */
        static bool is_univariate(polynomial const * p);

        /**
           \brief Return true if m is linear (i.e., it is of the form 1 or x).
        */
        static bool is_linear(monomial const * m);
       
        /**
           \brief Return true if all monomials in p are linear.
        */
        static bool is_linear(polynomial const * p);

        /**
           \brief Return true if the monomial is a variable.
        */
        static bool is_var(monomial const* p, var& v);

        /**
           \brief Return true if the polynomial is a variable.
        */
        bool is_var(polynomial const* p, var& v);

        /**
           \brief Return true if the polynomial is of the form x + k
        */
        bool is_var_num(polynomial const* p, var& v, scoped_numeral& n);

        /**
           \brief Return the degree of variable x in p.
        */
        static unsigned degree(polynomial const * p, var x);
        
        /**
           \brief Return the polynomial total degree. That is,
           the degree of the monomial of maximal degree in p.
        */
        static unsigned total_degree(polynomial const * p);
        
        /**
           \brief Return the number of monomials in p.
        */
        static unsigned size(polynomial const * p);
        
        /**
           \brief Return the maximal variable occurring in p.
           
           Return null_var if p is a constant polynomial.
        */
        static var max_var(polynomial const * p);
        
        /**
           \brief Return the coefficient of the i-th monomial in p.
           
           \pre i < size(p)
        */
        static numeral const & coeff(polynomial const * p, unsigned i);
        
        /**
           \brief Given an univariate polynomial, return the coefficient of x_k
        */
        static numeral const & univ_coeff(polynomial const * p, unsigned k); 
        
        /**
           \brief Return a polynomial h that is the coefficient of x^k in p.
           if p does not contain any monomial containing x^k, then return 0.
        */
        polynomial * coeff(polynomial const * p, var x, unsigned k);

        polynomial * coeff(polynomial const * p, var x, unsigned k, polynomial_ref & reduct);
        
        /**
           \brief Return true if the coefficient of x^k in p is an integer != 0.
        */
        bool nonzero_const_coeff(polynomial const * p, var x, unsigned k);

        /**
           \brief Return true if the coefficient of x^k in p is an integer, and store it in c.
        */
        bool const_coeff(polynomial const * p, var x, unsigned k, numeral & c);

        /**
           \brief Store in c the integer content of p.
        */
        void int_content(polynomial const * p, numeral & c);

        /**
           \brief Returns sum of the absolute value of the coefficients.
        */
        void abs_norm(polynomial const * p, numeral & norm);

        /**
           \brief Return the leading integer coefficient (among the loeding power of x, one is picked arbitrary).
        */
        numeral const & numeral_lc(polynomial const * p, var x);

        /**
           \brief Return the trailing integer coefficient (i.e. the constant term).
        */
        numeral const & numeral_tc(polynomial const * p);

        /**
           \brief Return the content i*c of p with respect to variable x.
           If p is a polynomial in Z[y_1, ..., y_k, x], then c is a polynomial in Z[y_1, ..., y_k]
        */
        void content(polynomial const * p, var x, numeral & i, polynomial_ref & c);
        void content(polynomial const * p, var x, polynomial_ref & c);

        /**
           \brief Return the primitive polynomial of p with respect to variable x.
           If p is a polynomial in Z[y_1, ..., y_k, x], then pp is a polynomial in Z[y_1, ..., y_k, x]
        */
        void primitive(polynomial const * p, var x, polynomial_ref & pp);
        
        /**
           \brief Return the integer content, content, and primitive polynomials of p with respect to x.
           i*c*pp = p
           If p is a polynomial in Z[y_1, ..., y_k, x], then 
               c is a polynomial in Z[y_1, ..., y_k]
               pp is a polynomial in Z[y_1, ..., y_k, x]
        */
        void icpp(polynomial const * p, var x, numeral & i, polynomial_ref & c, polynomial_ref & pp);

        polynomial * flip_sign_if_lm_neg(polynomial const * p);

        /**
           \brief Return the gcd g of p and q.
        */
        void gcd(polynomial const * p, polynomial const * q, polynomial_ref & g);

        /**
           \brief Return the i-th monomial of p.
        */
        static monomial * get_monomial(polynomial const * p, unsigned i);
        
        /**
           \brief Return the total degree of the given monomial.
        */
        static unsigned total_degree(monomial const * m);
        
        /**
           \brief Return the size (number of variables) of the given monomial.
        */
        static unsigned size(monomial const * m);
        
        /**
           \brief Convert a monomial created in a different manager.
        */
        monomial * convert(monomial const * m);

        /**
           \brief Return the i-th variable in the given monomial.

           \pre i < size(m)
        */
        static var get_var(monomial const * m, unsigned i);
        
        /**
           \brief Return the degree of the i-th variable in the given monomial.

           \pre i < size(m)
        */
        static unsigned degree(monomial const * m, unsigned i);

        /**
           \brief Return the degree of x in the given monomial.
        */
        static unsigned degree_of(monomial const * m, var x);

        /**
           \brief Return hash code for the given monomial.
        */
        static unsigned hash(monomial const * m);

        /**
           \brief Return hash code for the given polynomial.
        */
        unsigned hash(polynomial const * p);
        
        /**
           \brief Create the unit monomial. That is, the monomial of size zero.
        */
        monomial * mk_unit();

        /**
           \brief Create the zero polynomial. That is, the polynomial of size zero.
        */
        polynomial * mk_zero(); 
        
        /**
           \brief Create the constant polynomial \c r.
           
           \warning r is a number managed by the numeral_manager in the polynomial manager

           \warning r is reset.
        */
        polynomial * mk_const(numeral & r);
        
        /**
           \brief Create the constant polynomial \c r.
           
           \pre r must be an integer
        */
        polynomial * mk_const(rational const & r);

        /**
           \brief Create an univariate monomial.
        */
        monomial * mk_monomial(var x);

        /**
           \brief Create an univariate monomial.
        */
        monomial * mk_monomial(var x, unsigned k);
        
        /**
           \brief Create the monomial
           
           xs[0]*...*xs[sz-1]
           
           Remark: xs may contain duplicate variables.
           
           \warning The elements of xs will be reordered.
        */
        monomial * mk_monomial(unsigned sz, var * xs);
        
        /**
           \brief Create the polynomial x^k
        */
        polynomial * mk_polynomial(var x, unsigned k = 1);

        /**
           \brief Create the polynomial

           as[0]*ms[0] + ... + as[sz-1]*ms[sz - 1]

           \pre as's must be integers
        */
        polynomial * mk_polynomial(unsigned sz, rational const * as, monomial * const * ms);

        /**
           \brief Create the polynomial

           as[0]*ms[0] + ... + as[sz-1]*ms[sz - 1]
           
           \warning as's are numbers managed by mpq_manager in the polynomial manager

           \warning the numerals in as are reset.
        */
        polynomial * mk_polynomial(unsigned sz, numeral * as, monomial * const * ms);

        /**
           \brief Create the linear polynomial
           
           as[0]*xs[0] + ... + as[sz-1]*xs[sz-1] + c

           \pre as's must be integers
        */
        polynomial * mk_linear(unsigned sz, rational const * as, var const * xs, rational const & c);

        /**
           \brief Create the linear polynomial
           
           as[0]*xs[0] + ... + as[sz-1]*xs[sz-1] + c
           
           \warning as's are numbers managed by mpq_manager in the polynomial manager

           \warning the numerals in as are reset.
        */
        polynomial * mk_linear(unsigned sz, numeral * as, var const * xs, numeral & c);
        
        /**
           \brief Create an univariate polynomial of degree n
           
           as[0] + as[1]*x + as[2]*x^2 + ... + as[n]*x^n

           \warning \c as must contain n+1 elements.
        */
        polynomial * mk_univariate(var x, unsigned n, numeral * as);

        /**
           \brief Return -p
        */
        polynomial * neg(polynomial const * p);

        /**
           \brief Return p1 + p2
        */
        polynomial * add(polynomial const * p1, polynomial const * p2);    

        /**
           \brief Return p1 - p2
        */
        polynomial * sub(polynomial const * p1, polynomial const * p2);    

        /**
           \brief Return a1*m1*p1 + a2*m2*p2
        */
        polynomial * addmul(numeral const & a1, monomial const * m1, polynomial const * p1, numeral const & a2, monomial const * m2, polynomial const * p2);
        
        /**
           \brief Return p1 + a2*m2*p2
        */
        polynomial * addmul(polynomial const * p1, numeral const & a2, monomial const * m2, polynomial const * p2);

        /**
           \brief Return p1 + a2*p2
        */
        polynomial * addmul(polynomial const * p1, numeral const & a2, polynomial const * p2);
            
        /**
           \brief Return a * p
        */
        polynomial * mul(numeral const & a, polynomial const * p);    
        polynomial * mul(rational const & a, polynomial const * p);    
        
        /**
           \brief Return p1 * p2
        */
        polynomial * mul(polynomial const * p1, polynomial const * p2);    

        /**
           \brief Return m1 * m2
        */
        monomial * mul(monomial const * m1, monomial const * m2);

        /**
           \brief Return a * m * p
        */
        polynomial * mul(numeral const & a, monomial const * m, polynomial const * p);

        /**
           \brief Return m * p
        */
        polynomial * mul(monomial const * m, polynomial const * p);
        
        /**
           \brief Return true if m2 divides m1
        */
        bool div(monomial const * m1, monomial const * m2);

        /**
           \brief Return true if m2 divides m1, and store the result in r.
        */
        bool div(monomial const * m1, monomial const * m2, monomial * & r);

        /**
           \brief Newton interpolation algorithm for multivariate polynomials.
        */
        void newton_interpolation(var x, unsigned d, numeral const * inputs, polynomial * const * outputs, polynomial_ref & r);

        /**
           \brief Return the GCD of m1 and m2.
           Store in q1 and q2 monomials s.t.
           m1 = gcd * q1
           m2 = gcd * q2
        */
        monomial * gcd(monomial const * m1, monomial const * m2, monomial * & q1, monomial * & q2);

        /**
           \brief Return true if the gcd of m1 and m2 is not 1.
           In that case, store in q1 and q2 monomials s.t.
           m1 = gcd * q1
           m2 = gcd * q2
        */
        bool unify(monomial const * m1, monomial const * m2, monomial * & q1, monomial * & q2);

        /**
           \brief Return m^k
        */
        monomial * pw(monomial const * m, unsigned k);
        
        /**
           \brief Return the polynomial p^k
        */
        void pw(polynomial const * p, unsigned k, polynomial_ref & r);
       
        /**
           \brief Return dp/dx
        */
        polynomial * derivative(polynomial const * p, var x);

        /**
           \brief r := square free part of p with respect to x
        */
        void square_free(polynomial const * p, var x, polynomial_ref & r);

        /**
           \brief Return true if p is square free with respect to x
        */
        bool is_square_free(polynomial const * p, var x);

        /**
           \brief r := square free part of p 
        */
        void square_free(polynomial const * p, polynomial_ref & r);

        /**
           \brief Return true if p is square free
        */
        bool is_square_free(polynomial const * p);
        
        /**
           \brief Return true if p1 == p2.
        */
        bool eq(polynomial const * p1, polynomial const * p2);

        /**
           \brief Rename variables using the given permutation.

           sz must be num_vars()
        */
        void rename(unsigned sz, var const * xs);

        /**
           \brief Given an univariate polynomial p(x), 
           return the polynomial  x^n * p(1/x), where n = degree(p)
           
           If u is a nonzero root of p, then 1/u is a root the resultant polynomial.
        */
        polynomial * compose_1_div_x(polynomial const * p);

        /**
           \brief Given an univariate polynomial p(x), 
           return the polynomial  y^n * p(x/y), where n = degree(p)
        */
        polynomial * compose_x_div_y(polynomial const * p, var y);

        /**
           \brief Given an univariate polynomial p(x), return p(-x)
        */
        polynomial * compose_minus_x(polynomial const * p);
        
        /**
           \brief Given an univariate polynomial p(x) and a polynomial q(y_1, ..., y_n),
           return a polynomial r(y_1, ..., y_n) = p(q(y_1, ..., y_n)).
        */
        void compose(polynomial const * p, polynomial const * q, polynomial_ref & r);

        /**
           \brief Given an univariate polynomial p(x), return the polynomial r(y) = p(y)
        */
        polynomial * compose_y(polynomial const * p, var y);

        /**
           \brief Given an univariate polynomial p(x), return the polynomial r(x, y) = p(x - y).
           The result is stored in r.
        */
        void compose_x_minus_y(polynomial const * p, var y, polynomial_ref & r);

        /**
           \brief Given an univariate polynomial p(x), return the polynomial r(x, y) = p(x + y).
           The result is stored in r.
        */
        void compose_x_plus_y(polynomial const * p, var y, polynomial_ref & r);

        /**
           \brief Given an univariate polynomial p(x), return the polynomial r(x) = p(x - c).
           The result is stored in r.
        */
        void compose_x_minus_c(polynomial const * p, numeral const & c, polynomial_ref & r);
        
        /**
           \brief Return the exact pseudo remainder of p by q, assuming x is the maximal variable.
           
           See comments at pseudo_division_core at polynomial.cpp for a description of exact pseudo division.
        */
        void exact_pseudo_remainder(polynomial const * p, polynomial const * q, var x, polynomial_ref & R);

        void exact_pseudo_remainder(polynomial const * p, polynomial const * q, polynomial_ref & R) {
            exact_pseudo_remainder(p, q, max_var(q), R);
        }

        /**
           \brief Return the pseudo remainder of p by q, assuming x is the maximal variable.
           
           See comments at pseudo_division_core at polynomial.cpp for a description of exact pseudo division.
        */
        void pseudo_remainder(polynomial const * p, polynomial const * q, var x, unsigned & d, polynomial_ref & R);

        void pseudo_remainder(polynomial const * p, polynomial const * q, unsigned & d, polynomial_ref & R) {
            pseudo_remainder(p, q, max_var(q), d, R);
        }

        /**
           \brief Return the exact pseudo division quotient and remainder.
           
           See comments at pseudo_division_core at polynomial.cpp for a description of exact pseudo division.
        */
        void exact_pseudo_division(polynomial const * p, polynomial const * q, var x, polynomial_ref & Q, polynomial_ref & R);

        void exact_pseudo_division(polynomial const * p, polynomial const * q, polynomial_ref & Q, polynomial_ref & R) {
            exact_pseudo_division(p, q, max_var(q), Q, R);
        }

        /**
           \brief Return the pseudo division quotient and remainder.
           
           See comments at pseudo_division_core at polynomial.cpp for a description of exact pseudo division.
        */
        void pseudo_division(polynomial const * p, polynomial const * q, var x, unsigned & d, polynomial_ref & Q, polynomial_ref & R);
        
        void pseudo_division(polynomial const * p, polynomial const * q, unsigned & d, polynomial_ref & Q, polynomial_ref & R) {
            pseudo_division(p, q, max_var(q), d, Q, R);
        }

        /**
           \brief Return p/q if q divides p.

           \pre q divides p.
           
           \remark p and q may be multivariate polynomials.
        */
        polynomial * exact_div(polynomial const * p, polynomial const * q);

        /**
           \brief Return true if q divides p.
        */
        bool divides(polynomial const * q, polynomial const * p);

        /**
           \brief Return p/c if c divides p.

           \pre c divides p.
           
           \remark p may be multivariate polynomial.
        */
        polynomial * exact_div(polynomial const * p, numeral const & c);

        /**
           \brief Store in r the quasi-resultant of p and q with respect to variable x.
           
           Assume p and q are polynomials in Q[y_1, ..., y_n, x].
           Then r is a polynomial in Q[y_1, ..., y_n].
           Moreover, Forall a_1, ..., a_n, b,  
                   if p(a_1, ..., a_n, b) = q(a_1, ..., a_n, b) = 0
                   then r(a_1, ..., a_n) = 0

           \pre p and q must contain x.        
           
           \remark if r is the zero polynomial, then for any complex numbers a_1, ..., a_n,
           the univariate polynomials p(a_1, ..., a_n, x) and q(a_1, ..., a_n, x) in C[x] have
           a common root. C is the field of the complex numbers.
        */
        void quasi_resultant(polynomial const * p, polynomial const * q, var x, polynomial_ref & r);
        
        /**
           \brief Store in r the resultant of p and q with respect to variable x.
           See comments in polynomial.cpp for more details
        */
        void resultant(polynomial const * p, polynomial const * q, var x, polynomial_ref & r);
        
        /**
           \brief Store in r the discriminant of p with respect to variable x.
           discriminant(p, x, r) == resultant(p, derivative(p, x), x, r)
        */
        void discriminant(polynomial const * p, var x, polynomial_ref & r);

        /**
           \brief Store in S the principal subresultant coefficients for p and q.
        */
        void psc_chain(polynomial const * p, polynomial const * q, var x, polynomial_ref_vector & S);
        
        /**
           \brief Make sure the GCD of the coefficients is one.

           Make sure that the polynomial is a member of the polynomial ring of this manager.
           If manager is Z_p[X1, ..., Xn], and polynomial is in Z[X1, ..., Xn] return a new
           one where all coefficients are in Z_p
        */
        polynomial * normalize(polynomial const * p);
        
        /**
           \brief Return true if p is a square, and store its square root in r.
        */
        bool sqrt(polynomial const * p, polynomial_ref & r);
       

        /**
           \brief obtain the sign of the polynomial given sign of variables.
        */
        lbool sign(polynomial const* p, svector<lbool> const& sign_of_vars);
 
        /**
           \brief Return true if p is always positive for any assignment of its variables.
           
           This is an incomplete check. This method just check if all monomials are powers of two,
           and the coefficients are positive.
        */
        bool is_pos(polynomial const * p);

        /**
           \brief Return true if p is always negative for any assignment of its variables.
           
           This is an incomplete check.
        */
        bool is_neg(polynomial const * p);

        /**
           \brief Return true if p is always non-positive for any assignment of its variables.

           This is an incomplete check.
        */
        bool is_nonpos(polynomial const * p);

        /**
           \brief Return true if p is always non-negative for any assignment of its variables.

           This is an incomplete check.
        */
        bool is_nonneg(polynomial const * p);

        /**
           \brief Make sure the monomials in p are sorted using lexicographical order.
           Remark: the maximal monomial is at position 0.
        */
        void lex_sort(polynomial * p);

        /**
           \brief Collect variables that occur in p into xs
        */
        void vars(polynomial const * p, var_vector & xs);

        /**
           \brief Evaluate polynomial p using the assignment [x_1 -> v_1, ..., x_n -> v_n].
           The result is store in r.
           All variables occurring in p must be in xs.
        */
        void eval(polynomial const * p, var2mpbqi const & x2v, mpbqi & r);
        void eval(polynomial const * p, var2mpq const & x2v, mpq & r);
        void eval(polynomial const * p, var2anum const & x2v, algebraic_numbers::anum & r);

        /**
           \brief Apply substitution [x_1 -> v_1, ..., x_n -> v_n].
           That is, given p \in Z[x_1, ..., x_n, y_1, ..., y_m] return a polynomial
           r \in Z[y_1, ..., y_m].
           Moreover forall a_1, ..., a_m in Q
              sign(r(a_1, ..., a_m)) == sign(p(v_1, ..., v_n, a_1, ..., a_m))
        */
        polynomial * substitute(polynomial const * p, var2mpq const & x2v);
        polynomial * substitute(polynomial const * p, unsigned xs_sz, var const * xs, mpq const * vs);
        
        /**
           \brief Apply substitution [x_1 -> v_1, ..., x_n -> v_n].
           That is, given p \in Z[x_1, ..., x_n, y_1, ..., y_m] return 
           polynomial r(y_1, ..., y_m) = p(v_1, ..., v_n, y_1, ..., y_m) in Z[y_1, ..., y_m].
        */
        polynomial * substitute(polynomial const * p, unsigned xs_sz, var const * xs, numeral const * vs);

        /**
           \brief Apply substitution [x -> v].
           That is, given p \in Z[x, y_1, ..., y_m] return 
           polynomial r(y_1, ..., y_m) = p(v, y_1, ..., y_m) in Z[y_1, ..., y_m].
        */
        polynomial * substitute(polynomial const * p, var x, numeral const & v) {
            return substitute(p, 1, &x, &v);
        }

        /**
           \brief Apply substitution [x -> p/q] in r.
           That is, given r \in Z[x, y_1, .., y_m] return
           polynomial q^k * r(p/q, y_1, .., y_m), where k is the maximal degree of x in r.
        */
        void substitute(polynomial const* r, var x, polynomial const* p, polynomial const* q, polynomial_ref& result);

        /**
           \brief Factorize the given polynomial p and store its factors in r.
        */
        void factor(polynomial const * p, factors & r, factor_params const & params = factor_params());

        /**
           \brief Dense univariate polynomial to sparse polynomial. 
        */
        polynomial * to_polynomial(unsigned sz, numeral const * p, var x);
        polynomial * to_polynomial(numeral_vector const & p, var x) {
            return to_polynomial(p.size(), p.c_ptr(), x);
        }
       
        /**
           \brief Make the leading monomial (with respect to graded lexicographical order) monic.
           
           \pre numeral_manager must be a field.
        */
        polynomial * mk_glex_monic(polynomial const * p);

        /**
           \brief Return p'(y_1, ..., y_n, x) = p(y_1, ..., y_n, x + v)
        */
        polynomial * translate(polynomial const * p, var x, numeral const & v);
        
        /**
           \brief Store p'(y_1, ..., y_n, x_1, ..., x_m) = p(y_1, ..., y_n, x_1 + v_1, ..., x_m + v_m)
           into r.
        */
        void translate(polynomial const * p, unsigned xs_sz, var const * xs, numeral const * vs, polynomial_ref & r);
        void translate(polynomial const * p, var_vector const & xs, numeral_vector const & vs, polynomial_ref & r) {
            SASSERT(xs.size() == vs.size());
            translate(p, xs.size(), xs.c_ptr(), vs.c_ptr(), r); 
        }

        /**
           \brief Remove monomials m if it contains x^k and x2d[x] >= k
        */
        polynomial * mod_d(polynomial const * p, var2degree const & x2d);
        
        /**
           \brief (exact) Pseudo division modulo var->degree mapping.
        */
        void exact_pseudo_division_mod_d(polynomial const * p, polynomial const * q, var x, var2degree const & x2d, polynomial_ref & Q, polynomial_ref & R);

        void display(std::ostream & out, monomial const * m, display_var_proc const & proc = display_var_proc(), bool use_star = true) const;

        void display(std::ostream & out, polynomial const * p, display_var_proc const & proc = display_var_proc(), bool use_star = false) const;

        void display_smt2(std::ostream & out, polynomial const * p, display_var_proc const & proc = display_var_proc()) const;

        friend std::ostream & operator<<(std::ostream & out, polynomial_ref const & p) {
            p.m().display(out, p);
            return out;
        }
    };

    typedef manager::factors factors;
    typedef manager::numeral numeral;
    typedef manager::numeral_manager numeral_manager;
    typedef manager::scoped_numeral scoped_numeral;
    typedef manager::scoped_numeral_vector scoped_numeral_vector; 

    class scoped_set_z {
        manager &      m;
        bool           m_modular;
        scoped_numeral m_p;
    public:
        scoped_set_z(manager & _m):m(_m), m_modular(m.modular()), m_p(m.m()) {  m_p = m.p(); m.set_z(); }
        ~scoped_set_z() {  if (m_modular) m.set_zp(m_p); }
    };

    class scoped_set_zp {
        manager &      m;
        bool           m_modular;
        scoped_numeral m_p;
    public:
        scoped_set_zp(manager & _m, numeral const & p):m(_m), m_modular(m.modular()), m_p(m.m()) {  m_p = m.p(); m.set_zp(p); }
        scoped_set_zp(manager & _m, uint64_t p):m(_m), m_modular(m.modular()), m_p(m.m()) {  m_p = m.p(); m.set_zp(p); }
        ~scoped_set_zp() {  if (m_modular) m.set_zp(m_p); else m.set_z(); }
    };
};

typedef polynomial::polynomial_ref           polynomial_ref;
typedef polynomial::polynomial_ref_vector    polynomial_ref_vector;

polynomial::polynomial * convert(polynomial::manager & sm, polynomial::polynomial * p, polynomial::manager & tm, 
                                 polynomial::var x = polynomial::null_var, unsigned max_d = UINT_MAX);

inline polynomial::polynomial * convert(polynomial::manager & sm, polynomial_ref const & p, polynomial::manager & tm) {
    SASSERT(&sm == &(p.m()));
    return convert(sm, p.get(), tm);
}

inline polynomial_ref neg(polynomial_ref const & p) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.neg(p), m);
}

inline polynomial_ref operator-(polynomial_ref const & p) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.neg(p), m);
}

inline polynomial_ref operator+(polynomial_ref const & p1, polynomial_ref const & p2) {
    polynomial::manager & m = p1.m();
    return polynomial_ref(m.add(p1, p2), m);
}

inline polynomial_ref operator+(polynomial_ref const & p1, int n) {
    polynomial::manager & m = p1.m();
    polynomial_ref tmp(m.mk_const(rational(n)), m);
    return p1 + tmp;
}

inline polynomial_ref operator+(polynomial_ref const & p1, rational const & n) {
    polynomial::manager & m = p1.m();
    polynomial_ref tmp(m.mk_const(n), m);
    return p1 + tmp;
}

inline polynomial_ref operator+(polynomial::numeral const & n, polynomial_ref const & p) {
    polynomial::manager & m = p.m();
    polynomial_ref tmp(m.mk_const(n), m);
    return p + tmp;
}

inline polynomial_ref operator+(polynomial_ref const & p, polynomial::numeral const & n) {
    return operator+(n, p);
}

inline polynomial_ref operator-(polynomial_ref const & p1, polynomial_ref const & p2) {
    polynomial::manager & m = p1.m();
    return polynomial_ref(m.sub(p1, p2), m);
}

inline polynomial_ref operator-(polynomial_ref const & p1, int n) {
    polynomial::manager & m = p1.m();
    polynomial_ref tmp(m.mk_const(rational(n)), m);
    return p1 - tmp;
}

inline polynomial_ref operator-(polynomial_ref const & p1, rational const & n) {
    polynomial::manager & m = p1.m();
    polynomial_ref tmp(m.mk_const(n), m);
    return p1 - tmp;
}

inline polynomial_ref operator-(polynomial::numeral const & n, polynomial_ref const & p) {
    polynomial::manager & m = p.m();
    polynomial_ref tmp(m.mk_const(n), m);
    return p - tmp;
}

inline polynomial_ref operator-(polynomial_ref const & p, polynomial::numeral const & n) {
    return operator-(n, p);
}

inline polynomial_ref operator*(polynomial_ref const & p1, polynomial_ref const & p2) {
    polynomial::manager & m = p1.m();
    return polynomial_ref(m.mul(p1, p2), m);
}

inline polynomial_ref operator*(rational const & n, polynomial_ref const & p) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.mul(n, p), m);
}

inline polynomial_ref operator*(int n, polynomial_ref const & p) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.mul(rational(n), p), m);
}

inline polynomial_ref operator*(polynomial::numeral const & n, polynomial_ref const & p) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.mul(n, p), m);
}

inline polynomial_ref operator*(polynomial_ref const & p, polynomial::numeral const & n) {
    return operator*(n, p);
}

inline bool eq(polynomial_ref const & p1, polynomial_ref const & p2) {
    polynomial::manager & m = p1.m();
    return m.eq(p1, p2);
}

inline polynomial_ref operator^(polynomial_ref const & p, int k) {
    SASSERT(k > 0);
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.pw(p, k, r);
    return polynomial_ref(r);
}

inline polynomial_ref operator^(polynomial_ref const & p, unsigned k) {
    return operator^(p, static_cast<int>(k));
}

inline polynomial_ref derivative(polynomial_ref const & p, polynomial::var x) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.derivative(p, x), m);
}

inline bool is_zero(polynomial_ref const & p) {
    return p.m().is_zero(p);
}

inline bool is_const(polynomial_ref const & p) {
    return p.m().is_const(p);
}

inline bool is_linear(polynomial_ref const & p) {
    return p.m().is_linear(p);
}

inline bool is_univariate(polynomial_ref const & p) {
    return p.m().is_univariate(p);
}

inline unsigned total_degree(polynomial_ref const & p) {
    return p.m().total_degree(p);
}

inline polynomial::var max_var(polynomial_ref const & p) {
    return p.m().max_var(p);
}

inline unsigned degree(polynomial_ref const & p, polynomial::var x) {
    return p.m().degree(p, x);
}

inline unsigned size(polynomial_ref const & p) {
    return p.m().size(p);
}

inline polynomial_ref coeff(polynomial_ref const & p, polynomial::var x, unsigned k) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.coeff(p, x, k), m);
}

inline polynomial_ref lc(polynomial_ref const & p, polynomial::var x) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.coeff(p, x, degree(p, x)), m);
}

inline polynomial::numeral const & univ_coeff(polynomial_ref const & p, unsigned k) {
    return p.m().univ_coeff(p, k);
}

inline polynomial_ref content(polynomial_ref const & p, polynomial::var x) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.content(p, x, r);
    return r;
}

inline polynomial_ref primitive(polynomial_ref const & p, polynomial::var x) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.primitive(p, x, r);
    return r;
}

inline polynomial_ref gcd(polynomial_ref const & p, polynomial_ref const & q) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.gcd(p, q, r);
    return r;
}

inline bool is_square_free(polynomial_ref const & p, polynomial::var x) {
    return p.m().is_square_free(p, x);
}

inline polynomial_ref square_free(polynomial_ref const & p, polynomial::var x) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.square_free(p, x, r);
    return r;
}

inline bool is_square_free(polynomial_ref const & p) {
    return p.m().is_square_free(p);
}

inline polynomial_ref square_free(polynomial_ref const & p) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.square_free(p, r);
    return r;
}

inline polynomial_ref compose_y(polynomial_ref const & p, polynomial::var y) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.compose_y(p, y), m);
}

inline polynomial_ref compose_1_div_x(polynomial_ref const & p) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.compose_1_div_x(p), m);
}

inline polynomial_ref compose_x_div_y(polynomial_ref const & p, polynomial::var y) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.compose_x_div_y(p, y), m);
}

inline polynomial_ref compose_minus_x(polynomial_ref const & p) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.compose_minus_x(p), m);
}

inline polynomial_ref compose(polynomial_ref const & p, polynomial_ref const & g) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.compose(p, g, r);
    return polynomial_ref(r);
}

inline polynomial_ref compose_x_minus_y(polynomial_ref const & p, polynomial::var y) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.compose_x_minus_y(p, y, r);
    return polynomial_ref(r);
}

inline polynomial_ref compose_x_plus_y(polynomial_ref const & p, polynomial::var y) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.compose_x_plus_y(p, y, r);
    return polynomial_ref(r);
}

inline polynomial_ref compose_x_minus_c(polynomial_ref const & p, polynomial::numeral const & c) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.compose_x_minus_c(p, c, r);
    return polynomial_ref(r);
}

inline polynomial_ref exact_div(polynomial_ref const & p, polynomial_ref const & q) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.exact_div(p, q), m);
}

inline polynomial_ref normalize(polynomial_ref const & p) {
    polynomial::manager & m = p.m();
    return polynomial_ref(m.normalize(p), m);
}

inline bool sqrt(polynomial_ref const & p, polynomial_ref & r) {
    return p.m().sqrt(p, r);
}

inline polynomial_ref exact_pseudo_remainder(polynomial_ref const & p, polynomial_ref const & q, polynomial::var x) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.exact_pseudo_remainder(p, q, x, r);
    return polynomial_ref(r);
}

inline polynomial_ref exact_pseudo_remainder(polynomial_ref const & p, polynomial_ref const & q) {
    return exact_pseudo_remainder(p, q, max_var(q));
}

inline polynomial_ref pseudo_remainder(polynomial_ref const & p, polynomial_ref const & q, polynomial::var x, unsigned & d) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.pseudo_remainder(p, q, x, d, r);
    return polynomial_ref(r);
}

inline polynomial_ref pseudo_remainder(polynomial_ref const & p, polynomial_ref const & q, unsigned & d) {
    return pseudo_remainder(p, q, max_var(q), d);
}

inline polynomial_ref exact_pseudo_division(polynomial_ref const & p, polynomial_ref const & q, polynomial::var x, 
                                             polynomial_ref & R) {
    polynomial::manager & m = p.m();
    polynomial_ref Q(m);
    m.exact_pseudo_division(p, q, x, Q, R);
    return polynomial_ref(Q);
}

inline polynomial_ref exact_pseudo_division(polynomial_ref const & p, polynomial_ref const & q, polynomial_ref & R) {
    return exact_pseudo_division(p, q, max_var(q), R);
}

inline polynomial_ref pseudo_division(polynomial_ref const & p, polynomial_ref const & q, polynomial::var x, unsigned & d, polynomial_ref & R) {
    polynomial::manager & m = p.m();
    polynomial_ref Q(m);
    m.pseudo_division(p, q, x, d, Q, R);
    return polynomial_ref(Q);
}

inline polynomial_ref pseudo_division(polynomial_ref const & p, polynomial_ref const & q, unsigned & d, polynomial_ref & R) {
    return pseudo_division(p, q, max_var(q), d, R);
}

inline polynomial_ref quasi_resultant(polynomial_ref const & p, polynomial_ref const & q, unsigned x) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.quasi_resultant(p, q, x, r);
    return polynomial_ref(r);
}

inline polynomial_ref resultant(polynomial_ref const & p, polynomial_ref const & q, unsigned x) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.resultant(p, q, x, r);
    return polynomial_ref(r);
}

inline polynomial_ref discriminant(polynomial_ref const & p, unsigned x) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    m.discriminant(p, x, r);
    return polynomial_ref(r);
}

inline bool is_pos(polynomial_ref const & p) {
    return p.m().is_pos(p);
}

inline bool is_neg(polynomial_ref const & p) {
    return p.m().is_neg(p);
}

inline bool is_nonpos(polynomial_ref const & p) {
    return p.m().is_nonpos(p);
}

inline bool is_nonneg(polynomial_ref const & p) {
    return p.m().is_nonneg(p);
}

inline void factor(polynomial_ref const & p, polynomial::factors & r, polynomial::factor_params const & params = polynomial::factor_params()) {
    p.m().factor(p, r, params);
}

std::ostream & operator<<(std::ostream & out, polynomial_ref_vector const & seq);

#endif
