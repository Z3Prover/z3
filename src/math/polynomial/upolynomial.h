/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    upolynomial.h

Abstract:

    Goodies for creating and handling univariate polynomials.
    
    A dense representation is much better for Root isolation algorithms, 
    encoding algebraic numbers, factorization, etc.

    We also use integers as the coefficients of univariate polynomials.
    
Author:

    Leonardo (leonardo) 2011-11-29

Notes:

--*/
#ifndef UPOLYNOMIAL_H_
#define UPOLYNOMIAL_H_

#include"mpzzp.h"
#include"rational.h"
#include"polynomial.h"
#include"z3_exception.h"
#include"mpbq.h"
#define FACTOR_VERBOSE_LVL 1000

namespace upolynomial {
    
    typedef polynomial::factor_params factor_params;

    // It is used only for signing cancellation.
    class upolynomial_exception : public default_exception {
    public:
        upolynomial_exception(char const * msg):default_exception(msg) {}
    };

    typedef mpz                                     numeral;
    typedef mpzzp_manager                           numeral_manager;
    typedef mpzzp_manager                           zp_numeral_manager;
    typedef unsynch_mpz_manager                     z_numeral_manager;
    typedef svector<numeral>                        numeral_vector;
    
    class core_manager {
    public:
        typedef _scoped_numeral_vector<numeral_manager> scoped_numeral_vector;
        typedef _scoped_numeral<numeral_manager>        scoped_numeral;
        /**
           \brief Convenient vector of polynomials that manages its own memory and keeps the degree, of each polynomial.
           Polynomial is c*f_1^k_1*...*f_n^k_n.
        */
        class factors {
        private:
            vector<numeral_vector> m_factors;
            svector<unsigned>      m_degrees;
            core_manager &         m_upm;
            numeral                m_constant;
            unsigned               m_total_factors;
            unsigned               m_total_degree;
        public:
            factors(core_manager & upm);
            ~factors();

            core_manager & upm() const { return m_upm; }
            core_manager & pm() const { return m_upm; }
            numeral_manager & nm() const;
            
            unsigned distinct_factors() const { return m_factors.size(); }
            unsigned total_factors() const { return m_total_factors; }
            void clear();
            void reset() { clear(); }

            numeral_vector const & operator[](unsigned i) const { return m_factors[i]; }        
            
            numeral const & get_constant() const { return m_constant; }
            void set_constant(numeral const & constant);
            
            unsigned get_degree() const { return m_total_degree; }
            unsigned get_degree(unsigned i) const { return m_degrees[i]; }
            void set_degree(unsigned i, unsigned degree);
            void push_back(numeral_vector const & p, unsigned degree);        
            // push p to vectors and kill it
            void push_back_swap(numeral_vector & p, unsigned degree);
            
            void swap_factor(unsigned i, numeral_vector & p);
            void swap(factors & other);
            void multiply(numeral_vector & out) const; 
            
            void display(std::ostream & out) const;

            friend std::ostream & operator<<(std::ostream & out, factors const & fs) {
                fs.display(out);
                return out;
            }
        };

    protected:
        numeral_manager   m_manager;
        numeral_vector    m_basic_tmp;
        numeral_vector    m_div_tmp1;
        numeral_vector    m_div_tmp2;
        numeral_vector    m_exact_div_tmp;
        numeral_vector    m_gcd_tmp1;
        numeral_vector    m_gcd_tmp2;
        numeral_vector    m_CRA_tmp;
        #define UPOLYNOMIAL_MGCD_TMPS 6
        numeral_vector    m_mgcd_tmp[UPOLYNOMIAL_MGCD_TMPS]; 
        numeral_vector    m_sqf_tmp1;
        numeral_vector    m_sqf_tmp2;
        numeral_vector    m_pw_tmp;
        volatile bool     m_cancel;

        static bool is_alias(numeral const * p, numeral_vector & buffer) { return buffer.c_ptr() != 0 && buffer.c_ptr() == p; }
        void neg_core(unsigned sz1, numeral const * p1, numeral_vector & buffer);
        void add_core(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer);
        void sub_core(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer);
        void mul_core(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer);

        void flip_sign_if_lm_neg(numeral_vector & buffer);

        void mod_gcd(unsigned sz_u, numeral const * u, unsigned sz_v, numeral const * v, numeral_vector & result);
        void CRA_combine_images(numeral_vector const & q, numeral const & p, numeral_vector & C, numeral & bound);

    public:
        core_manager(z_numeral_manager & m);
        ~core_manager();

        z_numeral_manager & zm() const { return m_manager.m(); }
        numeral_manager & m() const { return const_cast<core_manager*>(this)->m_manager; }

        /**
           \brief Return true if Z_p[X]
        */
        bool modular() const { return m().modular(); }
        bool field() const { return m().field(); }
        /**
           \brief Return p in Z_p[X]
           \pre modular
        */
        numeral const & p() const { return m().p(); }
        /**
           \brief Set manager as Z[X]
        */
        void set_z() { m().set_z(); }
        /**
           \brief Set manager as Z_p[X]
        */
        void set_zp(numeral const & p) { m().set_zp(p); }
        void set_zp(uint64 p) { m().set_zp(p); }

        void checkpoint();

        void set_cancel(bool f);

        /**
           \brief set p size to 0. That is, p is the zero polynomial after this operation.
        */
        void reset(numeral_vector & p);
        
        /**
           \brief Remove zero leading coefficients. 
           After applying this method, we have that p is empty() or p[p.size()-1] is not zero.
        */
        void trim(numeral_vector & p);
        
        void set_size(unsigned sz, numeral_vector & buffer);

        /**
           \brief Return the actual degree of p.
        */
        unsigned degree(numeral_vector const & p) { 
            unsigned sz = p.size();
            return sz == 0 ? 0 : sz - 1;
        }

        /**
           \brief Return true if p is the zero polynomial.
        */
        bool is_zero(numeral_vector & p) { trim(p); return p.empty(); }

        /**
           \brief Return true if p is a constant polynomial
        */
        bool is_const(numeral_vector & p) { trim(p); return p.size() <= 1; }

        /**
           \brief Copy p to buffer.
        */
        void set(unsigned sz, numeral const * p, numeral_vector & buffer);
        void set(numeral_vector & target, numeral_vector const & source) { set(source.size(), source.c_ptr(), target);  }

        /**
           \brief Copy p to buffer.
           
           Coefficients of p must be integer.
        */
        void set(unsigned sz, rational const * p, numeral_vector & buffer);

        /**
            \brief Compute the primitive part and the content of f (pp can alias f).
        */
        void get_primitive_and_content(unsigned f_sz, numeral const * f, numeral_vector & pp, numeral & cont);
        void get_primitive_and_content(numeral_vector const & f, numeral_vector & pp, numeral & cont) {
            get_primitive_and_content(f.size(), f.c_ptr(), pp, cont);
        }
        void get_primitive(numeral_vector const & f, numeral_vector & pp) { 
            scoped_numeral cont(m());
            get_primitive_and_content(f.size(), f.c_ptr(), pp, cont);
        }

        /**
           \brief p := -p
        */
        void neg(unsigned sz, numeral * p);
        void neg(numeral_vector & p) { neg(p.size(), p.c_ptr()); }

        /**
           \brief buffer := -p
        */
        void neg(unsigned sz, numeral const * p, numeral_vector & buffer);
        void neg(numeral_vector const & p, numeral_vector & p_neg) { neg(p.size(), p.c_ptr(), p_neg); }

        /**
           \brief buffer := p1 + p2
        */
        void add(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer);
        void add(numeral_vector const & a, numeral_vector const & b, numeral_vector & c) { add(a.size(), a.c_ptr(), b.size(), b.c_ptr(), c); }

        /**
           \brief buffer := p1 - p2
        */
        void sub(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer);
        void sub(numeral_vector const & a, numeral_vector const & b, numeral_vector & c) { sub(a.size(), a.c_ptr(), b.size(), b.c_ptr(), c); }

        /**
           \brief buffer := p1 * p2
        */
        void mul(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & buffer);
        void mul(numeral_vector const & a, numeral_vector const & b, numeral_vector & c) { mul(a.size(), a.c_ptr(), b.size(), b.c_ptr(), c); }

        /**
           \brief r := p^k
        */
        void pw(unsigned sz, numeral const * p, unsigned k, numeral_vector & r);

        /**
           \brief buffer := dp/dx
        */
        void derivative(unsigned sz1, numeral const * p, numeral_vector & buffer);
        void derivative(numeral_vector const & p, numeral_vector & d_p) { derivative(p.size(), p.c_ptr(), d_p); }

        /**
           \brief Divide coeffients of p by their GCD
        */
        void normalize(unsigned sz, numeral * p);
        
        /**
           \brief Divide coeffients of p by their GCD
        */
        void normalize(numeral_vector & p);

        /**
           \brief Divide the coefficients of p by b.
           This method assumes that every coefficient of p is a multiple of b, and b != 0.
        */
        void div(unsigned sz, numeral * p, numeral const & b);
        void div(numeral_vector & p, numeral const & b) { div(p.size(), p.c_ptr(), b); }

        /**
           \brief Multiply the coefficients of p by b. 
           
           This method assume b != 0.
        */
        void mul(unsigned sz, numeral * p, numeral const & b);

        /**
           \brief Multiply the coefficients of p by b.
           If b == 0, it is equivalent to a reset()
        */
        void mul(numeral_vector & p, numeral const & b);

        /**
           \brief Similar to div_rem but p1 and p2 must not be q and r.
        */
        void div_rem_core(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, unsigned & d, numeral_vector & q, numeral_vector & r);

        /**
           \brief If numeral is a field, then
           return q and r s.t. p1 = q*p2 + r
           And degree(r) < degree(p2).
           
           If numeral is not a field, then 
           return q and r s.t.  (b_m)^d * p1 = q * p2 + r
           where b_m is the leading coefficient of p2 and d <= sz1 - sz2 + 1 
           if sz1 >= sz2.

           The output value d is irrelevant if numeral is a field.
        */
        void div_rem(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, unsigned & d, numeral_vector & q, numeral_vector & r);

        /**
           \see div_rem
        */
        void div_rem(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & q, numeral_vector & r) {
            unsigned d = 0;
            div_rem(sz1, p1, sz2, p2, d, q, r);
        }
        
        void div_rem(numeral_vector const & p1, numeral_vector const & p2, numeral_vector & q, numeral_vector & r) { 
            div_rem(p1.size(), p1.c_ptr(), p2.size(), p2.c_ptr(), q, r);
        }

        /**
           \see div_rem
        */
        void div(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & q);

        /**
           \see div_rem
        */
        void rem(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, unsigned & d, numeral_vector & r);

        /**
           \see div_rem
        */
        void rem(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & r) {
            unsigned d = 0;
            rem(sz1, p1, sz2, p2, d, r);
        }

        /**
           \brief Signed pseudo-remainder. 
           Alias for rem(sz1, p1, sz2, p2, r); neg(r);
        */
        void srem(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & r);

        /**
           \brief Return true if p2 divides p1.
        */
        bool divides(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2);
        bool divides(numeral_vector const & p1, numeral_vector const & p2) { return divides(p1.size(), p1.c_ptr(), p2.size(), p2.c_ptr()); }

        /**
           \brief Return true if p2 divides p1, and store the quotient in q.
        */
        bool exact_div(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & q);
        bool exact_div(numeral_vector const & p1, numeral_vector const & p2, numeral_vector & q) {
            return exact_div(p1.size(), p1.c_ptr(), p2.size(), p2.c_ptr(), q);
        }

        /**
           \brief Assuming that we can, make the polynomial monic by dividing with the leading coefficient. It
           puts the leading coefficient into lc, and it's inverse into lc_inv.           
        */
        void mk_monic(unsigned sz, numeral * p, numeral & lc, numeral & lc_inv);        
        void mk_monic(unsigned sz, numeral * p, numeral & lc) { numeral lc_inv; mk_monic(sz, p, lc, lc_inv); m().del(lc_inv); }
        void mk_monic(unsigned sz, numeral * p) { numeral lc, lc_inv; mk_monic(sz, p, lc, lc_inv); m().del(lc); m().del(lc_inv); }
        void mk_monic(numeral_vector & p) { mk_monic(p.size(), p.c_ptr()); }

        /**
           \brief g := gcd(p1, p2)
           If in a field the coefficients don't matter, so we also make sure that D is monic.
        */
        void gcd(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & g);
        void euclid_gcd(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & g);
        void subresultant_gcd(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, numeral_vector & g);
        void gcd(numeral_vector const & p1, numeral_vector const & p2, numeral_vector & g) {
            gcd(p1.size(), p1.c_ptr(), p2.size(), p2.c_ptr(), g);
        }
        void subresultant_gcd(numeral_vector const & p1, numeral_vector const & p2, numeral_vector & g) {
            subresultant_gcd(p1.size(), p1.c_ptr(), p2.size(), p2.c_ptr(), g);
        }
        
        /**
           \brief g := square free part of p
        */
        void square_free(unsigned sz, numeral const * p, numeral_vector & g);

        /**
           \brief Return true if p is a square-free polynomial.
        */
        bool is_square_free(unsigned sz, numeral const * p);

        /**
           \brief Return true if p is a square-free polynomial.
        */
        bool is_square_free(numeral_vector const & p) {
            return is_square_free(p.size(), p.c_ptr());
        }

        /**
           \brief Convert a multi-variate polynomial (that is) actually representing an univariate polynomial
           into a vector of coefficients.
        */
        template<typename polynomial_ref>
        void to_numeral_vector(polynomial_ref const & p, numeral_vector & r) {
            typename polynomial_ref::manager & pm = p.m();
            SASSERT(pm.is_univariate(p));
            polynomial_ref np(pm);
            np = pm.normalize(p);
            unsigned sz  = pm.size(p);
            unsigned deg = pm.total_degree(p);
            r.reserve(deg+1);
            for (unsigned i = 0; i <= deg; i++) {
                m().reset(r[i]);
            }
            for (unsigned i = 0; i < sz; i++) {
                unsigned k = pm.total_degree(pm.get_monomial(p, i));
                SASSERT(k <= deg);
                m().set(r[k], pm.coeff(p, i));
            }
            set_size(deg+1, r);
        }

        /**
           \brief Convert a multi-variate polynomial in [x, y1, ..., yn] to a univariate polynomial in just x 
           by removing everything multivariate.
        */
        template<typename polynomial_ref>
        void to_numeral_vector(polynomial_ref const & p, polynomial::var x, numeral_vector & r) {
            typename polynomial_ref::manager & pm = p.m();            
            polynomial_ref np(pm);
            np = pm.normalize(p);
            unsigned sz  = pm.size(p);
            unsigned deg = pm.degree(p, x);
            r.reserve(deg+1);
            for (unsigned i = 0; i <= deg; i++) {
                m().reset(r[i]);
            }
            for (unsigned i = 0; i < sz; i++) {
				typename polynomial::monomial * mon = pm.get_monomial(p, i);
				if (pm.size(mon) == 0) {
                    m().set(r[0], pm.coeff(p, i));
				} else if (pm.size(mon) == 1 && pm.get_var(mon, 0) == x) {
					unsigned m_deg_x = pm.degree(mon, 0);
                    m().set(r[m_deg_x], pm.coeff(p, i));
                }
            }
            set_size(deg+1, r);
        }

        /**
           \brief Extended GCD 
           This method assumes that numeral is a field.
           It determines U, V, D such that
           A*U + B*V = D and D is the GCD of A and B.
           Since in a field the coefficients don't matter, we also make sure that D is monic.
        */
        void ext_gcd(unsigned szA, numeral const * A, unsigned szB, numeral const * B, numeral_vector & U, numeral_vector & V, numeral_vector & D);
        void ext_gcd(numeral_vector const & A, numeral_vector const & B, numeral_vector & U, numeral_vector & V, numeral_vector & D) {
            ext_gcd(A.size(), A.c_ptr(), B.size(), B.c_ptr(), U, V, D);
        }

        bool eq(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2);
        bool eq(numeral_vector const & p1, numeral_vector const & p2) { return eq(p1.size(), p1.c_ptr(), p2.size(), p2.c_ptr()); }

        void display(std::ostream & out, unsigned sz, numeral const * p, char const * var_name = "x", bool use_star = false) const;
        void display(std::ostream & out, numeral_vector const & p, char const * var_name = "x") const { display(out, p.size(), p.c_ptr(), var_name); }
        void display_star(std::ostream & out, unsigned sz, numeral const * p) { display(out, sz, p, "x", true); }
        void display_star(std::ostream & out, numeral_vector const & p) { display_star(out, p.size(), p.c_ptr()); }

        void display_smt2(std::ostream & out, unsigned sz, numeral const * p, char const * var_name = "x") const;
        void display_smt2(std::ostream & out, numeral_vector const & p, char const * var_name = "x") const { 
            return display_smt2(out, p.size(), p.c_ptr(), var_name); 
        }
    };

    class scoped_set_z {
        core_manager & m;
        bool           m_modular;
        core_manager::scoped_numeral m_p;
    public:
        scoped_set_z(core_manager & _m):m(_m), m_modular(m.modular()), m_p(m.m()) {  m_p = m.p(); m.set_z(); }
        ~scoped_set_z() {  if (m_modular) m.set_zp(m_p); }
    };

    class scoped_set_zp {
        core_manager & m;
        bool           m_modular;
        core_manager::scoped_numeral m_p;
    public:
        scoped_set_zp(core_manager & _m, numeral const & p):m(_m), m_modular(m.modular()), m_p(m.m()) {  m_p = m.p(); m.set_zp(p); }
        scoped_set_zp(core_manager & _m, uint64 p):m(_m), m_modular(m.modular()), m_p(m.m()) {  m_p = m.p(); m.set_zp(p); }
        ~scoped_set_zp() {  if (m_modular) m.set_zp(m_p); else m.set_z(); }
    };

    class manager;

    typedef core_manager    z_manager;
    typedef core_manager    zp_manager;

    typedef z_manager::factors  factors;
    typedef zp_manager::factors zp_factors;
    
    typedef svector<numeral> numeral_vector;

    class scoped_numeral_vector : public _scoped_numeral_vector<numeral_manager> {
    public:
        scoped_numeral_vector(numeral_manager & m):_scoped_numeral_vector<numeral_manager>(m) {}
        scoped_numeral_vector(manager & m);
    };

    class upolynomial_sequence {
        numeral_vector     m_seq_coeffs; // coefficients of all polynomials in the sequence
        unsigned_vector    m_begins;     // start position (in m_seq_coeffs) of each polynomial in the sequence
        unsigned_vector    m_szs;        // size of each polynomial in the sequence 
        friend class manager;
    public:
        /**
           \brief Add a new polynomial to the sequence.
           The contents of p is erased.
        */
        void push(unsigned sz, numeral * p);

        /**
           \brief Add a new polynomial to the sequence.
           The contents of p is preserved.
        */
        void push(numeral_manager & m, unsigned sz, numeral const * p);

        /**
           \brief Return the number of polynomials in the sequence.
        */
        unsigned size() const { return m_szs.size(); }
        
        /**
           \brief Return the vector of coefficients for the i-th polynomial in the sequence.
        */
        numeral const * coeffs(unsigned i) const { return m_seq_coeffs.c_ptr() + m_begins[i]; }
        
        /**
           \brief Return the size of the i-th polynomial in the sequence.
        */
        unsigned size(unsigned i) const { return m_szs[i]; }
    };

    class scoped_upolynomial_sequence : public upolynomial_sequence {
        manager & m_manager;
    public:
        scoped_upolynomial_sequence(manager & m):m_manager(m) {}
        ~scoped_upolynomial_sequence();
    };

    class manager : public core_manager {
        numeral_vector    m_db_tmp;
        numeral_vector    m_dbab_tmp1;
        numeral_vector    m_dbab_tmp2;
        numeral_vector    m_tr_tmp;
        numeral_vector    m_push_tmp;

        int sign_of(numeral const & c);
        struct drs_frame;
        void pop_top_frame(numeral_vector & p_stack, svector<drs_frame> & frame_stack);
        void push_child_frames(unsigned sz, numeral const * p, numeral_vector & p_stack, svector<drs_frame> & frame_stack);
        void add_isolating_interval(svector<drs_frame> const & frame_stack, mpbq_manager & bqm, mpbq_vector & lowers, mpbq_vector & uppers);
        void add_root(svector<drs_frame> const & frame_stack, mpbq_manager & bqm, mpbq_vector & roots);
        void drs_isolate_0_1_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers);
        void drs_isolate_roots(unsigned sz, numeral * p, numeral & U, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers);
        void drs_isolate_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers);
        void sqf_nz_isolate_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers);
        void sturm_seq_core(upolynomial_sequence & seq);
        enum location { PLUS_INF, MINUS_INF, ZERO, MPBQ };
        template<location loc>
        unsigned sign_variations_at_core(upolynomial_sequence const & seq, mpbq const & b);

        void flip_sign(factors & r);
        void flip_factor_sign_if_lm_neg(numeral_vector & p, factors & r, unsigned k);
        void factor_2_sqf_pp(numeral_vector & p, factors & r, unsigned k);
        bool factor_sqf_pp(numeral_vector & p, factors & r, unsigned k, factor_params const & params);
        bool factor_core(unsigned sz, numeral const * p, factors & r, factor_params const & params);

    public:
        manager(z_numeral_manager & m):core_manager(m) {}
        ~manager();

        void reset(numeral_vector & p) { core_manager::reset(p); }

        void reset(upolynomial_sequence & seq);

        /**
           \brief Return true if 0 is a root of p.
        */
        bool has_zero_roots(unsigned sz, numeral const * p) { SASSERT(sz > 0); return m().is_zero(p[0]); }

        /**
           \brief Store in buffer a polynomial that has the same roots of p but the zero roots.
           We have that:
                forall u, p(u) = 0 and u != 0 implies buffer(u) = 0
                forall u, buffer(u) = 0 implies p(u) = 0

           This method assumes p is not the zero polynomial     
        */
        void remove_zero_roots(unsigned sz, numeral const * p, numeral_vector & buffer);

        /**
           \brief Return true if 1/2 is a root of p.
        */
        bool has_one_half_root(unsigned sz, numeral const * p);

        /**
           \brief Store in buffer a polynomial that has the same roots of p, but a 1/2 root is removed.

           This method assumes that 1/2 is a root of p.
        */
        void remove_one_half_root(unsigned sz, numeral const * p, numeral_vector & buffer);

        /**
           \brief Return the number of sign changes in the coefficients of p.
           Zero coefficients are ignored.
        */
        unsigned sign_changes(unsigned sz, numeral const * p);
        
        /**
           \brief Return the descartes bound for the number of roots of p in the interval (0, +oo)

           Result:
           0   - p has no roots in (0,1)
           1   - p has one root in (0,1)
           >1  - p has more than one root in (0,1)
        */
        unsigned descartes_bound(unsigned sz, numeral const * p);

        /**
           \brief Return the descartes bound for the number of roots of p in the interval (0, 1)

           \see descartes_bound
        */
        unsigned descartes_bound_0_1(unsigned sz, numeral const * p);

        /**
           \brief Return the descartes bound for the number of roots of p in the interval (a, b)

           \see descartes_bound
        */
        unsigned descartes_bound_a_b(unsigned sz, numeral const * p, mpbq_manager & m, mpbq const & a, mpbq const & b);

        /**
           \brief p(x) := p(x+1)
        */
        void translate(unsigned sz, numeral * p);
        void translate(unsigned sz, numeral const * p, numeral_vector & buffer) { set(sz, p, buffer); translate(sz, buffer.c_ptr()); }
        
        /**
           \brief p(x) := p(x+2^k)
        */
        void translate_k(unsigned sz, numeral * p, unsigned k);
        void translate_k(unsigned sz, numeral const * p, unsigned k, numeral_vector & buffer) { set(sz, p, buffer); translate_k(sz, buffer.c_ptr(), k); }

        /**
           \brief p(x) := p(x+c)
        */
        void translate_z(unsigned sz, numeral * p, numeral const & c);
        void translate_z(unsigned sz, numeral const * p, numeral const & c, numeral_vector & buffer) { set(sz, p, buffer); translate_z(sz, buffer.c_ptr(), c); }

        /**
           \brief p(x) := p(x+b) where b = c/2^k 
           buffer := (2^k)^n * p(x + c/(2^k))
        */
        void translate_bq(unsigned sz, numeral * p, mpbq const & b);
        void translate_bq(unsigned sz, numeral const * p, mpbq const & b, numeral_vector & buffer) { set(sz, p, buffer); translate_bq(sz, buffer.c_ptr(), b); }
        
        /**
           \brief p(x) := p(x+b) where b = c/d
           buffer := d^n * p(x + c/d)
        */
        void translate_q(unsigned sz, numeral * p, mpq const & b);
        void translate_q(unsigned sz, numeral const * p, mpq const & b, numeral_vector & buffer) { set(sz, p, buffer); translate_q(sz, buffer.c_ptr(), b); }
        
        /**
           \brief p(x) := 2^n*p(x/2) where n = sz-1
        */
        void compose_2n_p_x_div_2(unsigned sz, numeral * p);

        /**
           \brief p(x) := (2^k)^n * p(x/(2^k))
        */
        void compose_2kn_p_x_div_2k(unsigned sz, numeral * p, unsigned k);

        /**
           \brief p(x) := p(2^k * x) 

           If u is a root of old(p), then u/2^k is a root of p
        */
        void compose_p_2k_x(unsigned sz, numeral * p, unsigned k);

        /**
           \brief p(x) := p(b * x) 

           If u is a root of old(p), then u/b is a root of p
        */
        void compose_p_b_x(unsigned sz, numeral * p, numeral const & b);
        
        /**
           \brief p(x) := p(b * x)
           
           If u is a root of old(p), then u/b is a root of p
           
           Let b be of the form c/(2^k), then this operation is equivalent to:
           (2^k)^n*p(c*x/(2^k))
          
           Let old(p) be of the form:
           a_n * x^n + a_{n-1}*x^{n-1} + ... + a_1 * x + a_0

           Then p is of the form:
           a_n * c^n * x^n + a_{n-1} * c^{n-1} * 2^k * x^{n-1} + ... + a_1 * c * (2^k)^(n-1) * x +  a_0
        */
        void compose_p_b_x(unsigned sz, numeral * p, mpbq const & b);

        /**
           \brief p(x) := p(q*x)
        */
        void compose_p_q_x(unsigned sz, numeral * p, mpq const & q);

        /**
           \brief p(x) := a^n * p(x/a)
        */
        void compose_an_p_x_div_a(unsigned sz, numeral * p, numeral const & a);

        /**
           \brief p(x) := p(-x)
        */
        void p_minus_x(unsigned sz, numeral * p);

        /**
           \brief p(x) := x^n * p(1/x)
        */
        void p_1_div_x(unsigned sz, numeral * p);
        
        /**
           \brief Evaluate the sign of p(b) 
        */
        int eval_sign_at(unsigned sz, numeral const * p, mpbq const & b);

        /**
           \brief Evaluate the sign of p(b)
        */
        int eval_sign_at(unsigned sz, numeral const * p, mpq const & b);

        /**
           \brief Evaluate the sign of p(b)
        */
        int eval_sign_at(unsigned sz, numeral const * p, mpz const & b);

        /**
           \brief Evaluate the sign of p(0)
        */
        int eval_sign_at_zero(unsigned sz, numeral const * p);

        /**
           \brief Evaluate the sign of p(+oo)
        */
        int eval_sign_at_plus_inf(unsigned sz, numeral const * p);

        /**
           \brief Evaluate the sign of p(-oo)
        */
        int eval_sign_at_minus_inf(unsigned sz, numeral const * p);

        /**
           \brief Evaluate the sign variations in the polynomial sequence at -oo
        */
        unsigned sign_variations_at_minus_inf(upolynomial_sequence const & seq);

        /**
           \brief Evaluate the sign variations in the polynomial sequence at +oo
        */
        unsigned sign_variations_at_plus_inf(upolynomial_sequence const & seq);

        /**
           \brief Evaluate the sign variations in the polynomial sequence at 0
        */
        unsigned sign_variations_at_zero(upolynomial_sequence const & seq);
        
        /**
           \brief Evaluate the sign variations in the polynomial sequence at b
        */
        unsigned sign_variations_at(upolynomial_sequence const & seq, mpbq const & b);

        /**
           \brief Return an upper bound U for all roots of p.
           U is a positive value.
           We have that if u is a root of p, then |u| < U
        */
        void root_upper_bound(unsigned sz, numeral const * p, numeral & U);
        
        unsigned knuth_positive_root_upper_bound(unsigned sz, numeral const * p);
        unsigned knuth_negative_root_upper_bound(unsigned sz, numeral const * p);

        /**
           \brief Return k s.t. for any nonzero root alpha of p(x):
                          |alpha| > 1/2^k
        */
        unsigned nonzero_root_lower_bound(unsigned sz, numeral const * p);

        /**
           \brief Isolate roots of a square free polynomial p.
           The result is stored in three vectors: roots, lowers and uppers.
           The vector roots contains actual roots of p.
           The vectors lowers and uppers have the same size, and
           For all i in [0, lowers.size()), we have that there is only and only one root of p in the interval (lowers[i], uppers[i]).
           Every root of p in roots or in an interval (lowers[i], uppers[i])

           The total number of roots of p is roots.size() + lowers.size()

           \pre p is not the zero polynomial, that is, sz > 0
        */
        void sqf_isolate_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers);
        
        /**
           \brief Isolate roots of an arbitrary polynomial p.

           \see sqf_isolate_roots.

           \pre p is not the zero polynomial, that is, sz > 0
        */
        void isolate_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers);

        void drs_isolate_roots(unsigned sz, numeral * p, unsigned neg_k, unsigned pos_k,
                               mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers);

        void sturm_isolate_roots_core(unsigned sz, numeral * p, unsigned neg_k, unsigned pos_k,
                                      mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers);

        void sturm_isolate_roots(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers);

        /**
           \brief Compute the sturm sequence for p1 and p2.
        */
        void sturm_seq(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, upolynomial_sequence & seq);

        /**
           \brief Compute the sturm sequence for p and p'.
        */
        void sturm_seq(unsigned sz, numeral const * p, upolynomial_sequence & seq);

        /**
           \brief Compute the sturm tarski sequence for p1 and p1'*p2.
        */
        void sturm_tarski_seq(unsigned sz1, numeral const * p1, unsigned sz2, numeral const * p2, upolynomial_sequence & seq);

        /**
           \brief Compute the Fourier sequence for p.
        */
        void fourier_seq(unsigned sz, numeral const * p, upolynomial_sequence & seq);
        
        /**
           \brief Convert an isolating interval into a refinable one.
           See comments in upolynomial.cpp.
        */
        bool isolating2refinable(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq & a, mpbq & b);

        //
        // Interval refinement procedures
        // They all assume p is square free and (a, b) is a refinable isolating interval.
        //
        // Return TRUE, if interval was squeezed, and new interval is stored in (a,b).
        // Return FALSE, if the actual root was found, it is stored in a.
        // 
        // See upolynomial.cpp for additional comments
        bool refine_core(unsigned sz, numeral const * p, int sign_a, mpbq_manager & bqm, mpbq & a, mpbq & b);
        
        bool refine(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq & a, mpbq & b);

        bool refine_core(unsigned sz, numeral const * p, int sign_a, mpbq_manager & bqm, mpbq & a, mpbq & b, unsigned prec_k);
        
        bool refine(unsigned sz, numeral const * p, mpbq_manager & bqm, mpbq & a, mpbq & b, unsigned prec_k);
        /////////////////////

        /**
           \brief Convert a isolating (refinable) rational interval into a 
           isolating refinable binary rational interval.

           Return TRUE,  if interval was found and the result is stored in (c, d).
           Return FALSE, if the actual root was found, it is stored in c.
        */
        bool convert_q2bq_interval(unsigned sz, numeral const * p, mpq const & a, mpq const & b, mpbq_manager & bqm, mpbq & c, mpbq & d);
        
        /**
           \brief Given a polynomial p, and a lower bound l. Return
           the root id i. That is, the first root u > l is the i-th root of p.
        */
        unsigned get_root_id(unsigned sz, numeral const * p, mpbq const & l);

        /**
           \brief Make sure that isolating interval (a, b) for p does not contain zero.
           
           Return TRUE, if updated (a, b) does not contain zero.
           Return FALSE, if zero is a root of p
        */
        bool normalize_interval_core(unsigned sz, numeral const * p, int sign_a, mpbq_manager & m, mpbq & a, mpbq & b);
        
        /**
           \brief Similar to normalize_interval_core, but sign_a does not need to be provided.
        */
        bool normalize_interval(unsigned sz, numeral const * p, mpbq_manager & m, mpbq & a, mpbq & b);

        /**
           \brief Return true if all irreducible factors were found.
           That is, if the result if false, there is no guarantee that the factors in r are irreducible.
           This can happen when limits (e.g., on the search space size) are set in params.
        */
        bool factor(unsigned sz, numeral const * p, factors & r, factor_params const & params = factor_params());
        bool factor(numeral_vector const & p, factors & r, factor_params const & params = factor_params()) { return factor(p.size(), p.c_ptr(), r, params); }

        void display(std::ostream & out, unsigned sz, numeral const * p, char const * var_name = "x", bool use_star = false) const { 
            return core_manager::display(out, sz, p, var_name); 
        }
        void display(std::ostream & out, numeral_vector const & p, char const * var_name = "x") const { 
            return core_manager::display(out, p, var_name); 
        }
        void display(std::ostream & out, upolynomial_sequence const & seq, char const * var_name = "x") const;
    };

};

#endif
