/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    algebraic_numbers.cpp

Abstract:

    Real Algebraic Numbers

Author:

    Leonardo (leonardo) 2011-11-22

Notes:

--*/
#include "util/mpbq.h"
#include "util/basic_interval.h"
#include "util/scoped_ptr_vector.h"
#include "util/mpbqi.h"
#include "util/timeit.h"
#include "util/common_msgs.h"
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/upolynomial.h"
#include "math/polynomial/sexpr2upolynomial.h"
#include "math/polynomial/algebraic_params.hpp"

namespace algebraic_numbers {

    struct basic_cell {
        mpq m_value;
    };

    // Each algebraic number is associated with two
    // isolating (refinable) intervals. The second
    // interval just caches refinements of the first one.

    struct algebraic_cell {
        // polynomial
        unsigned   m_p_sz;
        mpz *      m_p;
        mpbqi      m_interval; // isolating/refinable interval
        // sign of p at the lower and upper bounds of m_interval
        unsigned   m_minimal:1; // true if p is a minimal polynomial for representing the number
        unsigned   m_sign_lower:1;
        unsigned   m_not_rational:1; // if true we know for sure it is not a rational
        unsigned   m_i:29; // number is the i-th root of p, 0 if it is not known which root of p the number is.
        algebraic_cell():m_p_sz(0), m_p(nullptr), m_minimal(false), m_not_rational(false), m_i(0) {}
        bool is_minimal() const { return m_minimal != 0; }
    };

    typedef polynomial::manager   poly_manager;
    typedef upolynomial::manager  upoly_manager;
    typedef upolynomial::numeral_vector upoly;
    typedef upolynomial::scoped_numeral_vector scoped_upoly;
    typedef upolynomial::factors factors;

    void manager::get_param_descrs(param_descrs & r) {
        algebraic_params::collect_param_descrs(r);
    }

    struct manager::imp {
        reslimit&                m_limit;
        manager &                m_wrapper;
        small_object_allocator & m_allocator;
        unsynch_mpq_manager &    m_qmanager;
        mpbq_manager             m_bqmanager;
        mpbqi_manager            m_bqimanager;
        poly_manager             m_pmanager;
        upoly_manager            m_upmanager;
        mpq                      m_zero;
        scoped_mpz               m_is_rational_tmp;
        scoped_upoly             m_isolate_tmp1;
        scoped_upoly             m_isolate_tmp2;
        scoped_upoly             m_isolate_tmp3;
        scoped_upoly             m_eval_sign_tmp;
        factors                  m_isolate_factors;
        scoped_mpbq_vector       m_isolate_roots;
        scoped_mpbq_vector       m_isolate_lowers;
        scoped_mpbq_vector       m_isolate_uppers;
        scoped_upoly             m_add_tmp;
        polynomial::var          m_x;
        polynomial::var          m_y;

        // configuration
        int                        m_min_magnitude;
        bool                       m_factor;
        polynomial::factor_params  m_factor_params;
        int                        m_zero_accuracy;

        // statistics
        unsigned                 m_compare_cheap;
        unsigned                 m_compare_sturm;
        unsigned                 m_compare_refine;
        unsigned                 m_compare_poly_eq;

        imp(reslimit& lim, manager & w, unsynch_mpq_manager & m, params_ref const & p, small_object_allocator & a):
            m_limit(lim),
            m_wrapper(w),
            m_allocator(a),
            m_qmanager(m),
            m_bqmanager(m),
            m_bqimanager(m_bqmanager),
            m_pmanager(lim, m, &a),
            m_upmanager(lim, m),
            m_is_rational_tmp(m),
            m_isolate_tmp1(upm()),
            m_isolate_tmp2(upm()),
            m_isolate_tmp3(upm()),
            m_eval_sign_tmp(upm()),
            m_isolate_factors(upm()),
            m_isolate_roots(bqm()),
            m_isolate_lowers(bqm()),
            m_isolate_uppers(bqm()),
            m_add_tmp(upm()) {
            updt_params(p);
            reset_statistics();
            m_x = pm().mk_var();
            m_y = pm().mk_var();
        }

        ~imp() {
        }

        bool acell_inv(algebraic_cell const& c) {
            auto s = upm().eval_sign_at(c.m_p_sz, c.m_p, lower(&c));
            return s == sign_zero || c.m_sign_lower == (s == sign_neg);
        }

        void checkpoint() {
            if (!m_limit.inc())
                throw algebraic_exception(Z3_CANCELED_MSG);
        }

        void reset_statistics() {
            m_compare_cheap   = 0;
            m_compare_sturm   = 0;
            m_compare_refine  = 0;
            m_compare_poly_eq = 0;
        }

        void collect_statistics(statistics & st) {
#ifndef _EXTERNAL_RELEASE
            st.update("algebraic compare cheap", m_compare_cheap);
            st.update("algebraic compare sturm", m_compare_sturm);
            st.update("algebraic compare refine", m_compare_refine);
            st.update("algebraic compare poly", m_compare_poly_eq);
#endif
        }

        void updt_params(params_ref const & _p) {
            algebraic_params p(_p);
            m_min_magnitude            = -static_cast<int>(p.min_mag());
            m_factor                   = p.factor();
            m_factor_params.m_max_p    = p.factor_max_prime();
            m_factor_params.m_p_trials = p.factor_num_primes();
            m_factor_params.m_max_search_size = p.factor_search_size();
            m_zero_accuracy            = -static_cast<int>(p.zero_accuracy());
        }

        unsynch_mpq_manager & qm() {
            return m_qmanager;
        }

        mpbq_manager & bqm() {
            return m_bqmanager;
        }

        mpbqi_manager & bqim() {
            return m_bqimanager;
        }

        poly_manager & pm() {
            return m_pmanager;
        }

        upoly_manager & upm() {
            return m_upmanager;
        }

        void del(basic_cell * c) {
            qm().del(c->m_value);
            m_allocator.deallocate(sizeof(basic_cell), c);
        }

        void del_poly(algebraic_cell * c) {
            for (unsigned i = 0; i < c->m_p_sz; i++)
                qm().del(c->m_p[i]);
            m_allocator.deallocate(sizeof(mpz)*c->m_p_sz, c->m_p);
            c->m_p    = nullptr;
            c->m_p_sz = 0;
        }

        void del_interval(algebraic_cell * c) {
            bqim().del(c->m_interval);
        }

        void del(algebraic_cell * c) {
            del_poly(c);
            del_interval(c);
            m_allocator.deallocate(sizeof(algebraic_cell), c);
        }

        void del(numeral & a) {
            if (a.m_cell == nullptr)
                return;
            if (a.is_basic())
                del(a.to_basic());
            else
                del(a.to_algebraic());
            a.m_cell = nullptr;
        }

        void reset(numeral & a) {
            del(a);
        }

        bool is_zero(numeral const & a) {
            return a.m_cell == nullptr;
        }

        bool is_pos(numeral const & a) {
            if (a.is_basic())
                return qm().is_pos(basic_value(a));
            else
                return bqim().is_pos(a.to_algebraic()->m_interval);
        }

        bool is_neg(numeral const & a) {
            if (a.is_basic())
                return qm().is_neg(basic_value(a));
            else
                return bqim().is_neg(a.to_algebraic()->m_interval);
        }

        mpq const & basic_value(numeral const & a) {
            SASSERT(a.is_basic());
            if (is_zero(a))
                return m_zero;
            else
                return a.to_basic()->m_value;
        }

        bool is_int(numeral & a) {
            if (a.is_basic())
                return qm().is_int(basic_value(a));
            if (a.to_algebraic()->m_not_rational)
                return false; // we know for sure a is not a rational (and consequently an integer)

            // make sure the isolating interval has at most one integer
            if (!refine_until_prec(a, 1)) {
                SASSERT(a.is_basic()); // a became basic
                return qm().is_int(basic_value(a));
            }

            // Find unique integer in the isolating interval
            algebraic_cell * c = a.to_algebraic();
            scoped_mpz candidate(qm());
            bqm().floor(qm(), upper(c), candidate);

            SASSERT(bqm().ge(upper(c), candidate));

            if (bqm().lt(lower(c), candidate) && upm().eval_sign_at(c->m_p_sz, c->m_p, candidate) == sign_zero) {
                m_wrapper.set(a, candidate);
                return true;
            }
            return false;
        }

        /*
          In our representation, non-basic numbers are encoded by
          polynomials of the form: a_n * x^n + ... + a_0 where
          a_0 != 0.

          Thus, we can find whether a non-basic number is actually a rational
          by using the Rational root theorem.

              p/q is a root of a_n * x^n + ... + a_0
              If p is a factor of a_0, and q is a factor of a_n.

          If the isolating interval (lower, upper) has size less than 1/a_n, then
          (a_n*lower, a_n*upper) contains at most one integer.
          Let u be this integer, then the non-basic number is a rational iff
          u/a_n is the actual root.
        */
        bool is_rational(numeral & a) {
            if (a.is_basic())
                return true;
            if (a.to_algebraic()->m_not_rational)
                return false; // we know for sure a is not a rational
            TRACE("algebraic_bug", tout << "is_rational(a):\n"; display_root(tout, a); tout << "\n"; display_interval(tout, a); tout << "\n";);
            algebraic_cell * c = a.to_algebraic();
            save_intervals saved_a(*this, c);
            mpz & a_n = c->m_p[c->m_p_sz - 1];
            scoped_mpz & abs_a_n = m_is_rational_tmp;
            qm().set(abs_a_n, a_n);
            qm().abs(abs_a_n);

            // 1/2^{log2(a_n)+1} <= 1/a_n
            unsigned k = qm().log2(abs_a_n);
            k++;

            TRACE("algebraic_bug", tout << "abs(an): " << qm().to_string(abs_a_n) << ", k: " << k << "\n";);

            // make sure the isolating interval size is less than 1/2^k
            if (!refine_until_prec(a, k)) {
                SASSERT(a.is_basic()); // a became basic
                return true;
            }

            TRACE("algebraic_bug", tout << "interval after refinement: "; display_interval(tout, a); tout << "\n";);

            // Find unique candidate rational in the isolating interval
            scoped_mpbq a_n_lower(bqm());
            scoped_mpbq a_n_upper(bqm());
            bqm().mul(lower(c), abs_a_n, a_n_lower);
            bqm().mul(upper(c), abs_a_n, a_n_upper);

            scoped_mpz zcandidate(qm());
            bqm().floor(qm(), a_n_upper, zcandidate);
            scoped_mpq candidate(qm());
            qm().set(candidate, zcandidate, abs_a_n);
            SASSERT(bqm().ge(upper(c), candidate));

            // Find if candidate is an actual root
            if (bqm().lt(lower(c), candidate) && upm().eval_sign_at(c->m_p_sz, c->m_p, candidate) == sign_zero) {
                saved_a.restore_if_too_small();
                set(a, candidate);
                return true;
            }
            else {
                saved_a.restore_if_too_small();
                c->m_not_rational = true;
                return false;
            }
        }

        void to_rational(numeral & a, mpq & r) {
            VERIFY(is_rational(a));
            SASSERT(a.is_basic());
            qm().set(r, basic_value(a));
        }

        void to_rational(numeral & a, rational & r) {
            scoped_mpq tmp(qm());
            to_rational(a, tmp);
            rational tmp2(tmp);
            r = tmp2;
        }

        unsigned degree(numeral const & a) {
            if (is_zero(a))
                return 0;
            if (a.is_basic())
                return 1;
            return a.to_algebraic()->m_p_sz - 1;
        }

        void swap(numeral & a, numeral & b) {
            std::swap(a.m_cell, b.m_cell);
        }

        basic_cell * mk_basic_cell(mpq & n) {
            if (qm().is_zero(n))
                return nullptr;
            void * mem = static_cast<basic_cell*>(m_allocator.allocate(sizeof(basic_cell)));
            basic_cell * c = new (mem) basic_cell();
            qm().swap(c->m_value, n);
            return c;
        }

        sign sign_lower(algebraic_cell * c) const {
            return c->m_sign_lower == 0 ? sign_pos : sign_neg;
        }

        mpbq const & lower(algebraic_cell const * c) const { return c->m_interval.lower(); }

        mpbq const & upper(algebraic_cell const * c) const { return c->m_interval.upper(); }

        mpbq & lower(algebraic_cell * c) { return c->m_interval.lower(); }

        mpbq & upper(algebraic_cell * c) { return c->m_interval.upper(); }

        void update_sign_lower(algebraic_cell * c) {
            sign sl = upm().eval_sign_at(c->m_p_sz, c->m_p, lower(c));
            // The isolating intervals are refinable. Thus, the polynomial has opposite signs at lower and upper.
            SASSERT(sl != sign_zero);
            SASSERT(upm().eval_sign_at(c->m_p_sz, c->m_p, upper(c)) == -sl);
            c->m_sign_lower = sl == sign_neg;
            SASSERT(acell_inv(*c));
        }

        // Make sure the GCD of the coefficients is one and the leading coefficient is positive
        void normalize_coeffs(algebraic_cell * c) {
            SASSERT(c->m_p_sz > 2);
            upm().normalize(c->m_p_sz, c->m_p);
            if (upm().m().is_neg(c->m_p[c->m_p_sz-1])) {
                upm().neg(c->m_p_sz, c->m_p);
                c->m_sign_lower = !(c->m_sign_lower);
                SASSERT(acell_inv(*c));
            }
        }

        algebraic_cell * mk_algebraic_cell(unsigned sz, mpz const * p, mpbq const & lower, mpbq const & upper, bool minimal) {
            SASSERT(sz > 2);
            void * mem = static_cast<algebraic_cell*>(m_allocator.allocate(sizeof(algebraic_cell)));
            algebraic_cell * c = new (mem) algebraic_cell();
            c->m_p_sz = sz;
            c->m_p    = static_cast<mpz*>(m_allocator.allocate(sizeof(mpz)*sz));
            for (unsigned i = 0; i < sz; i++) {
                new (c->m_p + i) mpz();
                qm().set(c->m_p[i], p[i]);
            }
            bqim().set(c->m_interval, lower, upper);
            update_sign_lower(c);
            c->m_minimal = minimal;
            SASSERT(c->m_i == 0);
            SASSERT(c->m_not_rational == false);
            if (c->m_minimal)
                c->m_not_rational = true;
            normalize_coeffs(c);
            return c;
        }

        void set(numeral & a, mpq & n) {
            if (qm().is_zero(n)) {
                reset(a);
                SASSERT(is_zero(a));
                return;
            }
            if (a.is_basic()) {
                if (is_zero(a))
                    a.m_cell = mk_basic_cell(n);
                else
                    qm().set(a.to_basic()->m_value, n);
            }
            else {
                del(a);
                a.m_cell = mk_basic_cell(n);
            }
        }

        void set(numeral & a, mpq const & n) {
            scoped_mpq tmp(qm());
            qm().set(tmp, n);
            set(a, tmp);
        }

        void copy_poly(algebraic_cell * c, unsigned sz, mpz const * p) {
            SASSERT(c->m_p == 0);
            SASSERT(c->m_p_sz == 0);
            c->m_p_sz = sz;
            c->m_p    = static_cast<mpz*>(m_allocator.allocate(sizeof(mpz)*sz));
            for (unsigned i = 0; i < sz; i++) {
                new (c->m_p + i) mpz();
                qm().set(c->m_p[i], p[i]);
            }
        }

        void set_interval(algebraic_cell * c, mpbqi const & i) {
            bqim().set(c->m_interval, i);
        }

        void set_interval(algebraic_cell * c, mpbq const & l, mpbq const & u) {
            bqim().set(c->m_interval, l, u);
        }

        // Copy fields from source to target.
        // It assumes that fields target->m_p is NULL or was deleted.
        void copy(algebraic_cell * target, algebraic_cell const * source) {
            copy_poly(target, source->m_p_sz, source->m_p);
            set_interval(target, source->m_interval);
            target->m_minimal      = source->m_minimal;
            target->m_sign_lower   = source->m_sign_lower;
            target->m_not_rational = source->m_not_rational;
            target->m_i            = source->m_i;
            SASSERT(acell_inv(*source));
            SASSERT(acell_inv(*target));
        }

        void set(numeral & a, unsigned sz, mpz const * p, mpbq const & lower, mpbq const & upper, bool minimal) {
            SASSERT(sz > 1);
            if (sz == 2) {
                // it is linear
                scoped_mpq tmp(qm());
                qm().set(tmp, p[0], p[1]);
                qm().neg(tmp);
                set(a, tmp);
            }
            else {
                if (a.is_basic()) {
                    del(a);
                    a.m_cell = TAG(void*, mk_algebraic_cell(sz, p, lower, upper, minimal), ROOT);
                }
                else {
                    SASSERT(sz > 2);
                    algebraic_cell * c = a.to_algebraic();
                    del_poly(c);
                    copy_poly(c, sz, p);
                    set_interval(c, lower, upper);
                    c->m_minimal      = minimal;
                    c->m_not_rational = false;
                    if (c->m_minimal)
                        c->m_not_rational = true;
                    c->m_i            = 0;
                    update_sign_lower(c);
                    normalize_coeffs(c);
                }
                SASSERT(acell_inv(*a.to_algebraic()));
            }
            TRACE("algebraic", tout << "a: "; display_root(tout, a); tout << "\n";);
        }

        void set(numeral & a, numeral const & b) {
            if (&a == &b)
                return;
            if (a.is_basic()) {
                if (b.is_basic()) {
                    SASSERT(a.is_basic() && b.is_basic());
                    set(a, basic_value(b));
                }
                else {
                    SASSERT(a.is_basic() && !b.is_basic());
                    del(a);
                    void * mem = m_allocator.allocate(sizeof(algebraic_cell));
                    algebraic_cell * c = new (mem) algebraic_cell();
                    a.m_cell = TAG(void *, c, ROOT);
                    copy(c, b.to_algebraic());
                    SASSERT(acell_inv(*c));
                }
            }
            else {
                if (b.is_basic()) {
                    SASSERT(!a.is_basic() && b.is_basic());
                    del(a);
                    set(a, basic_value(b));
                }
                else {
                    SASSERT(!a.is_basic() && !b.is_basic());
                    del_poly(a.to_algebraic());
                    del_interval(a.to_algebraic());
                    copy(a.to_algebraic(), b.to_algebraic());
                    SASSERT(acell_inv(*a.to_algebraic()));
                }
            }
        }

        bool factor(scoped_upoly const & up, factors & r) {
            if (m_factor) {
                return upm().factor(up, r, m_factor_params);
            }
            else {
                scoped_upoly & up_sqf = m_isolate_tmp3;
                up_sqf.reset();
                upm().square_free(up.size(), up.c_ptr(), up_sqf);
                TRACE("algebraic", upm().display(tout, up_sqf.size(), up_sqf.c_ptr()); tout << "\n";);
                r.push_back(up_sqf, 1);
                return false;
            }
        }

        struct lt_proc {
            manager & m;
            lt_proc(manager & _m):m(_m) {}
            bool operator()(numeral const & a1, numeral const & a2) const {
                return m.lt(a1, a2);
            }
        };

        void sort_roots(numeral_vector & r) {
            if (m_limit.inc()) {
                std::sort(r.begin(), r.end(), lt_proc(m_wrapper));
            }
        }

        void isolate_roots(scoped_upoly const & up, numeral_vector & roots) {
            TRACE("algebraic", upm().display(tout, up); tout << "\n";);
            if (up.empty())
                return; // ignore the zero polynomial
            factors & fs = m_isolate_factors;
            fs.reset();
            bool full_fact;
            if (upm().has_zero_roots(up.size(), up.c_ptr())) {
                roots.push_back(numeral());
                scoped_upoly & nz_up = m_isolate_tmp2;
                upm().remove_zero_roots(up.size(), up.c_ptr(), nz_up);
                full_fact = factor(nz_up, fs);
            }
            else {
                full_fact = factor(up, fs);
            }

            unsigned num_factors = fs.distinct_factors();
            for (unsigned i = 0; i < num_factors; i++) {
                upolynomial::numeral_vector const & f = fs[i];
                // polynomial f contains the non zero roots
                unsigned d = upm().degree(f);
                TRACE("algebraic", tout << "factor " << i << " degree: " << d << "\n";);
                if (d == 0)
                    continue; // found all roots of f
                scoped_mpq r(qm());
                if (d == 1) {
                    TRACE("algebraic", tout << "linear polynomial...\n";);
                    // f is a linear polynomial ax + b
                    // set r <- -b/a
                    qm().set(r, f[0]);
                    qm().div(r, f[1], r);
                    qm().neg(r);
                    roots.push_back(numeral(mk_basic_cell(r)));
                    continue;
                }
                SASSERT(m_isolate_roots.empty() && m_isolate_lowers.empty() && m_isolate_uppers.empty());
                upm().sqf_isolate_roots(f.size(), f.c_ptr(), bqm(), m_isolate_roots, m_isolate_lowers, m_isolate_uppers);
                // collect rational/basic roots                
                unsigned sz = m_isolate_roots.size();
                TRACE("algebraic", tout << "isolated roots: " << sz << "\n";);
                for (unsigned i = 0; i < sz; i++) {
                    to_mpq(qm(), m_isolate_roots[i], r);
                    roots.push_back(numeral(mk_basic_cell(r)));
                }
                SASSERT(m_isolate_uppers.size() == m_isolate_lowers.size());
                // collect non-basic roots
                sz = m_isolate_lowers.size();
                for (unsigned i = 0; i < sz; i++) {
                    mpbq & lower = m_isolate_lowers[i];
                    mpbq & upper = m_isolate_uppers[i];
                    if (!upm().isolating2refinable(f.size(), f.c_ptr(), bqm(), lower, upper)) {
                        // found rational root... it is stored in lower
                        to_mpq(qm(), lower, r);
                        roots.push_back(numeral(mk_basic_cell(r)));
                    }
                    else {
                        algebraic_cell * c = mk_algebraic_cell(f.size(), f.c_ptr(), lower, upper, full_fact);
                        roots.push_back(numeral(c));
                    }
                }
                m_isolate_roots.reset();
                m_isolate_lowers.reset();
                m_isolate_uppers.reset();
            }
            sort_roots(roots);
        }

        void isolate_roots(polynomial_ref const & p, numeral_vector & roots) {
            SASSERT(is_univariate(p));
            TRACE("algebraic", tout << "isolating roots of: " << p << "\n";);
            if (::is_zero(p))
                return; // ignore the zero polynomial
            scoped_upoly & up     = m_isolate_tmp1;
            upm().to_numeral_vector(p, up);
            isolate_roots(up, roots);
        }

        void mk_root(scoped_upoly const & up, unsigned i, numeral & r) {
            // TODO: implement version that finds i-th root without isolating all roots.
            if (i == 0)
                throw algebraic_exception("invalid root object, root index must be greater than 0");
            if (up.empty())
                throw algebraic_exception("invalid root object, polynomial must not be the zero polynomial");
            SASSERT(i != 0);
            scoped_numeral_vector roots(m_wrapper);
            isolate_roots(up, roots);
            unsigned num_roots = roots.size();
            TRACE("algebraic", tout << "num-roots: " << num_roots << "\n";
                  for (unsigned i = 0; i < num_roots; i++) {
                      display_interval(tout, roots[i]);
                      tout << "\n";
                  });
            if (i > num_roots)
                throw algebraic_exception("invalid root object, polynomial does have sufficient roots");
            set(r, roots[i-1]);
        }

        void mk_root(polynomial_ref const & p, unsigned i, numeral & r) {
            SASSERT(i != 0);
            SASSERT(is_univariate(p));
            TRACE("algebraic", tout << "isolating roots of: " << p << "\n";);
            scoped_upoly & up     = m_isolate_tmp1;
            upm().to_numeral_vector(p, up);
            mk_root(up, i, r);
        }

        void mk_root(sexpr const * p, unsigned i, numeral & r) {
            SASSERT(i != 0);
            scoped_upoly & up = m_isolate_tmp1;
            sexpr2upolynomial(upm(), p, up);
            TRACE("algebraic", tout << "mk_root " << i << "\n"; upm().display(tout, up); tout << "\n";);
            mk_root(up, i, r);
        }

        /**
           \brief Make sure that if a is 0, then a.m_cell == 0
        */
        void normalize(numeral & a) {
            if (is_zero(a))
                return;
            if (a.is_basic()) {
                if (qm().is_zero(a.to_basic()->m_value))
                    reset(a);
            }
            else {
                algebraic_cell * c = a.to_algebraic();
                if (!upm().normalize_interval_core(c->m_p_sz, c->m_p, sign_lower(c), bqm(), lower(c), upper(c)))
                    reset(a);
                SASSERT(acell_inv(*c));
            }
        }

        /**
           \brief Return the magnitude of the given interval.
           The magnitude is an approximation of the size of the interval.
        */
        int magnitude(mpbq const & l, mpbq const & u) {
            SASSERT(bqm().is_nonneg(l) || bqm().is_nonpos(u));
            int l_k = l.k();
            int u_k = u.k();
            if (l_k == u_k)
                return bqm().magnitude_ub(l);
            if (bqm().is_nonneg(l))
                return qm().log2(u.numerator()) - qm().log2(l.numerator()) - u_k + l_k - u_k;
            else
                return qm().mlog2(u.numerator()) - qm().mlog2(l.numerator()) - u_k + l_k - u_k;
        }

        /**
           \brief Return the magnitude of the isolating interval associated with the given algebraic_cell
        */
        int magnitude(algebraic_cell * c) {
            return magnitude(lower(c), upper(c));
        }

        /**
           \brief Refine isolating interval associated with algebraic number.
           The new interval will half of the size of the original one.

           Return TRUE,  if interval was refined
           Return FALSE, if actual root was found.
        */
        bool refine_core(algebraic_cell * c) {
            bool r = upm().refine_core(c->m_p_sz, c->m_p, sign_lower(c), bqm(), lower(c), upper(c));
            SASSERT(acell_inv(*c));
            return r;
        }

        /**
           \brief Refine isolating interval associated with algebraic number.
           This procedure is a noop if algebraic number is basic.

           This method essentially updates the field m_interval
           The new interval will half of the size of the original one.

           Remark: a root object may become basic when invoking this method,
           since we may find the actual rational root.
           This can only happen when non minimal polynomials are used to
           encode root objects.
        */
        bool refine(numeral & a) {
            if (a.is_basic())
                return false;
            algebraic_cell * c = a.to_algebraic();
            if (refine_core(c)) {
                return true;
            }
            else {
                // root was found
                scoped_mpq r(qm());
                to_mpq(qm(), lower(c), r);
                del(c);
                a.m_cell = mk_basic_cell(r);
                return false;
            }
        }

        bool refine(numeral & a, unsigned k) {
            for (unsigned i = 0; i < k; i++)
                if (!refine(a))
                    return false;
            return true;
        }

        bool refine_until_prec(numeral & a, unsigned prec) {
            if (a.is_basic())
                return true;
            algebraic_cell * c = a.to_algebraic();
            if (!upm().refine(c->m_p_sz, c->m_p, bqm(), lower(c), upper(c), prec)) {
                // actual root was found
                scoped_mpq r(qm());
                to_mpq(qm(), lower(c), r);
                del(c);
                a.m_cell = mk_basic_cell(r);
                return false;
            }
            SASSERT(acell_inv(*c));
            return true;
        }

        /**
           Functor for computing the polynomial
                resultant_y(pa(x-y), pb(y))
           where
              pa and pb are the polynomials for algebraic cells: a and b.

           Remark: If alpha and beta are roots of pa and pb, then
           alpha + beta is a root of the new polynomial.

           Remark: If the argument IsAdd == false, then the
           functor computes resultant_y(pa(x+y), pb(y))
        */
        template<bool IsAdd>
        struct mk_add_polynomial {
            imp & m;

            mk_add_polynomial(imp & _m):m(_m) {}

            void operator()(algebraic_cell * a, algebraic_cell * b, scoped_upoly & r) const {
                polynomial_ref pa_x(m.pm());   // pa(x)
                polynomial_ref pa_x_y(m.pm()); // pa(x-y) for addition and pa(x+y) for subtraction
                polynomial_ref pb_y(m.pm());   // pb(y)
                polynomial_ref r_x(m.pm());    // r(x) = resultant_y(pa(x-y), pb(y))
                pa_x = m.pm().to_polynomial(a->m_p_sz, a->m_p, m.m_x);
                pb_y = m.pm().to_polynomial(b->m_p_sz, b->m_p, m.m_y);
                if (IsAdd)
                    m.pm().compose_x_minus_y(pa_x, m.m_y, pa_x_y);
                else
                    m.pm().compose_x_plus_y(pa_x, m.m_y, pa_x_y);
                m.pm().resultant(pa_x_y, pb_y, m.m_y, r_x);
                m.upm().to_numeral_vector(r_x, r);
            }
        };

        /**
           Functor for computing the polynomial
                resultant_y(y^n * pa(x/y), pb(y))
           where
              pa and pb are the polynomials for algebraic cells: a and b.
              n is degree of pa.
        */
        struct mk_mul_polynomial {
            imp & m;

            mk_mul_polynomial(imp & _m):m(_m) {}

            void operator()(algebraic_cell * a, algebraic_cell * b, scoped_upoly & r) const {
                polynomial_ref pa_x(m.pm());   // pa(x)
                polynomial_ref pa_x_div_y(m.pm()); // y^n * pa(x/y)
                polynomial_ref pb_y(m.pm());   // pb(y)
                polynomial_ref r_x(m.pm());    // r(x) = resultant_y(y^n * pa(x/y), pb(y))
                pa_x = m.pm().to_polynomial(a->m_p_sz, a->m_p, m.m_x);
                pb_y = m.pm().to_polynomial(b->m_p_sz, b->m_p, m.m_y);
                pa_x_div_y = m.pm().compose_x_div_y(pa_x, m.m_y);
                m.pm().resultant(pa_x_div_y, pb_y, m.m_y, r_x);
                m.upm().to_numeral_vector(r_x, r);
            }
        };

        /**
           \brief Return the sum (interval) of the intervals of algebraic cells a and b.
        */
        template<bool IsAdd>
        struct add_interval_proc {
            imp & m;
            add_interval_proc(imp & _m):m(_m) {}

            void operator()(algebraic_cell * a, algebraic_cell * b, mpbqi & r) const {
                if (IsAdd)
                    m.bqim().add(a->m_interval, b->m_interval, r);
                else
                    m.bqim().sub(a->m_interval, b->m_interval, r);
            }
        };

        /**
           \brief Return the product of the intervals of algebraic cells a and b.
        */
        struct mul_interval_proc {
            imp & m;
            mul_interval_proc(imp & _m):m(_m) {}

            void operator()(algebraic_cell * a, algebraic_cell * b, mpbqi & r) const {
                m.bqim().mul(a->m_interval, b->m_interval, r);
            }
        };

        /**
           \brief Functor for c <- a + b
        */
        struct add_proc {
            imp & m;
            add_proc(imp & _m):m(_m) {}
            void operator()(numeral & a, numeral & b, numeral & c) const { return m.add(a, b, c); }
        };

        /**
           \brief Functor for c <- a - b
        */
        struct sub_proc {
            imp & m;
            sub_proc(imp & _m):m(_m) {}
            void operator()(numeral & a, numeral & b, numeral & c) const { return m.sub(a, b, c); }
        };

        /**
           \brief Functor for c <- a * b
        */
        struct mul_proc {
            imp & m;
            mul_proc(imp & _m):m(_m) {}
            void operator()(numeral & a, numeral & b, numeral & c) const { return m.mul(a, b, c); }
        };

        // Save the isolating interval of an algebraic cell.
        struct save_intervals {
            imp &             m_owner;
            numeral const &   m_num;
            mpbqi             m_old_interval;
            bool              m_restore_invoked; // true if restore_if_too_small was invoked

            save_intervals(imp & o, numeral const & num):
                m_owner(o),
                m_num(num),
                m_restore_invoked(false) {
                SASSERT(!num.is_basic());
                m_owner.bqim().set(m_old_interval, num.to_algebraic()->m_interval);
            }

            ~save_intervals() {
                if (!m_restore_invoked)
                    restore_if_too_small();
                m_owner.bqim().del(m_old_interval);
            }

            // Restore the intervals of m_cell, if its current magnitude is too small
            void restore_if_too_small() {
                m_restore_invoked = true;
                if (m_num.is_basic())
                    return; // m_num is not algebraic anymore
                algebraic_cell * cell = m_num.to_algebraic();
                if (m_owner.magnitude(cell) < m_owner.m_min_magnitude) {
                    // restore old interval
                    m_owner.bqim().swap(cell->m_interval, m_old_interval);
                }
            }
        };

        /**
           \brief Set c with the algebraic number associated with polynomial p and isolating interval r_i == (l, u).
           The isolating interval is not normalized, that is, it may contain zero.

           The method also requires the following (redundant) additional information:
             - seq: The Sturm sequence for p
             - lV:  The Number of sign variations (in seq) at l
             - lU:  The Number of sign variations (in seq) at u

           \pre p must be square free
           \pre r_i must be an isolating interval for p
           \pre seq must be the Sturm sequence for p
           \pre lV and uV are the sign variations (in seq) for r_i.lower() and r_i.upper()
        */
        void set_core(numeral & c, scoped_upoly & p, mpbqi & r_i, upolynomial::scoped_upolynomial_sequence & seq, int lV, int uV, bool minimal) {
            TRACE("algebraic", tout << "set_core p: "; upm().display(tout, p); tout << "\n";);
            if (bqim().contains_zero(r_i)) {
                if (upm().has_zero_roots(p.size(), p.c_ptr())) {
                    // zero is a root of p, and r_i is an isolating interval containing zero,
                    // then c is zero
                    reset(c);
                    TRACE("algebraic", tout << "resetting\nresult: "; display_root(tout, c); tout << "\n";);
                    return;
                }
                int zV = upm().sign_variations_at_zero(seq);
                if (lV == zV) {
                    // root is in the second half
                    bqim().set_lower(r_i, mpbq());
                }
                else {
                    SASSERT(zV == uV);
                    // root is in the first half
                    bqim().set_upper(r_i, mpbq());
                }
                SASSERT(bqm().lt(r_i.lower(), r_i.upper()));
            }

            // make sure 0 is not a root of p
            scoped_upoly & nz_p = m_add_tmp;
            if (upm().has_zero_roots(p.size(), p.c_ptr())) {
                // remove zero root
                upm().remove_zero_roots(p.size(), p.c_ptr(), nz_p);
            }
            else {
                p.swap(nz_p);
            }

            if (!upm().isolating2refinable(nz_p.size(), nz_p.c_ptr(), bqm(), r_i.lower(), r_i.upper())) {
                // found actual root
                scoped_mpq r(qm());
                to_mpq(qm(), r_i.lower(), r);
                set(c, r);
            }
            else {
                TRACE("algebraic", tout << "set_core...\n";);
                set(c, nz_p.size(), nz_p.c_ptr(), r_i.lower(), r_i.upper(), minimal);
            }
        }

        /**
           \brief Apply a binary operation on the given algebraic numbers.

           \pre !a.is_basic() and !b.is_basic()

           The template arguments:

           MkResultPoly:      functor for constructing a polynomial p(x) s.t. p(u) = 0 (where u is the result of the operation).
           MkResultInterval:  functor for computing an approximation of the resultant interval using the interval of the arguments.
                  The functor must be "monotonic". That is, if we provide better (smaller) input intervals, it produces a better
                  (smaller) output interval.
           MkBasic: functor for applying the operation if a or b become a basic cell. The numerals a and b may become basic
           during refinement.
        */
        template<typename MkResultPoly, typename MkResultInterval, typename MkBasic>
        void mk_binary(numeral & a, numeral & b, numeral & c, MkResultPoly const & mk_poly, MkResultInterval const & mk_interval, MkBasic const & mk_basic) {
            SASSERT(!a.is_basic());
            SASSERT(!b.is_basic());
            algebraic_cell * cell_a = a.to_algebraic();
            algebraic_cell * cell_b = b.to_algebraic();
            scoped_upoly p(upm());
            scoped_upoly f(upm());
            mk_poly(cell_a, cell_b, p);
            TRACE("anum_mk_binary", tout << "a: "; display_root(tout, a); tout << "\nb: "; display_root(tout, b); tout << "\np: ";
                  upm().display(tout, p); tout << "\n";);
            factors fs(upm());
            bool full_fact  = factor(p, fs);
            unsigned num_fs = fs.distinct_factors();
            scoped_ptr_vector<typename upolynomial::scoped_upolynomial_sequence> seqs;
            for (unsigned i = 0; i < num_fs; i++) {
                TRACE("anum_mk_binary", tout << "factor " << i << "\n"; upm().display(tout, fs[i]); tout << "\n";);
                typename upolynomial::scoped_upolynomial_sequence * seq = alloc(typename upolynomial::scoped_upolynomial_sequence, upm());
                upm().sturm_seq(fs[i].size(), fs[i].c_ptr(), *seq);
                seqs.push_back(seq);
            }
            SASSERT(seqs.size() == num_fs);

            save_intervals saved_a(*this, a);
            save_intervals saved_b(*this, b);
            scoped_mpbqi r_i(bqim());

            while (true) {
                checkpoint();
                SASSERT(!a.is_basic());
                SASSERT(!b.is_basic());
                mk_interval(cell_a, cell_b, r_i);

                unsigned num_rem  = 0; // number of remaining sequences
                unsigned target_i = UINT_MAX; // index of sequence that is isolating
                int target_lV = 0, target_uV = 0;
                for (unsigned i = 0; i < num_fs; i++) {
                    if (seqs[i] == nullptr)
                        continue; // sequence was discarded because it does not contain the root.
                    TRACE("anum_mk_binary", tout << "sequence " << i << "\n"; upm().display(tout, *(seqs[i])); tout << "\n";);
                    int lV = upm().sign_variations_at(*(seqs[i]), r_i.lower());
                    int uV = upm().sign_variations_at(*(seqs[i]), r_i.upper());
                    int V  = lV - uV;
                    TRACE("algebraic", tout << "r_i: "; bqim().display(tout, r_i); tout << "\n";
                          tout << "lV: " << lV << ", uV: " << uV << "\n";
                          tout << "a.m_interval: "; bqim().display(tout, cell_a->m_interval); tout << "\n";
                          tout << "b.m_interval: "; bqim().display(tout, cell_b->m_interval); tout << "\n";
                          );
                    if (V <= 0) {
                        // discard sequence, since factor does not contain the root
                        seqs.set(i, nullptr);
                    }
                    else if (V == 1) {
                        target_i  = i;
                        target_lV = lV;
                        target_uV = uV;
                        num_rem++;
                    }
                    else {
                        num_rem++;
                    }
                }

                if (num_rem == 1 && target_i != UINT_MAX) {
                    // found isolating interval
                    TRACE("anum_mk_binary", tout << "target_i: " << target_i << "\n";);
                    saved_a.restore_if_too_small();
                    saved_b.restore_if_too_small();
                    upm().set(fs[target_i].size(), fs[target_i].c_ptr(), f);
                    set_core(c, f, r_i, *(seqs[target_i]), target_lV, target_uV, full_fact);
                    return;
                }

                if (!refine(a) || !refine(b)) {
                    // a or b became basic
                    SASSERT(a.is_basic() || b.is_basic());
                    saved_a.restore_if_too_small();
                    saved_a.restore_if_too_small();
                    return mk_basic(a, b, c);
                }
            }
        }

        template<typename MkResultPoly, typename MkResultInterval, typename MkBasic>
        void mk_unary(numeral & a, numeral & b, MkResultPoly const & mk_poly, MkResultInterval const & mk_interval, MkBasic const & mk_basic) {
            SASSERT(!a.is_basic());
            algebraic_cell * cell_a = a.to_algebraic();

            scoped_upoly p(upm());
            scoped_upoly f(upm());
            mk_poly(cell_a, p);

            factors fs(upm());
            bool full_fact  = factor(p, fs);
            unsigned num_fs = fs.distinct_factors();
            scoped_ptr_vector<typename upolynomial::scoped_upolynomial_sequence> seqs;
            for (unsigned i = 0; i < num_fs; i++) {
                typename upolynomial::scoped_upolynomial_sequence * seq = alloc(typename upolynomial::scoped_upolynomial_sequence, upm());
                upm().sturm_seq(fs[i].size(), fs[i].c_ptr(), *seq);
                seqs.push_back(seq);
            }
            SASSERT(seqs.size() == num_fs);

            save_intervals saved_a(*this, a);
            scoped_mpbqi r_i(bqim());

            while (true) {
                checkpoint();
                SASSERT(!a.is_basic());
                mk_interval(cell_a, r_i);

                unsigned num_rem  = 0; // number of remaining sequences
                unsigned target_i = UINT_MAX; // index of sequence that is isolating
                int target_lV = 0, target_uV = 0;
                for (unsigned i = 0; i < num_fs; i++) {
                    if (seqs[i] == nullptr)
                        continue; // sequence was discarded because it does not contain the root.
                    int lV = upm().sign_variations_at(*(seqs[i]), r_i.lower());
                    int uV = upm().sign_variations_at(*(seqs[i]), r_i.upper());
                    int V  = lV - uV;
                    TRACE("algebraic", tout << "r_i: "; bqim().display(tout, r_i); tout << "\n";
                          tout << "lV: " << lV << ", uV: " << uV << "\n";
                          tout << "a.m_interval: "; bqim().display(tout, cell_a->m_interval); tout << "\n";
                          );
                    if (V <= 0) {
                        // discard sequence, since factor does not contain the root
                        seqs.set(i, nullptr);
                    }
                    else if (V == 1) {
                        target_i  = i;
                        target_lV = lV;
                        target_uV = uV;
                        num_rem++;
                    }
                    else {
                        num_rem++;
                    }
                }

                if (num_rem == 1 && target_i != UINT_MAX) {
                    // found isolating interval
                    saved_a.restore_if_too_small();
                    upm().set(fs[target_i].size(), fs[target_i].c_ptr(), f);
                    set_core(b, f, r_i, *(seqs[target_i]), target_lV, target_uV, full_fact);
                    return;
                }

                if (!refine(a)) {
                    // a became basic
                    SASSERT(a.is_basic());
                    saved_a.restore_if_too_small();
                    return mk_basic(a, b);
                }
            }
        }

        /**
           Functor for computing the polynomial
              resultant_y(x^k - y, pa(y))
           where
              pa is the polynomial for algebraic cell: a.
              k is a parameter.
        */
        struct mk_root_polynomial {
            imp & m;
            unsigned k;

            mk_root_polynomial(imp & _m, unsigned _k):m(_m), k(_k) {}

            void operator()(algebraic_cell * a, scoped_upoly & r) const {
                // Let p be the polynomial associated with a.
                // Then, r(x) := Resultant(x^k - y, p(y), y)
                // is a polynomial s.t. a^{1/k} is a root of r(x).

                // Create r(x)
                polynomial_ref p_y(m.pm());
                polynomial_ref xk_y(m.pm());
                polynomial_ref y(m.pm());
                polynomial_ref r_x(m.pm());
                p_y  = m.pm().to_polynomial(a->m_p_sz, a->m_p, m.m_y);
                y    = m.pm().mk_polynomial(m.m_y);
                xk_y = m.pm().mk_polynomial(m.m_x, k);
                xk_y = xk_y - y;
                m.pm().resultant(xk_y, p_y, m.m_y, r_x);
                m.upm().to_numeral_vector(r_x, r);
            }
        };

        /**
           \brief Return the k-th root of the interval of an algebraic cell a.
        */
        struct root_interval_proc {
            imp & m;
            unsigned k;
            root_interval_proc(imp & _m, unsigned _k):m(_m), k(_k) {}

            void operator()(algebraic_cell * a, mpbqi & r) const {
                m.bqm().root_lower(m.lower(a), k, r.lower());
                m.bqm().root_upper(m.upper(a), k, r.upper());
            }
        };

        /**
           \brief Functor for b <- a^{1/k}
        */
        struct root_proc {
            imp & m;
            unsigned k;
            root_proc(imp & _m, unsigned _k):m(_m), k(_k) {}
            void operator()(numeral & a, numeral & b) const {
                return m.root(a, k, b);
            }
        };

        /**
           Functor for computing the polynomial
              resultant_y(x - y^k, pa(y))
           where
              pa is the polynomial for algebraic cell: a.
              k is a parameter.
        */
        struct mk_power_polynomial {
            imp & m;
            unsigned k;

            mk_power_polynomial(imp & _m, unsigned _k):m(_m), k(_k) {}

            void operator()(algebraic_cell * a, scoped_upoly & r) const {
                polynomial_ref p_y(m.pm());
                polynomial_ref x(m.pm());
                polynomial_ref x_yk(m.pm());
                polynomial_ref r_x(m.pm());
                p_y  = m.pm().to_polynomial(a->m_p_sz, a->m_p, m.m_y);
                x    = m.pm().mk_polynomial(m.m_x);
                x_yk = m.pm().mk_polynomial(m.m_y, k);
                x_yk = x - x_yk;
                m.pm().resultant(x_yk, p_y, m.m_y, r_x);
                m.upm().to_numeral_vector(r_x, r);
            }
        };

        /**
           \brief Return the ^k of the interval of an algebraic cell a.
        */
        struct power_interval_proc {
            imp & m;
            unsigned k;
            power_interval_proc(imp & _m, unsigned _k):m(_m), k(_k) {}

            void operator()(algebraic_cell * a, mpbqi & r) const {
                m.bqim().power(a->m_interval, k, r);
            }
        };

        /**
           \brief Functor for b <- a^k
        */
        struct power_proc {
            imp & m;
            unsigned k;

            power_proc(imp & _m, unsigned _k):m(_m), k(_k) {}
            void operator()(numeral & a, numeral & b) const {
                return m.power(a, k, b);
            }
        };


        void root_core(basic_cell * a, unsigned k, numeral & b) {
            SASSERT(!qm().is_zero(a->m_value));
            SASSERT(k > 1);
            mpq & a_val = a->m_value;
            scoped_mpq r_a_val(qm());

            if (qm().root(a_val, k, r_a_val)) {
                // the result is rational
                TRACE("root_core", tout << "r_a_val: " << r_a_val << " a_val: "; qm().display(tout, a_val); tout << "\n";);
                set(b, r_a_val);
                return;
            }

            // Let a_val be of the form n/d
            // create polynomial p:  d*x^k - n
            // a_val > 0  --> (0, a_val+1) is an isolating interval
            // a_val < 0  --> (a_val-1, 0) is an isolating interval

            // Create p
            scoped_upoly p(upm());
            p.push_back(mpz());
            qm().set(p.back(), a_val.numerator());
            qm().neg(p.back());
            for (unsigned i = 0; i < k; i++)
                p.push_back(mpz());
            qm().set(p.back(), a_val.denominator());

            // Create isolating interval
            scoped_mpbq lower(bqm());
            scoped_mpbq upper(bqm());
            if (qm().is_neg(a_val)) {
                if (!bqm().to_mpbq(a_val, lower)) {
                    // a_val is not a binary rational, lower is just an approximation.
                    // lower == a_val.numerator() / 2^{log2(a_val.denominator()) + 1}
                    // Thus, 2*lower <= a_val <= lower
                    bqm().mul2(lower); // make sure lower <= a_val
                }
                bqm().sub(lower, mpz(1), lower); // make sure lower < (a_val)^{1/k}
            }
            else {
                if (!bqm().to_mpbq(a_val, upper)) {
                    // a_val is not a binary rational, upper is just an approximation.
                    // upper == a_val.numerator() / 2^{log2(a_val.denominator()) + 1}
                    // Thus, upper <= a_val <= 2*upper
                    bqm().mul2(upper); // make sure a_val <= upper
                }
                bqm().add(upper, mpz(1), upper); // make sure (a_val)^{1/k} < upper
            }
            SASSERT(bqm().lt(lower, upper));
            TRACE("algebraic", tout << "root_core:\n"; upm().display(tout, p.size(), p.c_ptr()); tout << "\n";);
            // p is not necessarily a minimal polynomial.
            // So, we set the m_minimal flag to false. TODO: try to factor.
            set(b, p.size(), p.c_ptr(), lower, upper, false);
        }

        void root(numeral & a, unsigned k, numeral & b) {
            if (k == 0)
                throw algebraic_exception("0-th root is indeterminate");
            if (k == 1 || is_zero(a)) {
                set(b, a);
                return;
            }

            if (is_neg(a) && k % 2 == 0) {
                // Remark: some computer algebra systems (e.g., Mathematica) define the
                // k-th root of a negative number as a complex number for any k.
                // We should check if our definition will not confuse users.
                throw algebraic_exception("even root of negative number is not real");
            }

            if (a.is_basic())
                root_core(a.to_basic(), k, b);
            else
                mk_unary(a, b, mk_root_polynomial(*this, k), root_interval_proc(*this, k), root_proc(*this, k));
        }

        void power_core(basic_cell * a, unsigned k, numeral & b) {
            scoped_mpq r(qm());
            qm().power(basic_value(a), k, r);
            set(b, r);
        }

        void power(numeral & a, unsigned k, numeral & b) {
            if (is_zero(a) && k == 0)
                throw algebraic_exception("0^0 is indeterminate");
            if (k == 0) {
                set(b, 1);
                return;
            }
            if (k == 1) {
                set(b, a);
                return;
            }
            if (is_zero(a)) {
                reset(b);
                return;
            }
            if (a.is_basic()) {
                scoped_mpq r(qm());
                qm().power(basic_value(a), k, r);
                set(b, r);
            }
            else {
                mk_unary(a, b, mk_power_polynomial(*this, k), power_interval_proc(*this, k), power_proc(*this, k));
            }
        }

        void add(basic_cell * a, basic_cell * b, numeral & c) {
            scoped_mpq r(qm());
            qm().add(basic_value(a), basic_value(b), r);
            set(c, r);
            normalize(c);
        }

        void sub(basic_cell * a, basic_cell * b, numeral & c) {
            scoped_mpq r(qm());
            qm().sub(basic_value(a), basic_value(b), r);
            set(c, r);
            normalize(c);
        }

        template<bool IsAdd>
        void add(algebraic_cell * a, basic_cell * b, numeral & c) {
            TRACE("algebraic", tout << "adding algebraic and basic cells:\n";
                  tout << "a: "; upm().display(tout, a->m_p_sz, a->m_p); tout << " "; bqim().display(tout, a->m_interval); tout << "\n";
                  tout << "b: "; qm().display(tout, b->m_value); tout << "\n";);
            scoped_mpq nbv(qm());
            qm().set(nbv, b->m_value);
            if (IsAdd)
                qm().neg(nbv);
            m_add_tmp.reset();
            upm().translate_q(a->m_p_sz, a->m_p, nbv, m_add_tmp);
            mpbqi const & i = a->m_interval;
            scoped_mpbq l(bqm());
            scoped_mpbq u(bqm());
            qm().neg(nbv);
            if (bqm().to_mpbq(nbv, l)) {
                bqm().add(i.upper(), l, u);
                bqm().add(i.lower(), l, l);
            }
            else {
                // failed to convert to binary rational
                scoped_mpq il(qm());
                scoped_mpq iu(qm());
                to_mpq(qm(), i.lower(), il);
                to_mpq(qm(), i.upper(), iu);
                TRACE("algebraic",
                      tout << "nbv: " << nbv << "\n";
                      tout << "il: " << il << ", iu: " << iu << "\n";);
                qm().add(il, nbv, il);
                qm().add(iu, nbv, iu);
                // (il, iu) is an isolating refinable (rational) interval for the new polynomial.
                upm().convert_q2bq_interval(m_add_tmp.size(), m_add_tmp.c_ptr(), il, iu, bqm(), l, u);
            }
            TRACE("algebraic",
                  upm().display(tout, m_add_tmp.size(), m_add_tmp.c_ptr());
                  tout << ", l: " << l << ", u: " << u << "\n";
                  tout << "l_sign: " << upm().eval_sign_at(m_add_tmp.size(), m_add_tmp.c_ptr(), l) << "\n";
                  tout << "u_sign: " << upm().eval_sign_at(m_add_tmp.size(), m_add_tmp.c_ptr(), u) << "\n";
                  );
            set(c, m_add_tmp.size(), m_add_tmp.c_ptr(), l, u, a->m_minimal /* minimality is preserved */);
            normalize(c);
        }

        void add(numeral & a, numeral & b, numeral & c) {
            if (is_zero(a)) {
                set(c, b);
                return;
            }

            if (is_zero(b)) {
                set(c, a);
                return;
            }

            if (a.is_basic()) {
                if (b.is_basic())
                    add(a.to_basic(), b.to_basic(), c);
                else
                    add<true>(b.to_algebraic(), a.to_basic(), c);
            }
            else {
                if (b.is_basic())
                    add<true>(a.to_algebraic(), b.to_basic(), c);
                else
                    mk_binary(a, b, c, mk_add_polynomial<true>(*this), add_interval_proc<true>(*this), add_proc(*this));
            }
        }

        void sub(numeral & a, numeral & b, numeral & c) {
            if (is_zero(a)) {
                set(c, b);
                neg(c);
                return;
            }

            if (is_zero(b)) {
                set(c, a);
                return;
            }

            if (a.is_basic()) {
                if (b.is_basic())
                    sub(a.to_basic(), b.to_basic(), c);
                else {
                    // c <- b - a
                    add<false>(b.to_algebraic(), a.to_basic(), c);
                    // c <- -c = a - b
                    neg(c);
                }
            }
            else {
                if (b.is_basic())
                    add<false>(a.to_algebraic(), b.to_basic(), c);
                else
                    mk_binary(a, b, c, mk_add_polynomial<false>(*this), add_interval_proc<false>(*this), sub_proc(*this));
            }
        }

        void mul(basic_cell * a, basic_cell * b, numeral & c) {
            scoped_mpq r(qm());
            qm().mul(basic_value(a), basic_value(b), r);
            set(c, r);
            normalize(c);
        }

        void mul(algebraic_cell * a, basic_cell * b, numeral & c) {
            TRACE("algebraic", tout << "mult algebraic and basic cells:\n";
                  tout << "a: "; upm().display(tout, a->m_p_sz, a->m_p); tout << " "; bqim().display(tout, a->m_interval); tout << "\n";
                  tout << "b: "; qm().display(tout, b->m_value); tout << "\n";);
            SASSERT(upm().eval_sign_at(a->m_p_sz, a->m_p, lower(a)) == -upm().eval_sign_at(a->m_p_sz, a->m_p, upper(a)));
            scoped_mpq nbv(qm());
            qm().set(nbv, b->m_value);
            qm().inv(nbv);
            scoped_upoly & mulp = m_add_tmp;
            upm().set(a->m_p_sz, a->m_p, mulp);
            upm().compose_p_q_x(mulp.size(), mulp.c_ptr(), nbv);
            mpbqi const & i = a->m_interval;
            scoped_mpbq l(bqm());
            scoped_mpbq u(bqm());
            qm().inv(nbv);
            bool is_neg = qm().is_neg(nbv);
            if (bqm().to_mpbq(nbv, l)) {
                bqm().mul(i.upper(), l, u);
                bqm().mul(i.lower(), l, l);
                if (is_neg)
                    bqm().swap(l, u);
            }
            else {
                // failed to convert to binary rational
                scoped_mpq il(qm());
                scoped_mpq iu(qm());
                to_mpq(qm(), i.lower(), il);
                to_mpq(qm(), i.upper(), iu);
                TRACE("algebraic",
                      tout << "nbv: " << nbv << "\n";
                      tout << "il: " << il << ", iu: " << iu << "\n";);
                qm().mul(il, nbv, il);
                qm().mul(iu, nbv, iu);
                if (is_neg)
                    qm().swap(il, iu);
                // (il, iu) is an isolating refinable (rational) interval for the new polynomial.
                upm().convert_q2bq_interval(mulp.size(), mulp.c_ptr(), il, iu, bqm(), l, u);
            }
            TRACE("algebraic",
                  upm().display(tout, mulp.size(), mulp.c_ptr());
                  tout << ", l: " << l << ", u: " << u << "\n";
                  tout << "l_sign: " << upm().eval_sign_at(mulp.size(), mulp.c_ptr(), l) << "\n";
                  tout << "u_sign: " << upm().eval_sign_at(mulp.size(), mulp.c_ptr(), u) << "\n";
                  );
            set(c, mulp.size(), mulp.c_ptr(), l, u, a->m_minimal /* minimality is preserved */);
            normalize(c);
        }

        void mul(numeral & a, numeral & b, numeral & c) {
            if (is_zero(a) || is_zero(b)) {
                reset(c);
                return;
            }

            if (a.is_basic()) {
                if (b.is_basic())
                    mul(a.to_basic(), b.to_basic(), c);
                else
                    mul(b.to_algebraic(), a.to_basic(), c);
            }
            else {
                if (b.is_basic())
                    mul(a.to_algebraic(), b.to_basic(), c);
                else
                    mk_binary(a, b, c, mk_mul_polynomial(*this), mul_interval_proc(*this), mul_proc(*this));
            }
        }

        void neg(numeral & a) {
            if (is_zero(a))
                return;
            if (a.is_basic()) {
                qm().neg(a.to_basic()->m_value);
            }
            else {
                algebraic_cell * c = a.to_algebraic();
                upm().p_minus_x(c->m_p_sz, c->m_p);
                bqim().neg(c->m_interval);
                update_sign_lower(c);
                SASSERT(acell_inv(*c));
            }
        }

        /**
           Make sure lower != 0 and upper != 0 if a is non-basic algebraic number.
        */
        void refine_nz_bound(numeral & a) {
            if (a.is_basic())
                return;
            algebraic_cell * cell_a = a.to_algebraic();
            SASSERT(acell_inv(*cell_a));
            mpbq & _lower = cell_a->m_interval.lower();
            mpbq & _upper = cell_a->m_interval.upper();
            if (!bqm().is_zero(_lower) && !bqm().is_zero(_upper))
                return;
            auto sign_l = sign_lower(cell_a);
            SASSERT(!::is_zero(sign_l));
            auto sign_u = -sign_l;

#define REFINE_LOOP(BOUND, TARGET_SIGN)                                 \
            while (true) {                                              \
                bqm().div2(BOUND);                                      \
                sign new_sign = upm().eval_sign_at(cell_a->m_p_sz, cell_a->m_p, BOUND); \
                if (new_sign == sign_zero) {                \
                    /* found actual root */                             \
                    scoped_mpq r(qm());                                 \
                    to_mpq(qm(), BOUND, r);                             \
                    set(a, r);                                          \
                    break;                                              \
                }                                                       \
                if (new_sign == TARGET_SIGN) {                          \
                    break;                                              \
                }                                                       \
            }

            if (bqm().is_zero(_lower)) {
                bqm().set(_lower, _upper);
                REFINE_LOOP(_lower, sign_l);
            }
            else {
                SASSERT(bqm().is_zero(_upper));
                bqm().set(_upper, _lower);
                REFINE_LOOP(_upper, sign_u);
            }
            SASSERT(acell_inv(*cell_a));       
        }

        void inv(numeral & a) {
            if (is_zero(a)) {
                UNREACHABLE();
                throw algebraic_exception("division by zero");
            }
            refine_nz_bound(a);
            if (a.is_basic()) {
                qm().inv(a.to_basic()->m_value);
            }
            else {
                TRACE("algebraic_bug", tout << "before inv: "; display_root(tout, a); tout << "\n"; display_interval(tout, a); tout << "\n";);
                algebraic_cell * cell_a = a.to_algebraic();
                upm().p_1_div_x(cell_a->m_p_sz, cell_a->m_p);
                // convert binary rational bounds into rational bounds
                scoped_mpq inv_lower(qm()), inv_upper(qm());
                to_mpq(qm(), lower(cell_a), inv_lower);
                to_mpq(qm(), upper(cell_a), inv_upper);
                // (1/upper, 1/lower) is an isolating interval for the new polynomial
                qm().inv(inv_lower);
                qm().inv(inv_upper);
                qm().swap(inv_lower, inv_upper);
                TRACE("algebraic_bug", tout << "inv new_bounds: " << qm().to_string(inv_lower) << ", " << qm().to_string(inv_upper) << "\n";);
                // convert isolating interval back as a binary rational bound
                upm().convert_q2bq_interval(cell_a->m_p_sz, cell_a->m_p, inv_lower, inv_upper, bqm(), lower(cell_a), upper(cell_a));
                TRACE("algebraic_bug", tout << "after inv: "; display_root(tout, a); tout << "\n"; display_interval(tout, a); tout << "\n";);
                update_sign_lower(cell_a);
                SASSERT(acell_inv(*cell_a));       
            }
        }

        void div(numeral & a, numeral & b, numeral & c) {
            if (is_zero(b)) {
                UNREACHABLE();
                throw algebraic_exception("division by zero");
            }
            // div is not used by the nonlinear procedure.
            // I implemented just to make sure that all field operations are available in the algebraic number module.
            // It is also useful to allow users to evaluate expressions containing algebraic numbers.
            //
            // We can avoid computing invb, by having a procedure similar to mul
            // that uses
            //      Resultant(pa(xy), pb(y), y) instead of
            //      Resultant(y^n * pa(x/y), pb(y), y)
            //
            scoped_anum invb(m_wrapper);
            set(invb, b);
            inv(invb);
            mul(a, invb, c);
        }

        // Todo: move to MPQ
        ::sign compare(mpq const & a, mpq const & b) {
            if (qm().eq(a, b))
                return sign_zero;
            return qm().lt(a, b) ? sign_neg : sign_pos;
        }

        /**
          Comparing algebraic_cells with rationals
          Given an algebraic cell c with isolating interval (l, u) for p and a rational b
          Then,
          u <= b implies   c < b
          b <= l implies   c > b
          Otherwise, l < b < u, and
             p(b) <  0  --> If p(l) < 0 then c > b else c < b
             p(b) == 0  --> c = b
             p(b) >  0  --> if p(l) < 0 then c < b else c > b

             We can simplify the rules above as:
             p(b) == 0 then c == b
             (p(b) < 0) == (p(l) < 0) then c > b else c < b
        */
        ::sign compare(algebraic_cell * c, mpq const & b) {
            mpbq const & l = lower(c);
            mpbq const & u = upper(c);
            if (bqm().le(u, b))
                return sign_neg;
            if (bqm().ge(l, b))
                return sign_pos;
            // b is in the isolating interval (l, u)
            auto sign_b = upm().eval_sign_at(c->m_p_sz, c->m_p, b);
            if (sign_b == sign_zero)
                return sign_zero;
            return sign_b == sign_lower(c) ? sign_pos : sign_neg;
        }

        // Return true if the polynomials of cell_a and cell_b are the same.
        bool compare_p(algebraic_cell const * cell_a, algebraic_cell const * cell_b) {
            return upm().eq(cell_a->m_p_sz, cell_a->m_p, cell_b->m_p_sz, cell_b->m_p);
        }

        ::sign compare_core(numeral & a, numeral & b) {
            SASSERT(!a.is_basic() && !b.is_basic());
            algebraic_cell * cell_a = a.to_algebraic();
            algebraic_cell * cell_b = b.to_algebraic();
            mpbq const & a_lower = lower(cell_a);
            mpbq const & a_upper = upper(cell_a);
            mpbq const & b_lower = lower(cell_b);
            mpbq const & b_upper = upper(cell_b);

            #define COMPARE_INTERVAL()                  \
            if (bqm().le(a_upper, b_lower)) {           \
                m_compare_cheap++;                      \
                return sign_neg;                        \
            }                                           \
            if (bqm().ge(a_lower, b_upper)) {           \
                m_compare_cheap++;                      \
                return sign_pos;                        \
            }

            COMPARE_INTERVAL();

            // if cell_a and cell_b, contain the same polynomial,
            // and the intervals are overlapping, then they are
            // the same root.
            if (compare_p(cell_a, cell_b)) {
                m_compare_poly_eq++;
                return sign_zero;
            }

            TRACE("algebraic", tout << "comparing\n";
                  tout << "a: "; upm().display(tout, cell_a->m_p_sz, cell_a->m_p); tout << "\n"; bqim().display(tout, cell_a->m_interval);
                  tout << "\ncell_a->m_minimal: " << cell_a->m_minimal << "\n";
                  tout << "b: "; upm().display(tout, cell_b->m_p_sz, cell_b->m_p); tout << "\n"; bqim().display(tout, cell_b->m_interval);
                  tout << "\ncell_b->m_minimal: " << cell_b->m_minimal << "\n";);

            if (cell_a->m_minimal && cell_b->m_minimal) {
                // Minimal polynomial special case.
                // This branch is only executed when polynomial
                // factorization is turned on.

                // If a and b are defined by minimal distinct polynomials,
                // then they MUST BE DIFFERENT.
                // Thus, if we keep refining the interval of a and b,
                // eventually they will not overlap
                while (m_limit.inc()) {
                    refine(a);
                    refine(b);
                    m_compare_refine++;
                    // refine can't reduce a and b to rationals,
                    // since the polynomial is minimal and it is not linear.
                    // So, the roots are NOT rational.
                    SASSERT(!a.is_basic());
                    SASSERT(!b.is_basic());
                    COMPARE_INTERVAL();
                }
            }

            if (!m_limit.inc())
                return sign_zero;

            // make sure that intervals of a and b have the same magnitude
            int a_m      = magnitude(a_lower, a_upper);
            int b_m      = magnitude(b_lower, b_upper);
            int target_m = std::max(m_min_magnitude, std::min(a_m, b_m));
            if (b_m > target_m) {
                if (!refine(b, b_m - target_m))
                    return compare(a, b);
                m_compare_refine += b_m - target_m;
                COMPARE_INTERVAL();
            }
            if (a_m > target_m) {
                if (!refine(a, a_m - target_m))
                    return compare(a, b);
                m_compare_refine += a_m - target_m;
                COMPARE_INTERVAL();
            }

            if (target_m > m_min_magnitude) {
                int num_refinements = target_m - m_min_magnitude;
                for (int i = 0; i < num_refinements; i++) {
                    if (!refine(a) || !refine(b))
                        return compare(a, b);
                    m_compare_refine++;
                    COMPARE_INTERVAL();
                }
            }

           // EXPENSIVE CASE
           // Let seq be the Sturm-Tarski sequence for
           //       p_a, p_a' * p_b
           // Let s_l be the number of sign variations at a_lower.
           // Let s_u be the number of sign variations at a_upper.
           // By Sturm-Tarski Theorem, we have that
           // V = s_l - s_u = #(p_b(r) > 0) - #(p_b(r) < 0) at roots r of p_a
           // Since there is only one root of p_a in (a_lower, b_lower),
           // we are evaluating the sign of p_b at a.
           // That is V is the sign of p_b at a.
           //
           // We have
           //    V <  0 -> p_b(a) < 0  -> if p_b(b_lower) < 0 then b > a else b < a
           //    V == 0 -> p_b(a) == 0 -> a = b
           //    V >  0 -> p_b(a) > 0  -> if p_b(b_lower) > 0 then b > a else b < a
           //    Simplifying we have:
           //       V == 0 -->  a = b
           //       if (V < 0) == (p_b(b_lower) < 0) then b > a else b < a
           //

           m_compare_sturm++;
           upolynomial::scoped_upolynomial_sequence seq(upm());
           upm().sturm_tarski_seq(cell_a->m_p_sz, cell_a->m_p, cell_b->m_p_sz, cell_b->m_p, seq);
           unsigned V1 = upm().sign_variations_at(seq, a_lower);
           unsigned V2 = upm().sign_variations_at(seq, a_upper); 
           int V =  V1 - V2;
           TRACE("algebraic", tout << "comparing using sturm\n"; display_interval(tout, a); tout << "\n"; display_interval(tout, b); tout << "\n";
                 tout << "V: " << V << " V1 " << V1 << " V2 " << V2 << " sign_lower(a): " << sign_lower(cell_a) << ", sign_lower(b): " << sign_lower(cell_b) << "\n";);
           if (V == 0)
               return sign_zero;
           if ((V < 0) == (sign_lower(cell_b) < 0))
               return sign_neg;
           else
               return sign_pos;

           // Here is an unexplored option for comparing numbers.
           //
           // The isolating intervals of a and b are still overlapping
           // Then we compute
           //    r(x) = Resultant(x - y1 + y2, p1(y1), p2(y2))
           //    where p1(y1) and p2(y2) are the polynomials defining a and b.
           // Remarks:
           //    1) The resultant r(x) must not be the zero polynomial,
           //       since the polynomial x - y1 + y2 does not vanish in any of the roots of p1(y1) and p2(y2)
           //
           //    2) By resultant calculus, If alpha, beta1, beta2 are roots of x - y1 + y2, p1(y1), p2(y2)
           //       then alpha is a root of r(x).
           //       Thus, we have that a - b is a root of r(x)
           //
           //    3) If 0 is not a root of r(x), then a != b (by remark 2)
           //
           //    4) Let (l1, u1) and (l2, u2) be the intervals of a and b.
           //       Then, a - b must be in (l1 - u2, u1 - l2)
           //
           //    5) Assume a != b, then if we keep refining the isolating intervals for a and b,
           //       then eventually, (l1, u1) and (l2, u2) will not overlap.
           //       Thus, if 0 is not a root of r(x), we can keep refining until
           //       the intervals do not overlap.
           //
           //    6) If 0 is a root of r(x), we have two possibilities:
           //       a) Isolate roots of r(x) in the interval (l1 - u2, u1 - l2),
           //          and then keep refining (l1, u1) and (l2, u2) until they
           //          (l1 - u2, u1 - l2) "convers" only one root.
           //
           //       b) Compute the sturm sequence for r(x),
           //          keep refining the (l1, u1) and (l2, u2) until
           //          (l1 - u2, u1 - l2) contains only one root of r(x)
        }

        ::sign compare(numeral & a, numeral & b) {
            TRACE("algebraic", tout << "comparing: "; display_interval(tout, a); tout << " "; display_interval(tout, b); tout << "\n";);
            if (a.is_basic()) {
                if (b.is_basic())
                    return compare(basic_value(a), basic_value(b));
                else
                    return -compare(b.to_algebraic(), basic_value(a));
            }
            else {
                if (b.is_basic())
                    return compare(a.to_algebraic(), basic_value(b));
                else
                    return compare_core(a, b);
            }
        }

        bool eq(numeral & a, numeral & b) {
            return compare(a, b) == 0;
        }

        bool eq(numeral & a, mpq const & b) {
            if (a.is_basic())
                return qm().eq(basic_value(a), b);
            else
                return compare(a.to_algebraic(), b) == 0;
        }

        bool lt(numeral & a, numeral & b) {
            return compare(a, b) < 0;
        }

        bool lt(numeral & a, mpq const & b) {
            if (a.is_basic())
                return qm().lt(basic_value(a), b);
            else
                return compare(a.to_algebraic(), b) < 0;
        }

        bool gt(numeral & a, mpq const & b) {
            if (a.is_basic())
                return qm().gt(basic_value(a), b);
            else
                return compare(a.to_algebraic(), b) > 0;
        }

        void get_polynomial(numeral const & a, svector<mpz> & r) {
            if (a.is_basic()) {
                r.reserve(2);
                if (is_zero(a)) {
                    qm().set(r[0], 0);
                    qm().set(r[1], 1);
                }
                else {
                    mpq const & v = basic_value(a);
                    qm().set(r[0], v.numerator());
                    qm().set(r[1], v.denominator());
                    qm().neg(r[0]);
                }
                upm().set_size(2, r);
            }
            else {
                algebraic_cell * c = a.to_algebraic();
                upm().set(c->m_p_sz, c->m_p, r);
            }
        }

        /**
           \brief "Optimistic" mapping: it assumes all variables are mapped to
           basic_values (rationals). Throws an exception if that is not the case.
        */
        struct opt_var2basic : public polynomial::var2mpq {
            struct failed {};
            imp & m_imp;
            polynomial::var2anum const & m_x2v;
            opt_var2basic(imp & i, polynomial::var2anum const & x2v):m_imp(i), m_x2v(x2v) {}
            unsynch_mpq_manager & m() const override { return m_imp.qm(); }
            bool contains(polynomial::var x) const override { return m_x2v.contains(x); }
            mpq const & operator()(polynomial::var x) const override {
                anum const & v = m_x2v(x);
                if (!v.is_basic())
                    throw failed();
                return m_imp.basic_value(v);
            }
        };

        /**
           \brief Reduced mapping which contains only the rational values
        */
        struct var2basic : public polynomial::var2mpq {
            imp & m_imp;
            polynomial::var2anum const & m_x2v;
            var2basic(imp & i, polynomial::var2anum const & x2v):m_imp(i), m_x2v(x2v) {}
            unsynch_mpq_manager & m() const override { return m_imp.qm(); }
            bool contains(polynomial::var x) const override { return m_x2v.contains(x) && m_x2v(x).is_basic(); }
            mpq const & operator()(polynomial::var x) const override {
                anum const & v = m_x2v(x);
                SASSERT(v.is_basic());
                TRACE("var2basic", tout << "getting value of x" << x << " -> " << m().to_string(m_imp.basic_value(v)) << "\n";);
                return m_imp.basic_value(v);
            }
        };

        /**
           \brief Reduced mapping which contains only the non-basic values as intervals
        */
        struct var2interval : public polynomial::var2mpbqi {
            imp & m_imp;
            polynomial::var2anum const & m_x2v;
            var2interval(imp & i, polynomial::var2anum const & x2v):m_imp(i), m_x2v(x2v) {}
            mpbqi_manager & m() const override { return m_imp.bqim(); }
            bool contains(polynomial::var x) const override { return m_x2v.contains(x) && !m_x2v(x).is_basic(); }
            mpbqi const & operator()(polynomial::var x) const override {
                anum const & v = m_x2v(x);
                SASSERT(!v.is_basic());
                return v.to_algebraic()->m_interval;
            }
        };

        polynomial::var_vector m_eval_sign_vars;
        sign eval_sign_at(polynomial_ref const & p, polynomial::var2anum const & x2v) {
            polynomial::manager & ext_pm = p.m();
            TRACE("anum_eval_sign", tout << "evaluating sign of: " << p << "\n";);
            while (true) {
                bool restart = false;
                // Optimistic: maybe x2v contains only rational values
                try {
                    opt_var2basic x2v_basic(*this, x2v);
                    scoped_mpq r(qm());
                    ext_pm.eval(p, x2v_basic, r);
                    TRACE("anum_eval_sign", tout << "all variables are assigned to rationals, value of p: " << r << "\n";);
                    return ::to_sign(qm().sign(r));
                }
                catch (const opt_var2basic::failed &) {
                    // continue
                }

                // Eliminate rational values from p
                polynomial_ref p_prime(ext_pm);
                var2basic x2v_basic(*this, x2v);
                p_prime = ext_pm.substitute(p, x2v_basic);
                TRACE("anum_eval_sign", tout << "p after eliminating rationals: " << p_prime << "\n";);

                if (ext_pm.is_zero(p_prime)) {
                    // polynomial vanished after substituting rational values.
                    return sign_zero;
                }

                if (is_const(p_prime)) {
                    // polynomial became the constant polynomial after substitution.
                    SASSERT(size(p_prime) == 1);
                    return to_sign(ext_pm.m().sign(ext_pm.coeff(p_prime, 0)));
                }

                // Try to find sign using intervals
                polynomial::var_vector & xs = m_eval_sign_vars;
                xs.reset();
                ext_pm.vars(p_prime, xs);
                SASSERT(!xs.empty());
                var2interval x2v_interval(*this, x2v);
                scoped_mpbqi ri(bqim());

                while (true) {
                    checkpoint();
                    ext_pm.eval(p_prime, x2v_interval, ri);
                    TRACE("anum_eval_sign", tout << "evaluating using intervals: " << ri << "\n";);
                    if (!bqim().contains_zero(ri)) {
                        return bqim().is_pos(ri) ? sign_pos : sign_neg;
                    }
                    // refine intervals if magnitude > m_min_magnitude
                    bool refined = false;
                    for (unsigned i = 0; i < xs.size(); i++) {
                        polynomial::var x = xs[i];
                        SASSERT(x2v.contains(x));
                        anum const & v = x2v(x);
                        SASSERT(!v.is_basic());
                        algebraic_cell * c = v.to_algebraic();
                        int m = magnitude(c);
                        if (m > m_min_magnitude || (m_zero_accuracy > 0 && m > m_zero_accuracy)) {
                            if (!refine(const_cast<anum&>(v))) {
                                // v became a basic value
                                restart = true;
                                break;
                            }
                            TRACE("anum_eval_sign", tout << "refined algebraic interval\n";);
                            SASSERT(!v.is_basic());
                            refined = true;
                        }
                    }
                    if (!refined || restart) {
                        // Stop if no interval was refined OR some algebraic cell became basic
                        break;
                    }
                }

                if (restart) {
                    // Some non-basic value became basic.
                    // So, restarting the whole process
                    TRACE("anum_eval_sign", tout << "restarting some algebraic_cell became basic\n";);
                    continue;
                }

                // At this point, we are almost sure that p is zero at x2n
                // That is, rin is probably a very small interval that contains zero.

                // Remark: m_zero_accuracy == 0 means use precise computation.
                if (m_zero_accuracy > 0) {
                    // assuming the value is 0, since the result is in (-1/2^k, 1/2^k), where m_zero_accuracy = k
                    return sign_zero;
                }
#if 0
                // Evaluating sign using algebraic arithmetic
                scoped_anum ra(m_wrapper);
                ext_pm.eval(p_prime, x2v, ra);
                TRACE("anum_eval_sign", tout << "value of p as algebraic number " << ra << "\n";);
                if (is_zero(ra))
                    return 0;
                return is_pos(ra) ? 1 : -1;
#else
                // Evaluating the sign using Resultants
                // Basic idea:
                // We want to evaluate the sign of
                // p(x_1, ..., x_n)
                // at x_1 -> v_1, ..., x_n -> v_n
                //
                // Let v be p(v_1, ..., v_n).
                // We want to know the sign of v.
                //
                // Assume v_i's are defined by the polynomials q_i(x_i)
                // Then, we have that
                // the polynomials
                // y - p(x_1, ..., x_n), q_1(x_1), ..., q_n(x_n)
                // are zero at y -> v, x_1 -> v_1, ..., x_n -> v_n
                //
                // Thus, by resultant theory, v is also a root of
                // R(y) = Resultant(p(x_1, ..., x_n), q_1(x_1), ..., q_n(x_n))
                // Remark: R(y) is not the zero polynomial, since
                // the coefficient of y in the polynomial y - p(x_1, ..., x_n)
                // is (the constant polynomial) one.
                //
                // Now, let L be a lower bound on the nonzero roots of R(y).
                // Thus, any root alpha of R(y) is zero or |alpha| > L
                //
                // Therefore, we have that |v| > L
                // Now, using L, we can keep refining the interval ri which contains v.
                // Eventually, ri will not contain zero (and consequently v != 0),
                // or ri is in (-L, L), and consequently v = 0.
                polynomial::var y = get_max_var(xs) + 1;
                ensure_num_vars(y+1);
                // we create all polynomials in the local polynomial manager because we need an extra variable y
                polynomial_ref yp(pm());
                yp = pm().mk_polynomial(y);
                polynomial_ref p_prime_aux(pm());
                p_prime_aux = convert(ext_pm, p_prime, pm());
                polynomial_ref R(pm());
                R = yp - p_prime_aux;
                // compute the resultants
                polynomial_ref q_i(pm());
                std::stable_sort(xs.begin(), xs.end(), var_degree_lt(*this, x2v));
                for (unsigned i = 0; i < xs.size(); i++) {
                    checkpoint();
                    polynomial::var x_i = xs[i];
                    SASSERT(x2v.contains(x_i));
                    anum const & v_i = x2v(x_i);
                    SASSERT(!v_i.is_basic());
                    algebraic_cell * c = v_i.to_algebraic();
                    q_i = pm().to_polynomial(c->m_p_sz, c->m_p, x_i);
                    pm().resultant(R, q_i, x_i, R);
                    SASSERT(!pm().is_zero(R));
                }
                SASSERT(pm().is_univariate(R));
                scoped_upoly & _R = m_eval_sign_tmp;
                upm().to_numeral_vector(R, _R);
                unsigned k = upm().nonzero_root_lower_bound(_R.size(), _R.c_ptr());
                TRACE("anum_eval_sign", tout << "R: " << R << "\nk: " << k << "\nri: "<< ri << "\n";);
                scoped_mpbq mL(bqm()), L(bqm());
                bqm().set(mL, -1);
                bqm().set(L,   1);
                bqm().div2k(mL, k);
                bqm().div2k(L, k);
                if (bqm().lt(mL, ri.lower()) && bqm().lt(ri.upper(), L))
                    return sign_zero;
                // keep refining ri until ri is inside (-L, L) or
                // ri does not contain zero.

                // The invervals (for the values of the variables in xs) are going to get too small.
                // So, we save them before refining...
                scoped_ptr_vector<save_intervals> saved_intervals;
                for (unsigned i = 0; i < xs.size(); i++) {
                    polynomial::var x_i = xs[i];
                    SASSERT(x2v.contains(x_i));
                    anum const & v_i = x2v(x_i);
                    SASSERT(!v_i.is_basic());
                    saved_intervals.push_back(alloc(save_intervals, *this, v_i));
                }

                // Actual refinement loop
                restart = false;
                while (!restart) {
                    checkpoint();
                    ext_pm.eval(p_prime, x2v_interval, ri);
                    TRACE("anum_eval_sign", tout << "evaluating using intervals: " << ri << "\n";
                          tout << "zero lower bound is: " << L << "\n";);
                    if (!bqim().contains_zero(ri)) {
                        return bqim().is_pos(ri) ? sign_pos : sign_neg;
                    }

                    if (bqm().lt(mL, ri.lower()) && bqm().lt(ri.upper(), L))
                        return sign_zero;

                    for (auto x : xs) {
                        SASSERT(x2v.contains(x));
                        anum const & v = x2v(x);
                        SASSERT(!v.is_basic());
                        if (!refine(const_cast<anum&>(v))) {
                            // v became a basic value
                            restart = true;
                            break;
                        }
                        TRACE("anum_eval_sign", tout << "refined algebraic interval\n";);
                        SASSERT(!v.is_basic());
                    }
                }
#endif
            }
        }

        // Functor used to sort variables by the degree of the polynomial used to represent their value.
        struct var_degree_lt {
            imp & m_imp;
            polynomial::var2anum const & m_x2v;

            var_degree_lt(imp & i, polynomial::var2anum const & x2v):
                m_imp(i),
                m_x2v(x2v) {
            }

            unsigned degree(polynomial::var x) const {
                if (!m_x2v.contains(x))
                    return UINT_MAX;
                return m_imp.degree(m_x2v(x));
            }

            bool operator()(polynomial::var x1, polynomial::var x2) const {
                return degree(x1) < degree(x2);
            }
        };

        // Add entry x->v to existing mapping
        struct ext_var2num : public polynomial::var2anum {
            manager & m_am;
            polynomial::var2anum const & m_x2v;
            polynomial::var m_x;
            anum const & m_v;
            ext_var2num(manager & am, polynomial::var2anum const & x2v, polynomial::var x, anum const & v):
                m_am(am),
                m_x2v(x2v),
                m_x(x),
                m_v(v) {
            }
            manager & m() const override { return m_am; }
            bool contains(polynomial::var x) const override { return x == m_x || m_x2v.contains(x); }
            anum const & operator()(polynomial::var x) const override {
                if (x == m_x)
                    return m_v;
                else
                    return m_x2v(x);
            }
        };

        // Remove from roots any solution r such that p does not evaluate to 0 at x2v extended with x->r.
        void filter_roots(polynomial_ref const & p, polynomial::var2anum const & x2v, polynomial::var x, numeral_vector & roots) {
            TRACE("isolate_roots", tout << "before filtering roots, x: x" << x << "\n";
                  for (unsigned i = 0; i < roots.size(); i++) {
                      display_root(tout, roots[i]); tout << "\n";
                  });

            unsigned sz = roots.size();
            unsigned j  = 0;
            for (unsigned i = 0; i < sz; i++) {
                checkpoint();
                ext_var2num ext_x2v(m_wrapper, x2v, x, roots[i]);
                TRACE("isolate_roots", tout << "filter_roots i: " << i << ", ext_x2v: x" << x << " -> "; display_root(tout, roots[i]); tout << "\n";);
                sign sign = eval_sign_at(p, ext_x2v);
                TRACE("isolate_roots", tout << "filter_roots i: " << i << ", result sign: " << sign << "\n";);
                if (sign != 0)
                    continue;
                if (i != j)
                    set(roots[j], roots[i]);
                j++;
            }
            for (unsigned i = j; i < sz; i++)
                del(roots[i]);
            roots.shrink(j);

            TRACE("isolate_roots", tout << "after filtering roots:\n";
                  for (unsigned i = 0; i < roots.size(); i++) {
                      display_root(tout, roots[i]); tout << "\n";
                  });
        }

        // Return the maximal variable in xs.
        static polynomial::var get_max_var(polynomial::var_vector const & xs) {
            SASSERT(!xs.empty());
            polynomial::var x = xs[0];
            for (unsigned i = 1; i < xs.size(); i++) {
                if (xs[i] > x)
                    x = xs[i];
            }
            return x;
        }

        // Ensure that local polynomial manager has at least sz vars
        void ensure_num_vars(unsigned sz) {
            while (sz > pm().num_vars())
                pm().mk_var();
            SASSERT(pm().num_vars() >= sz);
        }

        polynomial::var_vector m_isolate_roots_vars;
        void isolate_roots(polynomial_ref const & p, polynomial::var2anum const & x2v, numeral_vector & roots, bool nested_call = false) {
            TRACE("isolate_roots", tout << "isolating roots of: " << p << "\n";);
            SASSERT(roots.empty());
            polynomial::manager & ext_pm = p.m();
            if (ext_pm.is_zero(p) || ext_pm.is_const(p)) {
                TRACE("isolate_roots", tout << "p is zero or the constant polynomial\n";);
                return;
            }

            if (ext_pm.is_univariate(p)) {
                TRACE("isolate_roots", tout << "p is univariate, using univariate procedure\n";);
                isolate_roots(p, roots);
                return;
            }

            // eliminate rationals
            polynomial_ref p_prime(ext_pm);
            var2basic x2v_basic(*this, x2v);
            p_prime = ext_pm.substitute(p, x2v_basic);
            TRACE("isolate_roots", tout << "p after applying (rational fragment of) x2v:\n" << p_prime << "\n";);

            if (ext_pm.is_zero(p_prime) || ext_pm.is_const(p_prime)) {
                TRACE("isolate_roots", tout << "p is zero or the constant polynomial after applying (rational fragment of) x2v\n";);
                return;
            }

            if (ext_pm.is_univariate(p_prime)) {
                polynomial::var x = ext_pm.max_var(p_prime);
                if (x2v.contains(x)) {
                    // The remaining variable is assigned, the actual unassigned variable vanished when we replaced rational values.
                    // So, the polynomial does not have any roots
                    return;
                }
                TRACE("isolate_roots", tout << "p is univariate after applying (rational fragment of) x2v... using univariate procedure\n";);
                isolate_roots(p_prime, roots);
                return;
            }

            polynomial::var_vector & xs = m_isolate_roots_vars;
            xs.reset();
            ext_pm.vars(p_prime, xs);
            SASSERT(xs.size() > 1);

            // sort variables by the degree of the values
            std::stable_sort(xs.begin(), xs.end(), var_degree_lt(*this, x2v));
            TRACE("isolate_roots", tout << "there are " << (xs.size() - 1) << " variables assigned to nonbasic numbers...\n";);

            // last variables is the one not assigned by x2v, or the unassigned variable vanished
            polynomial::var x = xs.back();
            if (x2v.contains(x)) {
                // all remaining variables are assigned.
                // the unassigned variable vanished when we replaced the rational values.
                DEBUG_CODE({
                    for (unsigned i = 0; i < xs.size(); i++) {
                        SASSERT(x2v.contains(xs[i]));
                    }
                });
                return;
            }

            // construct univariate polynomial q which contains all roots of p_prime at x2v.
            polynomial_ref q(ext_pm);
            q = p_prime;
            polynomial_ref p_y(ext_pm);
            for (unsigned i = 0; i < xs.size() - 1; i++) {
                checkpoint();
                polynomial::var y = xs[i];
                SASSERT(x2v.contains(y));
                anum const & v = x2v(y);
                SASSERT(!v.is_basic());
                algebraic_cell * c = v.to_algebraic();
                p_y = ext_pm.to_polynomial(c->m_p_sz, c->m_p, y);
                ext_pm.resultant(q, p_y, y, q);
                TRACE("isolate_roots", tout << "resultant loop i: " << i << ", y: x" << y << "\np_y: " << p_y << "\n";
                      tout << "q: " << q << "\n";);
                if (ext_pm.is_zero(q)) {
                    SASSERT(!nested_call);
                    break;
                }
            }

            if (ext_pm.is_zero(q)) {
                TRACE("isolate_roots", tout << "q vanished\n";);
                // q may vanish at some of the other roots of the polynomial defining the values.
                // To decide if p_prime vanishes at x2v or not, we start evaluating each coefficient of p_prime at x2v
                // until we find one that is not zero at x2v.
                // In the process we will copy p_prime to the local polynomial manager, since we will need to create
                // an auxiliary variable.
                SASSERT(!nested_call);
                unsigned n = ext_pm.degree(p_prime, x);
                SASSERT(n > 0);
                if (n == 1) {
                    // p_prime is linear on p, so we just evaluate the coefficients...
                    TRACE("isolate_roots", tout << "p is linear after applying (rational fragment) of x2v\n";);
                    polynomial_ref c0(ext_pm);
                    polynomial_ref c1(ext_pm);
                    c0 = ext_pm.coeff(p_prime, x, 0);
                    c1 = ext_pm.coeff(p_prime, x, 1);
                    scoped_anum a0(m_wrapper);
                    scoped_anum a1(m_wrapper);
                    ext_pm.eval(c0, x2v, a0);
                    ext_pm.eval(c1, x2v, a1);
                    // the root must be - a0/a1 if a1 != 0
                    if (is_zero(a1)) {
                        TRACE("isolate_roots", tout << "coefficient of degree 1 vanished, so p does not have roots at x2v\n";);
                        // p_prime does not have any root
                        return;
                    }
                    roots.push_back(anum());
                    div(a0, a1, roots[0]);
                    neg(roots[0]);
                    TRACE("isolate_roots", tout << "after trivial solving p has only one root:\n"; display_root(tout, roots[0]); tout << "\n";);
                }
                else {
                    polynomial_ref c(ext_pm);
                    scoped_anum a(m_wrapper);
                    int i = n;
                    for (; i >= 1; i--) {
                        c = ext_pm.coeff(p_prime, x, i);
                        ext_pm.eval(c, x2v, a);
                        if (!is_zero(a))
                            break;
                    }
                    if (i == 0) {
                        // all coefficients of x vanished, so
                        // the polynomial has no roots
                        TRACE("isolate_roots", tout << "all coefficients vanished... polynomial does not have roots\n";);
                        return;
                    }
                    SASSERT(!is_zero(a));
                    polynomial::var z = get_max_var(xs) + 1;
                    ensure_num_vars(z+1);
                    // create polynomial q2 in the local manager
                    //   z * x^i + c_{i-1} * x^{i-1} + ... + c_1 * x + c_0
                    // where c's are the coefficients of p_prime.
                    // Then we invoke isolate_roots with q2 and x2v extended with z->a.
                    // The resultant will not vanish again because
                    // 0 is not a root of the polynomial defining a.
                    polynomial_ref q2(pm());
                    polynomial_ref z_p(pm()); // z poly
                    polynomial_ref xi_p(pm()); // x^i poly
                    polynomial_ref zxi_p(pm()); // z*x^i
                    SASSERT(i >= 1);
                    q2 = convert(ext_pm, p_prime, pm(), x, static_cast<unsigned>(i-1));
                    xi_p = pm().mk_polynomial(x, i);
                    z_p  = pm().mk_polynomial(z);
                    q2 = z_p*xi_p + q2;
                    TRACE("isolate_roots", tout << "invoking isolate_roots with q2:\n" << q2 << "\n";
                          tout << "z: x" << z << " -> "; display_root(tout, a); tout << "\n";);
                    // extend x2p with z->a
                    ext_var2num ext_x2v(m_wrapper, x2v, z, a);
                    isolate_roots(q2, ext_x2v, roots, true /* nested call */);
                }
            }
            else if (ext_pm.is_const(q)) {
                // q does not have any roots, so p_prime also does not have roots at x2v.
                TRACE("isolate_roots", tout << "q is the constant polynomial, so p does not contain any roots at x2v\n";);
            }
            else {
                SASSERT(is_univariate(q));
                isolate_roots(q, roots);
                // some roots of q may not be roots of p_prime
                filter_roots(p_prime, x2v, x, roots);
            }
        }

        sign eval_at_mpbq(polynomial_ref const & p, polynomial::var2anum const & x2v, polynomial::var x, mpbq const & v) {
            scoped_mpq  qv(qm());
            to_mpq(qm(), v, qv);
            scoped_anum av(m_wrapper);
            set(av, qv);
            ext_var2num ext_x2v(m_wrapper, x2v, x, av);
            return eval_sign_at(p, ext_x2v);
        }

        // Make sure that lower and upper of prev and curr don't touch each other
        void separate(numeral & prev, numeral & curr) {
            SASSERT(lt(prev, curr));
            if (prev.is_basic()) {
                if (curr.is_basic()) {
                    // do nothing
                }
                else {
                    while (bqm().le(lower(curr.to_algebraic()), basic_value(prev))) {
                        refine(curr);
                        if (curr.is_basic())
                            break; // curr became basic
                    }
                }
            }
            else {
                if (curr.is_basic()) {
                    while (bqm().ge(upper(prev.to_algebraic()), basic_value(curr))) {
                        refine(prev);
                        if (prev.is_basic())
                            break;
                    }
                }
                else {
                    while (bqm().ge(upper(prev.to_algebraic()), lower(curr.to_algebraic()))) {
                        refine(prev);
                        refine(curr);
                        if (prev.is_basic() || curr.is_basic())
                            break;
                    }
                }
            }
        }

        void int_lt(numeral const & a, numeral & b) {
            scoped_mpz v(qm());
            if (a.is_basic()) {
                qm().floor(basic_value(a), v);
                qm().dec(v);
            }
            else {
                bqm().floor(qm(), lower(a.to_algebraic()), v);
            }
            m_wrapper.set(b, v);
        }

        void int_gt(numeral const & a, numeral & b) {
            scoped_mpz v(qm());
            if (a.is_basic()) {
                qm().ceil(basic_value(a), v);
                qm().inc(v);
            }
            else {
                bqm().ceil(qm(), upper(a.to_algebraic()), v);
            }
            m_wrapper.set(b, v);
        }

        // Select a numeral between prev and curr.
        // Pre: prev < curr
        void select(numeral & prev, numeral & curr, numeral & result) {
            TRACE("algebraic_select",
                  tout << "prev: "; display_interval(tout, prev); tout << "\n";
                  tout << "curr: "; display_interval(tout, curr); tout << "\n";);
            SASSERT(lt(prev, curr));
            separate(prev, curr);
            scoped_mpbq w(bqm());
            if (prev.is_basic()) {
                if (curr.is_basic())
                    bqm().select_small_core(qm(), basic_value(prev), basic_value(curr), w);
                else
                    bqm().select_small_core(qm(), basic_value(prev), lower(curr.to_algebraic()), w);
            }
            else {
                if (curr.is_basic())
                    bqm().select_small_core(qm(), upper(prev.to_algebraic()), basic_value(curr), w);
                else
                    bqm().select_small_core(upper(prev.to_algebraic()), lower(curr.to_algebraic()), w);
            }
            scoped_mpq qw(qm());
            to_mpq(qm(), w, qw);
            set(result, qw);
        }

        // Similar to ext_var2num but all variables that are not mapped by x2v are mapped to the same value.
        struct ext2_var2num : public polynomial::var2anum {
            manager & m_am;
            polynomial::var2anum const & m_x2v;
            anum const & m_v;
            ext2_var2num(manager & am, polynomial::var2anum const & x2v, anum const & v):
                m_am(am),
                m_x2v(x2v),
                m_v(v) {
            }
            manager & m() const override { return m_am; }
            bool contains(polynomial::var x) const override { return true; }
            anum const & operator()(polynomial::var x) const override {
                if (m_x2v.contains(x))
                    return m_x2v(x);
                else
                    return m_v;
            }
        };

#define DEFAULT_PRECISION 2

        void isolate_roots(polynomial_ref const & p, polynomial::var2anum const & x2v, numeral_vector & roots, svector<sign> & signs) {
            isolate_roots(p, x2v, roots);
            unsigned num_roots = roots.size();
            if (num_roots == 0) {
                anum zero;
                ext2_var2num ext_x2v(m_wrapper, x2v, zero);
                sign s = eval_sign_at(p, ext_x2v);
                signs.push_back(s);
            }
            else {
                TRACE("isolate_roots_bug", tout << "p: " << p << "\n";
                      polynomial::var_vector xs;
                      p.m().vars(p, xs);
                      for (unsigned i = 0; i < xs.size(); i++) {
                          if (x2v.contains(xs[i])) {
                              tout << "x" << xs[i] << " -> ";
                              display_root(tout, x2v(xs[i]));
                              tout << " ";
                              display_interval(tout, x2v(xs[i]));
                              tout << "\n";
                          }
                      }
                      for (unsigned i = 0; i < roots.size(); i++) {
                          tout << "root[i]: "; display_root(tout, roots[i]); tout << "\n";
                      });
                for (unsigned i = 0; i < num_roots; i++)
                    refine_until_prec(roots[i], DEFAULT_PRECISION);

                scoped_anum w(m_wrapper);
                int_lt(roots[0], w);
                TRACE("isolate_roots_bug", tout << "w: "; display_root(tout, w); tout << "\n";);
                {
                    ext2_var2num ext_x2v(m_wrapper, x2v, w);
                    auto s = eval_sign_at(p, ext_x2v);
                    SASSERT(s != sign_zero);
                    signs.push_back(s);
                }

                for (unsigned i = 1; i < num_roots; i++) {
                    numeral & prev = roots[i-1];
                    numeral & curr = roots[i];
                    select(prev, curr, w);
                    ext2_var2num ext_x2v(m_wrapper, x2v, w);
                    auto s = eval_sign_at(p, ext_x2v);
                    SASSERT(s != sign_zero);
                    signs.push_back(s);
                }

                int_gt(roots[num_roots - 1], w);
                {
                    ext2_var2num ext_x2v(m_wrapper, x2v, w);
                    auto s = eval_sign_at(p, ext_x2v);
                    SASSERT(s != sign_zero);
                    signs.push_back(s);
                }
            }
        }

        void display_root(std::ostream & out, numeral const & a) {
            if (is_zero(a)) {
                out << "(#, 1)"; // first root of polynomial #
            }
            else if (a.is_basic()) {
                mpq const & v = basic_value(a);
                mpz neg_n;
                qm().set(neg_n, v.numerator());
                qm().neg(neg_n);
                mpz coeffs[2] = { std::move(neg_n), qm().dup(v.denominator()) };
                out << "(";
                upm().display(out, 2, coeffs, "#");
                out << ", 1)"; // first root of the polynomial d*# - n
                qm().del(coeffs[0]);
                qm().del(coeffs[1]);
            }
            else {
                algebraic_cell * c = a.to_algebraic();
                out << "(";
                upm().display(out, c->m_p_sz, c->m_p, "#");
                if (c->m_i == 0) {
                    // undefined
                    c->m_i = upm().get_root_id(c->m_p_sz, c->m_p, lower(c)) + 1;
                }
                SASSERT(c->m_i > 0);
                out << ", " << c->m_i;
                out << ")";
            }
        }

        void display_mathematica(std::ostream & out, numeral const & a) {
            if (a.is_basic()) {
                qm().display(out, basic_value(a));
            }
            else {
                algebraic_cell * c = a.to_algebraic();
                out << "Root[";
                upm().display(out, c->m_p_sz, c->m_p, "#1", true);
                if (c->m_i == 0) {
                    // undefined
                    c->m_i = upm().get_root_id(c->m_p_sz, c->m_p, lower(c)) + 1;
                }
                SASSERT(c->m_i > 0);
                out << " &, " << c->m_i << "]";
            }

        }

        void display_root_smt2(std::ostream & out, numeral const & a) {
            if (is_zero(a)) {
                out << "(root-obj x 1)";
            }
            else if (a.is_basic()) {
                mpq const & v = basic_value(a);
                mpz neg_n;
                qm().set(neg_n, v.numerator());
                qm().neg(neg_n);
                mpz coeffs[2] = { std::move(neg_n), qm().dup(v.denominator()) };
                out << "(root-obj ";
                upm().display_smt2(out, 2, coeffs, "x");
                out << " 1)"; // first root of the polynomial d*# - n
                qm().del(coeffs[0]);
                qm().del(coeffs[1]);
            }
            else {
                algebraic_cell * c = a.to_algebraic();
                out << "(root-obj ";
                upm().display_smt2(out, c->m_p_sz, c->m_p, "x");
                if (c->m_i == 0) {
                    // undefined
                    c->m_i = upm().get_root_id(c->m_p_sz, c->m_p, lower(c)) + 1;
                }
                SASSERT(c->m_i > 0);
                out << " " << c->m_i;
                out << ")";
            }
        }

        void display_interval(std::ostream & out, numeral const & a) {
            if (a.is_basic()) {
                out << "[";
                qm().display(out, basic_value(a));
                out << ", ";
                qm().display(out, basic_value(a));
                out << "]";
            }
            else {
                bqim().display(out, a.to_algebraic()->m_interval);
            }
        }

        bool get_interval(numeral const & a, mpbq & l, mpbq & u, unsigned precision) {
            SASSERT(!a.is_basic());
            algebraic_cell * c = a.to_algebraic();
            mpbqi const & i = c->m_interval;
            bqm().set(l, i.lower());
            bqm().set(u, i.upper());
            // the precision on refine is base 2
            return upm().refine(c->m_p_sz, c->m_p, bqm(), l, u, precision * 4);
        }

        void display_decimal(std::ostream & out, numeral const & a, unsigned precision) {
            if (a.is_basic()) {
                qm().display_decimal(out, basic_value(a), precision);
            }
            else {
                scoped_mpbq l(bqm()), u(bqm());
                if (get_interval(a, l, u, precision)) {
                    // this is a hack... fix it
                    bqm().display_decimal(out, u, precision);
                }
                else {
                    // actual root was found
                    bqm().display_decimal(out, l, precision);
                }
            }
        }

        void get_lower(numeral const & a, mpq & l, unsigned precision) {
            if (a.is_basic()) {
                qm().set(l, basic_value(a));
            }
            else {
                scoped_mpbq _l(bqm()), _u(bqm());
                get_interval(a, _l, _u, precision);
                to_mpq(qm(), _l, l);
            }
        }

        void get_upper(numeral const & a, mpq & u, unsigned precision) {
            if (a.is_basic()) {
                qm().set(u, basic_value(a));
            }
            else {
                scoped_mpbq _l(bqm()), _u(bqm());
                get_interval(a, _l, _u, precision);
                to_mpq(qm(), _u, u);
            }
        }

    };

    manager::manager(reslimit& lim, unsynch_mpq_manager & m, params_ref const & p, small_object_allocator * a) {
        m_own_allocator = false;
        m_allocator     = a;
        if (m_allocator == nullptr) {
            m_own_allocator = true;
            m_allocator     = alloc(small_object_allocator, "algebraic");
        }
        m_imp = alloc(imp, lim, *this, m, p, *m_allocator);
    }

    manager::~manager() {
        dealloc(m_imp);
        if (m_own_allocator)
            dealloc(m_allocator);
    }

    void manager::updt_params(params_ref const & p) {
    }

    unsynch_mpq_manager & manager::qm() const {
        return m_imp->qm();
    }

    mpbq_manager & manager::bqm() const {
        return m_imp->bqm();
    }

    void manager::del(numeral & a) {
        return m_imp->del(a);
    }

    void manager::reset(numeral & a) {
        return m_imp->reset(a);
    }

    bool manager::is_zero(numeral const & a) {
        return m_imp->is_zero(const_cast<numeral&>(a));
    }

    bool manager::is_pos(numeral const & a) {
        return m_imp->is_pos(const_cast<numeral&>(a));
    }

    bool manager::is_neg(numeral const & a) {
        return m_imp->is_neg(const_cast<numeral&>(a));
    }

    bool manager::is_rational(numeral const & a) {
        return m_imp->is_rational(const_cast<numeral&>(a));
    }

    bool manager::is_int(numeral const & a) {
        return m_imp->is_int(const_cast<numeral&>(a));
    }

    unsigned manager::degree(numeral const & a) {
        return m_imp->degree(const_cast<numeral&>(a));
    }

    void manager::to_rational(numeral const & a, mpq & r) {
        return m_imp->to_rational(const_cast<numeral&>(a), r);
    }

    void manager::to_rational(numeral const & a, rational & r) {
        return m_imp->to_rational(const_cast<numeral&>(a), r);
    }

    void manager::swap(numeral & a, numeral & b) {
        return m_imp->swap(a, b);
    }

    void manager::int_lt(numeral const & a, numeral & b) {
        m_imp->int_lt(const_cast<numeral&>(a), b);
    }

    void manager::int_gt(numeral const & a, numeral & b) {
        m_imp->int_gt(const_cast<numeral&>(a), b);
    }

    void manager::select(numeral const & prev, numeral const & curr, numeral & result) {
        m_imp->select(const_cast<numeral&>(prev), const_cast<numeral&>(curr), result);
    }

    void manager::set(numeral & a, int n) {
        scoped_mpq _n(qm());
        qm().set(_n, n);
        set(a, _n);
    }

    void manager::set(numeral & a, mpz const & n) {
        scoped_mpq _n(qm());
        qm().set(_n, n);
        set(a, _n);
    }

    void manager::set(numeral & a, mpq const & n) {
        m_imp->set(a, n);
    }

    void manager::set(numeral & a, numeral const & n) {
        m_imp->set(a, n);
    }

    void manager::isolate_roots(polynomial_ref const & p, numeral_vector & roots) {
        m_imp->isolate_roots(p, roots);
    }

    void manager::isolate_roots(polynomial_ref const & p, polynomial::var2anum const & x2v, numeral_vector & roots) {
        m_imp->isolate_roots(p, x2v, roots);
    }

    void manager::isolate_roots(polynomial_ref const & p, polynomial::var2anum const & x2v, numeral_vector & roots, svector<sign> & signs) {
        m_imp->isolate_roots(p, x2v, roots, signs);
    }

    void manager::mk_root(polynomial_ref const & p, unsigned i, numeral & r) {
        m_imp->mk_root(p, i, r);
    }

    void manager::mk_root(sexpr const * p, unsigned i, numeral & r) {
        m_imp->mk_root(p, i, r);
    }

    void manager::root(numeral const & a, unsigned k, numeral & b) {
        m_imp->root(const_cast<numeral&>(a), k, b);
    }

    void manager::power(numeral const & a, unsigned k, numeral & b) {
        TRACE("anum_detail", display_root(tout, a); tout << "^" << k << "\n";);
        m_imp->power(const_cast<numeral&>(a), k, b);
        TRACE("anum_detail", tout << "^ result: "; display_root(tout, b); tout << "\n";);
    }

    void manager::add(numeral const & a, numeral const & b, numeral & c) {
        TRACE("anum_detail", display_root(tout, a); tout << " + "; display_root(tout, b); tout << "\n";);
        m_imp->add(const_cast<numeral&>(a), const_cast<numeral&>(b), c);
        TRACE("anum_detail", tout << "+ result: "; display_root(tout, c); tout << "\n";);
    }

    void manager::add(numeral const & a, mpz const & b, numeral & c) {
        scoped_anum tmp(*this);
        set(tmp, b);
        add(a, tmp, c);
    }

    void manager::sub(numeral const & a, numeral const & b, numeral & c) {
        TRACE("anum_detail", display_root(tout, a); tout << " - "; display_root(tout, b); tout << "\n";);
        m_imp->sub(const_cast<numeral&>(a), const_cast<numeral&>(b), c);
        TRACE("anum_detail", tout << "- result: "; display_root(tout, c); tout << "\n";);
    }

    void manager::mul(numeral const & a, numeral const & b, numeral & c) {
        TRACE("anum_detail", display_root(tout, a); tout << " * "; display_root(tout, b); tout << "\n";);
        m_imp->mul(const_cast<numeral&>(a), const_cast<numeral&>(b), c);
        TRACE("anum_detail", tout << "* result: "; display_root(tout, c); tout << "\n";);
    }

    void manager::div(numeral const & a, numeral const & b, numeral & c) {
        m_imp->div(const_cast<numeral&>(a), const_cast<numeral&>(b), c);
    }

    void manager::neg(numeral & a) {
        m_imp->neg(a);
    }

    void manager::inv(numeral & a) {
        m_imp->inv(a);
    }

    sign manager::compare(numeral const & a, numeral const & b) {
        return m_imp->compare(const_cast<numeral&>(a), const_cast<numeral&>(b));
    }

    bool manager::eq(numeral const & a, numeral const & b) {
        return m_imp->eq(const_cast<numeral&>(a), const_cast<numeral&>(b));
    }

    bool manager::eq(numeral const & a, mpq const & b) {
        return m_imp->eq(const_cast<numeral&>(a), b);
    }

    bool manager::eq(numeral const & a, mpz const & b) {
        scoped_mpq _b(qm());
        qm().set(_b, b);
        return eq(const_cast<numeral&>(a), _b);
    }

    bool manager::lt(numeral const & a, numeral const & b) {
        return m_imp->lt(const_cast<numeral&>(a), const_cast<numeral&>(b));
    }

    bool manager::lt(numeral const & a, mpq const & b) {
        return m_imp->lt(const_cast<numeral&>(a), b);
    }

    bool manager::lt(numeral const & a, mpz const & b) {
        scoped_mpq _b(qm());
        qm().set(_b, b);
        return lt(const_cast<numeral&>(a), _b);
    }

    bool manager::gt(numeral const & a, mpq const & b) {
        return m_imp->gt(const_cast<numeral&>(a), b);
    }

    bool manager::gt(numeral const & a, mpz const & b) {
        scoped_mpq _b(qm());
        qm().set(_b, b);
        return gt(const_cast<numeral&>(a), _b);
    }

    void manager::get_polynomial(numeral const & a, svector<mpz> & r) {
        m_imp->get_polynomial(a, r);
    }

    void manager::get_lower(numeral const & a, mpbq & l) {
        SASSERT(!is_rational(a));
        bqm().set(l, a.to_algebraic()->m_interval.lower());
    }

    void manager::get_lower(numeral const & a, mpq & l) {
        scoped_mpbq bq(bqm());
        get_lower(a, bq);
        to_mpq(qm(), bq, l);
    }

    void manager::get_lower(numeral const & a, rational & l) {
        scoped_mpq q(m_imp->qm());
        get_lower(a, q);
        l = rational(q);
    }

    void manager::get_lower(numeral const & a, mpq & l, unsigned precision) {
        m_imp->get_lower(a, l, precision);
    }

    void manager::get_lower(numeral const & a, rational & l, unsigned precision) {
        scoped_mpq _l(qm());
        m_imp->get_lower(a, _l, precision);
        l = rational(_l);
    }

    void manager::get_upper(numeral const & a, mpbq & u) {
        SASSERT(!is_rational(a));
        bqm().set(u, a.to_algebraic()->m_interval.upper());
    }

    void manager::get_upper(numeral const & a, mpq & u) {
        scoped_mpbq bq(bqm());
        get_upper(a, bq);
        to_mpq(qm(), bq, u);
    }

    void manager::get_upper(numeral const & a, rational & u) {
        scoped_mpq q(m_imp->qm());
        get_upper(a, q);
        u = rational(q);
    }

    void manager::get_upper(numeral const & a, mpq & l, unsigned precision) {
        m_imp->get_upper(a, l, precision);
    }

    void manager::get_upper(numeral const & a, rational & l, unsigned precision) {
        scoped_mpq _l(qm());
        m_imp->get_upper(a, _l, precision);
        l = rational(_l);
    }

    sign manager::eval_sign_at(polynomial_ref const & p, polynomial::var2anum const & x2v) {
        SASSERT(&(x2v.m()) == this);
        return m_imp->eval_sign_at(p, x2v);
    }

    void manager::display_interval(std::ostream & out, numeral const & a) const {
        m_imp->display_interval(out, a);
    }

    void manager::display_decimal(std::ostream & out, numeral const & a, unsigned precision) const {
        m_imp->display_decimal(out, a, precision);
    }

    void manager::display_root(std::ostream & out, numeral const & a) const {
        m_imp->display_root(out, a);
    }

    void manager::display_mathematica(std::ostream & out, numeral const & a) const {
        m_imp->display_mathematica(out, a);
    }

    void manager::display_root_smt2(std::ostream & out, numeral const & a) const {
        m_imp->display_root_smt2(out, a);
    }

    void manager::reset_statistics() {
        m_imp->reset_statistics();
    }

    void manager::collect_statistics(statistics & st) const {
        m_imp->collect_statistics(st);
    }
};
