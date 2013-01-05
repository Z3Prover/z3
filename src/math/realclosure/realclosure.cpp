/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    realclosure.cpp

Abstract:

    Package for computing with elements of the realclosure of a field containing
       - all rationals
       - extended with computable transcendental real numbers (e.g., pi and e)
       - infinitesimals

Author:

    Leonardo (leonardo) 2013-01-02

Notes:

--*/
#include"realclosure.h"
#include"array.h"
#include"mpbq.h"
#include"interval_def.h"
#include"obj_ref.h"
#include"ref_vector.h"
#include"ref_buffer.h"

#ifndef REALCLOSURE_INI_BUFFER_SIZE
#define REALCLOSURE_INI_BUFFER_SIZE 32
#endif

#ifndef REALCLOSURE_INI_SEQ_SIZE
#define REALCLOSURE_INI_SEQ_SIZE 256
#endif

#ifndef REALCLOSURE_INI_DIV_PRECISION
#define REALCLOSURE_INI_DIV_PRECISION 24
#endif

namespace realclosure {
    
    // ---------------------------------
    //
    // Intervals with binary rational endpoints
    //
    // ---------------------------------

    struct mpbq_config {

        struct numeral_manager : public mpbq_manager {
            unsigned m_div_precision;
            bool     m_to_plus_inf;
            
            numeral_manager(unsynch_mpq_manager & qm):mpbq_manager(qm), m_div_precision(REALCLOSURE_INI_DIV_PRECISION), m_to_plus_inf(true) {
            }

            void div(mpbq const & a, mpbq const & b, mpbq & c) {
                approx_div(a, b, c, m_div_precision, m_to_plus_inf);
            }

            void inv(mpbq & a) {
                mpbq one(1);
                scoped_mpbq r(*this);
                approx_div(one, a, r, m_div_precision, m_to_plus_inf);
                swap(a, r);
            }
        };

        typedef mpbq         numeral;
        numeral_manager &    m_manager;

        struct interval {
            numeral   m_lower;
            numeral   m_upper;
            unsigned  m_lower_inf:1;
            unsigned  m_upper_inf:1;
            unsigned  m_lower_open:1;
            unsigned  m_upper_open:1;
            interval():m_lower_inf(true), m_upper_inf(true), m_lower_open(true), m_upper_open(true) {}
            interval(numeral & l, numeral & u):m_lower_inf(false), m_upper_inf(false), m_lower_open(true), m_upper_open(true) {
                swap(m_lower, l);
                swap(m_upper, u);
            }
            numeral & lower() { return m_lower; }
            numeral & upper() { return m_upper; }
            void set_lower_is_inf(bool f) { m_lower_inf = f; }
            void set_upper_is_inf(bool f) { m_upper_inf = f; }
            void set_lower_is_open(bool f) { m_lower_open = f; }
            void set_upper_is_open(bool f) { m_upper_open = f; }
            numeral const & lower() const { return m_lower; }
            numeral const & upper() const { return m_upper; }
            bool lower_is_inf() const { return m_lower_inf; }
            bool upper_is_inf() const { return m_upper_inf; }
            bool lower_is_open() const { return m_lower_open; }
            bool upper_is_open() const { return m_upper_open; }
        };

        void set_rounding(bool to_plus_inf) { m_manager.m_to_plus_inf = to_plus_inf; }
        void round_to_minus_inf() { set_rounding(false); }
        void round_to_plus_inf() { set_rounding(true); }
        
        // Getters
        numeral const & lower(interval const & a) const { return a.m_lower; }
        numeral const & upper(interval const & a) const { return a.m_upper; }
        numeral & lower(interval & a) { return a.m_lower; }
        numeral & upper(interval & a) { return a.m_upper; }
        bool lower_is_open(interval const & a) const { return a.m_lower_open; }
        bool upper_is_open(interval const & a) const { return a.m_upper_open; }
        bool lower_is_inf(interval const & a) const { return a.m_lower_inf; }
        bool upper_is_inf(interval const & a) const { return a.m_upper_inf; }
        
        // Setters
        void set_lower(interval & a, numeral const & n) { m_manager.set(a.m_lower, n); }
        void set_upper(interval & a, numeral const & n) { m_manager.set(a.m_upper, n); }
        void set_lower_is_open(interval & a, bool v) { a.m_lower_open = v; }
        void set_upper_is_open(interval & a, bool v) { a.m_upper_open = v; }
        void set_lower_is_inf(interval & a, bool v) { a.m_lower_inf = v; }
        void set_upper_is_inf(interval & a, bool v) { a.m_upper_inf = v; }
        
        // Reference to numeral manager
        numeral_manager & m() const { return m_manager; }
        
        mpbq_config(numeral_manager & m):m_manager(m) {}
    };
    
    typedef interval_manager<mpbq_config> mpbqi_manager;
    typedef mpbqi_manager::interval       mpbqi;

    void swap(mpbqi & a, mpbqi & b) {
        swap(a.m_lower, b.m_lower);
        swap(a.m_upper, b.m_upper);
        unsigned tmp;
        tmp = a.m_lower_inf; a.m_lower_inf = b.m_lower_inf; b.m_lower_inf = tmp;
        tmp = a.m_upper_inf; a.m_upper_inf = b.m_upper_inf; b.m_upper_inf = tmp;
    }

    // ---------------------------------
    //
    // Values are represented as
    //   - arbitrary precision rationals (mpq)
    //   - rational functions on field extensions
    //
    // ---------------------------------

    struct value {
        unsigned m_ref_count; //!< Reference counter
        bool     m_rational;  //!< True if the value is represented as an abitrary precision rational value.
        mpbqi    m_interval;  //!< approximation as an interval with binary rational end-points
        value(bool rat):m_ref_count(0), m_rational(rat) {}
        bool is_rational() const { return m_rational; }
        mpbqi const & interval() const { return m_interval; }
        mpbqi & interval() { return m_interval; }
    };

    struct rational_value : public value {
        mpq      m_value;
        rational_value():value(true) {}
    };

    typedef ptr_array<value> polynomial;
    
    struct extension;
    bool rank_lt(extension * r1, extension * r2);

    struct rational_function_value : public value {
        polynomial   m_numerator;
        polynomial   m_denominator;
        extension *  m_ext;
        bool         m_real; //!< True if the polynomial expression does not depend on infinitesimal values.
        rational_function_value(extension * ext):value(false), m_ext(ext), m_real(false) {}
        
        polynomial const & num() const { return m_numerator; }
        polynomial & num() { return m_numerator; }
        polynomial const & den() const { return m_denominator; }
        polynomial & den() { return m_denominator; }

        extension * ext() const { return m_ext; }
        bool is_real() const { return m_real; }
        void set_real(bool f) { m_real = f; }
    };

    typedef ptr_vector<value> value_vector;

    // ---------------------------------
    //
    // Root object definition
    //
    // ---------------------------------
    
    typedef int sign;

    typedef std::pair<polynomial, sign> p2s;

    typedef sarray<p2s> signs;

    struct extension {
        enum kind {
            TRANSCENDENTAL = 0,
            INFINITESIMAL  = 1,
            ALGEBRAIC      = 2
        };

        unsigned m_ref_count;
        unsigned m_kind:2;
        unsigned m_idx:30;
        mpbqi    m_interval;

        extension(kind k, unsigned idx):m_ref_count(0), m_kind(k), m_idx(idx) {}

        unsigned idx() const { return m_idx; }
        kind knd() const { return static_cast<kind>(m_kind); }

        bool is_algebraic() const { return knd() == ALGEBRAIC; }
        bool is_infinitesimal() const { return knd() == INFINITESIMAL; }
        bool is_transcendental() const { return knd() == TRANSCENDENTAL; }

        mpbqi const & interval() const { return m_interval; }
        mpbqi & interval() { return m_interval; }
    };

    bool rank_lt(extension * r1, extension * r2) {
        return r1->knd() < r2->knd() || (r1->knd() == r2->knd() && r1->idx() < r2->idx()); 
    }

    bool rank_eq(extension * r1, extension * r2) {
        return r1->knd() == r2->knd() && r1->idx() == r2->idx(); 
    }

    struct rank_lt_proc {
        bool operator()(extension * r1, extension * r2) const {
            return rank_lt(r1, r2);
        }
    };

    struct algebraic : public extension {
        polynomial   m_p;
        signs        m_signs;
        bool         m_real;  //!< True if the polynomial p does not depend on infinitesimal extensions.

        algebraic(unsigned idx):extension(ALGEBRAIC, idx), m_real(false) {}

        polynomial const & p() const { return m_p; }
        signs const & s() const { return m_signs; }
        bool is_real() const { return m_real; }
    };

    struct transcendental : public extension {
        symbol        m_name;
        mk_interval & m_proc;
        
        transcendental(unsigned idx, symbol const & n, mk_interval & p):extension(TRANSCENDENTAL, idx), m_name(n), m_proc(p) {}

        void display(std::ostream & out) const {
            out << m_name;
        }
    };
    
    struct infinitesimal : public extension {
        symbol        m_name;
 
        infinitesimal(unsigned idx, symbol const & n):extension(INFINITESIMAL, idx), m_name(n) {}

        void display(std::ostream & out) const {
            if (m_name.is_numerical())
                out << "eps!" << m_name.get_num();
            else
                out << m_name;
        }
    };

    struct manager::imp {
        typedef ref_vector<value, imp> value_ref_vector;
        typedef ref_buffer<value, imp, REALCLOSURE_INI_BUFFER_SIZE> value_ref_buffer;
        typedef obj_ref<value, imp>    value_ref;
        
        small_object_allocator *       m_allocator;
        bool                           m_own_allocator;
        unsynch_mpq_manager &          m_qm;
        mpbq_config::numeral_manager   m_bqm;
        mpqi_manager                   m_qim;
        mpbqi_manager                  m_bqim;
        ptr_vector<extension>          m_extensions[3];
        value *                        m_one;
        unsigned                       m_ini_precision; //!< initial precision for transcendentals, infinitesimals, etc.
        volatile bool                  m_cancel;

        struct scoped_polynomial_seq {
            typedef ref_buffer<value, imp, REALCLOSURE_INI_SEQ_SIZE> value_seq;
            value_seq          m_seq_coeffs;
            sbuffer<unsigned>  m_begins;     // start position (in m_seq_coeffs) of each polynomial in the sequence
            sbuffer<unsigned>  m_szs;        // size of each polynomial in the sequence 
        public:
            scoped_polynomial_seq(imp & m):m_seq_coeffs(m) {}
            
            /**
               \brief Add a new polynomial to the sequence.
               The contents of p is erased.
            */
            void push(unsigned sz, value * const * p) {
                m_begins.push_back(m_seq_coeffs.size());
                m_szs.push_back(sz);
                m_seq_coeffs.append(sz, p);
            }

            /**
               \brief Return the number of polynomials in the sequence.
            */
            unsigned size() const { return m_szs.size(); }
            
            /**
               \brief Return the vector of coefficients for the i-th polynomial in the sequence.
            */
            value * const * coeffs(unsigned i) const { 
                return m_seq_coeffs.c_ptr() + m_begins[i]; 
            }
        
            /**
               \brief Return the size of the i-th polynomial in the sequence.
            */
            unsigned size(unsigned i) const { return m_szs[i]; }

            void reset() {
                m_seq_coeffs.reset();
                m_begins.reset();
                m_szs.reset();
            }
        };
        
        imp(unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a):
            m_allocator(a == 0 ? alloc(small_object_allocator, "realclosure") : a),
            m_own_allocator(a == 0),
            m_qm(qm),
            m_bqm(m_qm),
            m_qim(m_qm),
            m_bqim(m_bqm) {
            mpq one(1);
            m_one = mk_rational(one);
            inc_ref(m_one);
            m_cancel = false;
            
            updt_params(p);
        }

        ~imp() {
            dec_ref(m_one);
            if (m_own_allocator)
                dealloc(m_allocator);
        }

        unsynch_mpq_manager & qm() const { return m_qm; }
        mpbq_manager & bqm() { return m_bqm; }
        mpqi_manager & qim() { return m_qim; }
        mpbqi_manager & bqim() { return m_bqim; }
        mpbqi_manager const & bqim() const { return m_bqim; }
        small_object_allocator & allocator() { return *m_allocator; }

        void checkpoint() {
            // TODO
        }

        value * one() const {
            return m_one;
        }

        void cleanup(extension::kind k) {
            ptr_vector<extension> & exts = m_extensions[k];
            // keep removing unused slots
            while (!exts.empty() && exts.back() == 0) {
                exts.pop_back();
            }
        }

        unsigned next_transcendental_idx() {
            cleanup(extension::TRANSCENDENTAL);
            return m_extensions[extension::TRANSCENDENTAL].size();
        }

        unsigned next_infinitesimal_idx() {
            cleanup(extension::INFINITESIMAL);
            return m_extensions[extension::INFINITESIMAL].size();
        }
        
        void set_cancel(bool f) {
            m_cancel = f;
        }
        
        void updt_params(params_ref const & p) {
            m_ini_precision = p.get_uint("initial_precision", 24);
            // TODO
        }

        /**
           \brief Reset the given polynomial.
           That is, after the call p is the 0 polynomial.
        */
        void reset_p(polynomial & p) {
            dec_ref(p.size(), p.c_ptr());
            p.finalize(allocator());
        }

        void del_rational(rational_value * v) {
            bqim().del(v->m_interval);
            qm().del(v->m_value);
            allocator().deallocate(sizeof(rational_value), v);
        }

        void del_rational_function(rational_function_value * v) {
            bqim().del(v->m_interval);
            reset_p(v->num());
            reset_p(v->den());
            dec_ref_ext(v->ext());
            allocator().deallocate(sizeof(rational_function_value), v);
        }

        void del_value(value * v) {
            if (v->is_rational())
                del_rational(static_cast<rational_value*>(v));
            else
                del_rational_function(static_cast<rational_function_value*>(v));
        }

        void del_algebraic(algebraic * a) {
            reset_p(a->m_p);
            bqim().del(a->m_interval);
            unsigned sz = a->m_signs.size();
            for (unsigned i = 0; i < sz; i++) {
                reset_p(a->m_signs[i].first);
            }
            allocator().deallocate(sizeof(algebraic), a);
        }

        void del_transcendental(transcendental * t) {
            allocator().deallocate(sizeof(transcendental), t);
        }
        
        void del_infinitesimal(infinitesimal * i) {
            allocator().deallocate(sizeof(infinitesimal), i);
        }

        void inc_ref_ext(extension * ext) {
            SASSERT(ext != 0);
            ext->m_ref_count++;
        }

        void dec_ref_ext(extension * ext) {
            SASSERT(m_extensions[ext->knd()][ext->idx()] == ext);
            SASSERT(ext->m_ref_count > 0);
            ext->m_ref_count--;
            if (ext->m_ref_count == 0) {
                m_extensions[ext->knd()][ext->idx()] = 0;
                switch (ext->knd()) {
                case extension::TRANSCENDENTAL: del_transcendental(static_cast<transcendental*>(ext)); break;
                case extension::INFINITESIMAL:  del_infinitesimal(static_cast<infinitesimal*>(ext)); break;
                case extension::ALGEBRAIC:      del_algebraic(static_cast<algebraic*>(ext)); break;
                }
            }
        }

        void inc_ref(value * v) {
            if (v)
                v->m_ref_count++;
        }

        void inc_ref(unsigned sz, value * const * p) {
            for (unsigned i = 0; i < sz; i++)
                inc_ref(p[i]);
        }

        void dec_ref(value * v) {
            if (v) {
                SASSERT(v->m_ref_count > 0);
                v->m_ref_count--;
                if (v->m_ref_count == 0)
                    del_value(v);
            }
        }

        void dec_ref(unsigned sz, value * const * p) {
            for (unsigned i = 0; i < sz; i++)
                dec_ref(p[i]);
        }

        void del(numeral & a) {
            dec_ref(a.m_value);
            a.m_value = 0;
        }

        /**
           \brief Return true if the given interval is smaller than 1/2^k
        */
        bool check_precision(mpbqi const & interval, unsigned k) {
            if (interval.lower_is_inf() || interval.upper_is_inf())
                return false;
            scoped_mpbq w(bqm());
            bqm().sub(interval.upper(), interval.lower(), w);
            return bqm().lt_1div2k(w, k);
        }

        /**
           \brief Return true if v is zero.
        */
        static bool is_zero(value * v) {
            return v == 0;
        }

        /**
           \brief Return true if v is represented using a nonzero arbitrary precision rational value.
        */
        static bool is_nz_rational(value * v) { 
            SASSERT(v != 0);
            return v->is_rational(); 
        }

        /**
           \brief Return true if v is represented as rational value one.
        */
        bool is_rational_one(value * v) const {
            return !is_zero(v) && is_nz_rational(v) && qm().is_one(to_mpq(v));
        }

        /**
           \brief Return true if v is the value one;
         */
        bool is_one(value * v) const {
            if (is_rational_one(v))
                return true;
            // TODO: check if v is equal to one.
            return false;
        }

        /**
           \brief Return true if v is a represented as a rational function of the set of field extensions.
        */
        static bool is_rational_function(value * v) {
            SASSERT(v != 0);
            return !(v->is_rational());
        }
        
        static rational_value * to_nz_rational(value * v) { 
            SASSERT(is_nz_rational(v)); 
            return static_cast<rational_value*>(v); 
        }
        
        static rational_function_value * to_rational_function(value * v) { 
            SASSERT(!is_nz_rational(v)); 
            return static_cast<rational_function_value*>(v); 
        }

        static bool is_zero(numeral const & a) {
            return is_zero(a.m_value);
        }

        static bool is_nz_rational(numeral const & a) {
            SASSERT(!is_zero(a));
            return is_nz_rational(a.m_value);
        }

        /**
           \brief Return true if v is not a shared value. That is, we can perform
           destructive updates.
        */
        static bool is_unique(value * v) {
            SASSERT(v);
            return v->m_ref_count <= 1;
        }

        static bool is_unique(numeral const & a) {
            return is_unique(a.m_value);
        }

        static bool is_unique_nz_rational(value * v) {
            return is_nz_rational(v) && is_unique(v);
        }

        static bool is_unique_nz_rational(numeral const & a) {
            return is_unique_nz_rational(a.m_value);
        }

        static rational_value * to_nz_rational(numeral const & a) {
            SASSERT(is_nz_rational(a));
            return to_nz_rational(a.m_value);
        }

        static bool is_rational_function(numeral const & a) {
            return is_rational_function(a.m_value);
        }

        static rational_function_value * to_rational_function(numeral const & a) {
            SASSERT(is_rational_function(a));
            return to_rational_function(a.m_value);
        }

        static mpq & to_mpq(value * v) {
            SASSERT(is_nz_rational(v));
            return to_nz_rational(v)->m_value;
        }

        static mpq & to_mpq(numeral const & a) {
            SASSERT(is_nz_rational(a));
            return to_nz_rational(a)->m_value;
        }

        static int compare_rank(value * a, value * b) {
            SASSERT(a); SASSERT(b);
            if (is_nz_rational(a))
                return is_nz_rational(b) ? 0 : -1;
            else if (is_nz_rational(b)) {
                SASSERT(is_rational_function(a));
                return 1;
            }
            else if (rank_eq(to_rational_function(a)->ext(), to_rational_function(b)->ext()))
                return 0;
            else 
                return rank_lt(to_rational_function(a)->ext(), to_rational_function(b)->ext()) ? -1 : 1;
        }

        static transcendental * to_transcendental(extension * ext) {
            SASSERT(ext->is_transcendental());
            return static_cast<transcendental*>(ext);
        }

        static infinitesimal * to_infinitesimal(extension * ext) {
            SASSERT(ext->is_infinitesimal());
            return static_cast<infinitesimal*>(ext);
        }

        static algebraic * to_algebraic(extension * ext) {
            SASSERT(ext->is_algebraic());
            return static_cast<algebraic*>(ext);
        }
        
        /**
           \brief Return True if the given extension is a Real value.
           The result is approximate for algebraic extensions.
             For algebraic extensions, we have
               - true result is always correct (i.e., the extension is really a real value)
               - false result is approximate (i.e., the extension may be a real value although it is a root of a polynomial that contains non-real coefficients)
                   Example: Assume eps is an infinitesimal, and pi is 3.14... . 
                   Assume also that ext is the unique root between (3, 4) of the following polynomial:
                          x^2 - (pi + eps)*x + pi*ext 
                   Thus, x is pi, but the system will return false, since its defining polynomial has infinitesimal
                   coefficients. In the future, to make everything precise, we should be able to factor the polynomial
                   above as 
                          (x - eps)*(x - pi)
                   and then detect that x is actually the root of (x - pi).
        */
        bool is_real(extension * ext) {
            switch (ext->knd()) {
            case extension::TRANSCENDENTAL: return true;
            case extension::INFINITESIMAL:  return false;
            case extension::ALGEBRAIC:      return to_algebraic(ext)->is_real();
            default:
                UNREACHABLE();
                return false;
            }
        }

        /**
           \brief Return true if v is definitely a real value.
        */
        bool is_real(value * v) {
            if (v->is_rational())
                return true;
            else 
                return to_rational_function(v)->is_real();
        }

        bool is_real(unsigned sz, value * const * p) {
            for (unsigned i = 0; i < sz; i++)
                if (!is_real(p[i]))
                    return false;
            return true;
        }

        /**
           \brief Set the polynomial p with the given coefficients as[0], ..., as[n-1]
        */
        void set_p(polynomial & p, unsigned n, value * const * as) {
            SASSERT(n > 0);
            SASSERT(!is_zero(as[n - 1]));
            reset_p(p);
            p.set(allocator(), n, as);
            inc_ref(n, as);
        }

        /**
           \brief Set the polynomial p as the constant polynomial 1.
        */
        void set_p_one(polynomial & p) {
            set_p(p, 1, &m_one);
        }

        /**
           \brief Set the lower bound of the given interval.
        */
        void set_lower_core(mpbqi & a, mpbq const & k, bool open, bool inf) {
            bqm().set(a.lower(), k);
            a.set_lower_is_open(open);
            a.set_lower_is_inf(inf);
        }

        /**
           \brief a.lower <- k
        */
        void set_lower(mpbqi & a, mpbq const & k, bool open = true) {
            set_lower_core(a, k, open, false);
        }

        /**
           \brief Set the upper bound of the given interval.
        */
        void set_upper_core(mpbqi & a, mpbq const & k, bool open, bool inf) {
            bqm().set(a.upper(), k);
            a.set_upper_is_open(open);
            a.set_upper_is_inf(inf);
        }

        /**
           \brief a.upper <- k
        */
        void set_upper(mpbqi & a, mpbq const & k, bool open = true) {
            set_upper_core(a, k, open, false);
        }

        /**
           \brief a <- b
        */
        void set_interval(mpbqi & a, mpbqi const & b) {
            set_lower_core(a, b.lower(), b.lower_is_open(), b.lower_is_inf());
            set_upper_core(a, b.upper(), b.upper_is_open(), b.upper_is_inf());
        }

        /**
           \brief Create a value using the given extension.
        */
        rational_function_value * mk_value(extension * ext) {
            rational_function_value * v = alloc(rational_function_value, ext);
            inc_ref_ext(ext);
            
            value * num[2] = { 0, one() };
            set_p(v->num(), 2, num); 
            set_p_one(v->den());
            
            set_interval(v->interval(), ext->interval());
            
            v->set_real(is_real(ext));

            return v;
        }

        /**
           \brief Create a new infinitesimal.
        */
        void mk_infinitesimal(symbol const & n, numeral & r) {
            unsigned idx = next_infinitesimal_idx();
            infinitesimal * eps = alloc(infinitesimal, idx, n);
            m_extensions[extension::INFINITESIMAL].push_back(eps);

            set_lower(eps->interval(), mpbq(0));
            set_upper(eps->interval(), mpbq(1, m_ini_precision));
            
            r.m_value = mk_value(eps);
            inc_ref(r.m_value);

            SASSERT(sign(r) > 0);
            SASSERT(!is_real(r));
        }

        void mk_infinitesimal(char const * n, numeral & r) {
            mk_infinitesimal(symbol(n), r);
        }

        void mk_infinitesimal(numeral & r) {
            mk_infinitesimal(symbol(next_infinitesimal_idx()), r);
        }

        void mk_transcendental(symbol const & n, mk_interval & proc, numeral & r) {
            // TODO
        }
        
        void mk_transcendental(char const * p, mk_interval & proc, numeral & r) {
            mk_transcendental(symbol(p), proc, r);
        }

        void mk_transcendental(mk_interval & proc, numeral & r) {
            mk_transcendental(symbol(next_transcendental_idx()), proc, r);
        }

        void isolate_roots(unsigned n, numeral const * as, numeral_vector & roots) {
            // TODO
        }

        void reset(numeral & a) {
            del(a);
            SASSERT(is_zero(a));
        }

        int sign(numeral const & a) {
            if (is_zero(a))
                return 0;
            else if (is_nz_rational(a)) {
                return qm().is_pos(to_mpq(a)) ? 1 : -1;
            }
            else {
                value * v = a.m_value;
                SASSERT(!bqim().contains_zero(v->interval()));
                return bqim().is_P(v->interval()) ? 1 : -1;
            }
        }
        
        bool is_int(numeral const & a) {
            if (is_zero(a))
                return true;
            else if (is_nz_rational(a)) 
                return qm().is_int(to_mpq(a));
            else {
                // TODO
                return false;
            }
        }

        bool is_real(value * v) const {
            if (is_zero(v) || is_nz_rational(v))
                return true;
            else
                return to_rational_function(v)->is_real();
        }
        
        bool is_real(numeral const & a) const {
            return is_real(a.m_value);
        }

        void mpq_to_mpbqi(mpq const & q, mpbqi & interval) {
            interval.set_lower_is_inf(false);
            interval.set_upper_is_inf(false);
            if (bqm().to_mpbq(q, interval.lower())) {
                bqm().set(interval.upper(), interval.lower());
                interval.set_lower_is_open(false);
                interval.set_upper_is_open(false);
            }
            else {
                bqm().set(interval.upper(), interval.lower());
                bqm().mul2(interval.upper());
                interval.set_lower_is_open(true);
                interval.set_upper_is_open(true);
                if (qm().is_neg(q)) {
                    ::swap(interval.lower(), interval.upper());
                }
                while (bqim().contains_zero(interval) || !check_precision(interval, m_ini_precision)) {
                    checkpoint();
                    bqm().refine_lower(q, interval.lower(), interval.upper());
                    bqm().refine_upper(q, interval.lower(), interval.upper());
                }
            }
        }

        void initialize_rational_value_interval(value * a) {
            // For rational values, we only compute the binary intervals if needed.
            SASSERT(is_nz_rational(a));
            mpq_to_mpbqi(to_mpq(a), a->m_interval);
        }

        mpbqi const & interval(value * a) const {
            SASSERT(a != 0);
            if (bqim().contains_zero(a->m_interval)) {
                SASSERT(is_nz_rational(a));
                const_cast<imp*>(this)->initialize_rational_value_interval(a);
            }
            return a->m_interval;
        }

        rational_value * mk_rational() {
            return new (allocator()) rational_value();
        }

        rational_value * mk_rational(mpq & v) {
            rational_value * r = mk_rational();
            ::swap(r->m_value, v);
            return r;
        }

        template<typename T>
        void update_mpq_value(value * a, T & v) {
            SASSERT(is_nz_rational(a));
            qm().set(to_mpq(a), v);
            bqim().reset(a->m_interval);
        }

        template<typename T>
        void update_mpq_value(numeral & a, T & v) {
            update_mpq_value(a.m_value, v);
        }

        void set(numeral & a, int n) {
            if (n == 0) {
                reset(a);
                return;
            }
            
            if (is_zero(a) || !is_unique_nz_rational(a)) {
                del(a);
                a.m_value = mk_rational();
                inc_ref(a.m_value);
            }
            SASSERT(is_unique_nz_rational(a));
            update_mpq_value(a, n);
        }

        void set(numeral & a, mpz const & n) {
            if (qm().is_zero(n)) {
                reset(a);
                return;
            }

            if (is_zero(a) || !is_unique_nz_rational(a)) {
                del(a);
                a.m_value = mk_rational();
                inc_ref(a.m_value);
            }
            SASSERT(is_unique_nz_rational(a));
            update_mpq_value(a, n);
        }
        
        void set(numeral & a, mpq const & n) {
            if (qm().is_zero(n)) {
                reset(a);
                return;
            }

            if (is_zero(a) || !is_unique_nz_rational(a)) {
                del(a);
                a.m_value = mk_rational();
                inc_ref(a.m_value);
            }
            SASSERT(is_unique_nz_rational(a));
            update_mpq_value(a, n);
        }
        
        void set(numeral & a, numeral const & n) {
            inc_ref(n.m_value);
            dec_ref(a.m_value);
            a.m_value = n.m_value;
        }

        void root(numeral const & a, unsigned k, numeral & b) {
            // TODO
        }
      
        void power(numeral const & a, unsigned k, numeral & b) {
            // TODO
        }

        /**
           \brief Remove 0s
        */
        void adjust_size(value_ref_buffer & r) {
            while (!r.empty() && r.back() == 0) {
                r.pop_back();
            }
        }

        /**
           \brief r <- p1 + p2
        */
        void add(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & r) {
            r.reset();
            unsigned min = std::min(sz1, sz2);
            for (unsigned i = 0; i < min; i++)
                r.push_back(add(p1[i], p2[i]));
            for (unsigned i = 0; i < sz1; i++)
                r.push_back(p1[i]);
            for (unsigned i = 0; i < sz2; i++)
                r.push_back(p2[i]);
            adjust_size(r);
        }

        /**
           \brief r <- p1 - p2
        */
        void sub(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & r) {
            r.reset();
            unsigned min = std::min(sz1, sz2);
            for (unsigned i = 0; i < min; i++)
                r.push_back(sub(p1[i], p2[i]));
            for (unsigned i = 0; i < sz1; i++)
                r.push_back(p1[i]);
            for (unsigned i = 0; i < sz2; i++)
                r.push_back(neg(p2[i]));
            adjust_size(r);
        }

        /**
           \brief r <- a * p
        */
        void mul(value * a, unsigned sz, value * const * p, value_ref_buffer & r) {
            r.reset();
            if (a == 0) 
                return;
            for (unsigned i = 0; i < sz; i++)
                r.push_back(mul(a, p[i]));
        }

        /**
           \brief r <- p1 * p2
        */
        void mul(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & r) {
            r.reset();
            unsigned sz = sz1*sz2;
            r.resize(sz);
            if (sz1 < sz2) {
                std::swap(sz1, sz2);
                std::swap(p1, p2);
            }
            value_ref tmp(*this);
            for (unsigned i = 0; i < sz1; i++) {
                checkpoint();
                if (p1[i] == 0)
                    continue;
                for (unsigned j = 0; j < sz2; j++) {
                    // r[i+j] <- r[i+j] + p1[i]*p2[j]
                    tmp = mul(p1[i], p2[j]);
                    r.set(i+j, add(r[i+j], tmp));
                }
            }
            adjust_size(r);
        }

        /**
           \brief p <- p/a
        */
        void div(value_ref_buffer & p, value * a) {
            SASSERT(!is_zero(a));
            if (is_rational_one(a))
                return;
            unsigned sz = p.size();
            for (unsigned i = 0; i < sz; i++)
                p.set(i, div(p[i], a));
        }

        /**
           \brief q <- quotient(p1, p2); r <- rem(p1, p2)
        */
        void div_rem(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, 
                     value_ref_buffer & q, value_ref_buffer & r) {
            SASSERT(sz2 > 0);
            if (sz2 == 1) {
                q.reset(); q.append(sz1, p1);
                div(q, *p2);
                r.reset();
            }
            else {
                q.reset();
                r.reset(); r.append(sz1, p1);
                if (sz1 > 1) {
                    if (sz1 >= sz2) {
                        q.resize(sz1 - sz2 + 1);
                    }
                    else {
                        SASSERT(q.empty());
                    }
                    value * b_n = p2[sz2-1];
                    SASSERT(!is_zero(b_n));
                    value_ref ratio(*this);
                    while (true) {
                        checkpoint();
                        sz1 = r.size();
                        if (sz1 < sz2) {
                            adjust_size(q);
                            break;
                        }
                        unsigned m_n = sz1 - sz2; // m-n            
                        ratio = div(r[sz1 - 1], b_n);
                        // q[m_n] <- q[m_n] + r[sz1 - 1]/b_n
                        q.set(m_n, add(q[m_n], ratio));
                        for (unsigned i = 0; i < sz2 - 1; i++) {
                            // r[i + m_n] <- r[i + m_n] - ratio * p2[i]
                            ratio = mul(ratio, p2[i]);
                            r.set(i + m_n, sub(r[i + m_n], ratio));
                        }
                        r.shrink(sz1 - 1);
                        adjust_size(r);
                    }
                }
            }
        }
        
        /**
           \brief q <- quotient(p1, p2)
        */
        void div(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & q) {
            value_ref_buffer r(*this);
            div_rem(sz1, p1, sz2, p2, q, r);
        }

        /**
           \brief r <- rem(p1, p2)
        */
        void rem(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & r) {
            r.reset();
            SASSERT(sz2 > 0);
            if (sz2 == 1)
                return;
            r.append(sz1, p1);
            if (sz1 <= 1)
                return; // r is p1
            value * b_n = p2[sz2 - 1];
            value_ref ratio(*this);
            SASSERT(b_n != 0);
            while (true) {
                checkpoint();
                sz1 = r.size();
                if (sz1 < sz2) {
                    return;
                }
                unsigned m_n = sz1 - sz2;
                ratio = div(b_n, r[sz1 - 1]);
                for (unsigned i = 0; i < sz2 - 1; i++) {
                    ratio = mul(ratio, p2[i]);
                    r.set(i + m_n, sub(r[i + m_n], ratio));
                }
                r.shrink(sz1 - 1);
                adjust_size(r);
            }
        }

        /**
           \brief r <- -r
        */
        void neg(value_ref_buffer & r) {
            unsigned sz = r.size();
            for (unsigned i = 0; i < sz; i++) 
                r.set(i, neg(r[i]));
        }

        /**
           \brief r <- srem(p1, p2)  
           Signed remainder
        */
        void srem(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & r) {
            rem(sz1, p1, sz2, p2, r);
            neg(r);
        }
        
        /**
           \brief Force the leading coefficient of p to be 1.
        */
        void mk_monic(value_ref_buffer & p) {
            unsigned sz = p.size();
            if (sz > 0) {
                SASSERT(p[sz-1] != 0);
                if (!is_one(p[sz-1])) {
                    for (unsigned i = 0; i < sz - 1; i++) {
                        p.set(i, div(p[i], p[sz-1]));
                    }
                }
                // I perform the following assignment even when is_one(p[sz-1]) returns true, 
                // Reason: the leading coefficient may be equal to one but may not be encoded using
                // the rational value 1.
                p.set(sz-1, one());
            }
        }

        /**
           \brief r <- gcd(p1, p2)
        */
        void gcd(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & r) {
            if (sz1 == 0) {
                r.append(sz2, p2);
                mk_monic(r);
            }
            else if (sz2 == 0) {
                r.append(sz1, p1);
                mk_monic(r);
            }
            else {
                value_ref_buffer A(*this);
                value_ref_buffer B(*this);
                value_ref_buffer & R = r;
                A.append(sz1, p1);
                B.append(sz2, p2);
                while (true) {
                    if (B.empty()) {
                        mk_monic(A);
                        r = A;
                        return;
                    }
                    rem(A.size(), A.c_ptr(), B.size(), B.c_ptr(), R);
                    A = B;
                    B = R;
                }
            }
        }

        /**
           \brief r <- dp/dx
        */
        void derivative(unsigned sz, value * const * p, value_ref_buffer & r) {
            r.reset();
            if (sz > 1) {
                for (unsigned i = 1; i < sz; i++) {
                    mpq i_mpq(i);
                    value_ref i_value(*this);
                    i_value = mk_rational(i_mpq);
                    r.push_back(mul(i_value, p[i]));
                }
                adjust_size(r);
            }
        }

        /**
           \brief r <- squarefree(p)
           Store in r the square free factors of p.
        */
        void square_free(unsigned sz, value * const * p, value_ref_buffer & r) {
            if (sz <= 1) {
                r.append(sz, p);
            }
            else {
                value_ref_buffer p_prime(*this);
                value_ref_buffer g(*this);
                derivative(sz, p, p_prime);
                gcd(sz, p, p_prime.size(), p_prime.c_ptr(), g);
                if (g.size() <= 1) {
                    r.append(sz, p);
                }
                else {
                    div(sz, p, g.size(), g.c_ptr(), r);
                }
            }
        }

        /**
           \brief Keep expanding the Sturm sequence starting at seq
        */
        void sturm_seq_core(scoped_polynomial_seq & seq) {
            value_ref_buffer r(*this);
            while (true) {
                unsigned sz = seq.size();
                srem(seq.size(sz-2), seq.coeffs(sz-2), seq.size(sz-1), seq.coeffs(sz-1), r);
                if (r.empty())
                    return;
                seq.push(r.size(), r.c_ptr());
            }
        }
        
        /**
           \brief Store in seq the Sturm sequence for (p1; p2)
        */
        void sturm_seq(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, scoped_polynomial_seq & seq) {
            seq.reset();
            seq.push(sz1, p1);
            seq.push(sz2, p2);
            sturm_seq_core(seq);
        }
        
        /**
           \brief Store in seq the Sturm sequence for (p; p')
        */
        void sturm_seq(unsigned sz, value * const * p, scoped_polynomial_seq & seq) {
            seq.reset();
            value_ref_buffer p_prime(*this);
            seq.push(sz, p);
            derivative(sz, p, p_prime);
            seq.push(p_prime.size(), p_prime.c_ptr());
            sturm_seq_core(seq);
        }

        /**
           \brief Store in seq the Sturm sequence for (p1; p1' * p2)
        */
        void sturm_tarski_seq(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, scoped_polynomial_seq & seq) {
            seq.reset();
            value_ref_buffer p1p2(*this);
            seq.push(sz1, p1);
            derivative(sz1, p1, p1p2);
            mul(p1p2.size(), p1p2.c_ptr(), sz2, p2, p1p2);
            seq.push(p1p2.size(), p1p2.c_ptr());
            sturm_seq_core(seq);
        }


        value * add(value * a, value * b) {
            if (a == 0)
                return b;
            else if (b == 0)
                return a;
            else if (is_nz_rational(a) && is_nz_rational(b)) {
                scoped_mpq r(qm());
                qm().add(to_mpq(a), to_mpq(b), r);
                if (qm().is_zero(r))
                    return 0;
                else 
                    return mk_rational(r);
            }
            else {
                // TODO
                return 0;
            }
        }
        
        value * sub(value * a, value * b) {
            if (a == 0)
                return neg(b);
            else if (b == 0)
                return a;
            else if (is_nz_rational(a) && is_nz_rational(b)) {
                scoped_mpq r(qm());
                qm().sub(to_mpq(a), to_mpq(b), r);
                if (qm().is_zero(r))
                    return 0;
                else 
                    return mk_rational(r);
            }
            else {
                // TODO
                return 0;
            }
        }

        value * neg(value * a) {
            if (a == 0)
                return 0;
            else if (is_nz_rational(a)) {
                scoped_mpq r(qm());
                qm().set(r, to_mpq(a));
                qm().neg(r);
                return mk_rational(r);
            }
            else {
                // TODO
                return 0;
            }
        }

        value * mul(value * a, value * b) {
            if (a == 0 || b == 0)
                return 0;
            else if (is_nz_rational(a) && is_nz_rational(b)) {
                scoped_mpq r(qm());
                qm().mul(to_mpq(a), to_mpq(b), r);
                return mk_rational(r);
            }
            else {
                // TODO
                return 0;
            }
        }

        value * div(value * a, value * b) {
            if (a == 0)
                return 0;
            if (b == 0)
                throw exception("division by zero");
            else if (is_nz_rational(a) && is_nz_rational(b)) {
                scoped_mpq r(qm());
                qm().div(to_mpq(a), to_mpq(b), r);
                return mk_rational(r);
            }
            else {
                // TODO
                return 0;
            }
        }

        void add(numeral const & a, numeral const & b, numeral & c) {
            // TODO
        }

        void sub(numeral const & a, numeral const & b, numeral & c) {
            // TODO
        }

        void mul(numeral const & a, numeral const & b, numeral & c) {
            // TODO
        }
        
        void neg(numeral & a) {
            // TODO
        }
        
        void inv(numeral & a) {
            if (a.m_value == 0) {
                throw exception("division by zero");
            }
            else if (is_unique(a)) {
                if (is_nz_rational(a)) {
                    qm().inv(to_mpq(a));
                }
                else {
                    rational_function_value * v = to_rational_function(a);
                    v->num().swap(v->den());
                    // TODO: Invert interval
                }
            }
            else { 
                if (is_nz_rational(a)) {
                    rational_value * v = mk_rational();
                    inc_ref(v);
                    qm().inv(to_mpq(a), to_mpq(v));
                    dec_ref(a.m_value);
                    a.m_value = v;
                }
                else {
                    // TODO
                }
            }
        }

        void div(numeral const & a, numeral const & b, numeral & c) {
            // TODO
        }

        int compare(numeral const & a, numeral const & b) {
            // TODO
            return 0;
        }

        void select(numeral const & prev, numeral const & next, numeral & result) {
            // TODO
        }

        struct collect_algebraic_refs {
            char_vector            m_visited; // Set of visited algebraic extensions.
            ptr_vector<algebraic>  m_found;   // vector/list of visited algebraic extensions.

            void mark(extension * ext) {
                if (ext->is_algebraic()) {
                    m_visited.reserve(ext->idx() + 1, false);
                    if (!m_visited[ext->idx()]) {
                        m_visited[ext->idx()] = true;
                        algebraic * a = to_algebraic(ext);
                        m_found.push_back(a);
                        mark(a->p());
                    }
                }
            }

            void mark(polynomial const & p) {
                for (unsigned i = 0; i < p.size(); i++) {
                    mark(p[i]);
                }
            }
            
            void mark(value * v) {
                if (v == 0 || is_nz_rational(v))
                    return;
                rational_function_value * rf = to_rational_function(v);
                mark(rf->ext());
                mark(rf->num());
                mark(rf->den());
            }
        };

        template<typename DisplayVar>
        void display_polynomial(std::ostream & out, polynomial const & p, DisplayVar const & display_var, bool compact) const {
            unsigned i = p.size();
            bool first = true;
            SASSERT(i > 0);
            while (i > 0) {
                --i;
                if (p[i] == 0)
                    continue;
                if (first)
                    first = false;
                else
                    out << " + ";
                if (i == 0)
                    display(out, p[i], compact);
                else {
                    if (!is_rational_one(p[i])) {
                        out << "(";
                        display(out, p[i], compact);
                        out << ")*";
                    }
                    display_var(out, compact);
                    if (i > 1)
                        out << "^" << i;
                }
            }
        }

        struct display_free_var_proc {
            void operator()(std::ostream & out, bool compact) const {
                out << "#";
            }
        };

        struct display_ext_proc {
            imp const &  m;
            extension *  m_ref;    
            display_ext_proc(imp const & _m, extension * r):m(_m), m_ref(r) {}
            void operator()(std::ostream & out, bool compact) const {
                m.display_ext(out, m_ref, compact);
            }
        };

        void display_polynomial_expr(std::ostream & out, polynomial const & p, extension * ext, bool compact) const {
            display_polynomial(out, p, display_ext_proc(*this, ext), compact);
        }

        static void display_poly_sign(std::ostream & out, int s) {
            if (s < 0)
                out << " < 0";
            else if (s == 0)
                out << " = 0";
            else
                out << " > 0";
        }

        void display_algebraic_def(std::ostream & out, algebraic * a, bool compact) const {
            out << "root(";
            display_polynomial(out, a->p(), display_free_var_proc(), compact);
            out << ", ";
            bqim().display(out, a->interval());
            out << ", {";
            signs const & s = a->s();
            for (unsigned i = 0; i < s.size(); i++) {
                if (i > 0)
                    out << ", ";
                display_polynomial(out, s[i].first, display_free_var_proc(), compact);
                display_poly_sign(out, s[i].second);
            }
            out << "})";
        }

        void display_ext(std::ostream & out, extension * r, bool compact) const {
            switch (r->knd()) {
            case extension::TRANSCENDENTAL: to_transcendental(r)->display(out); break;
            case extension::INFINITESIMAL:  to_infinitesimal(r)->display(out); break;
            case extension::ALGEBRAIC: 
                if (compact)
                    out << "r!" << r->idx();
                else
                    display_algebraic_def(out, to_algebraic(r), compact);
            }
        }

        /**
           \brief Return true if p is the constant polynomial where the coefficient is 
           the rational value 1.

           \remark This is NOT checking whether p is actually equal to 1.
           That is, it is just checking the representation.
        */
        bool is_rational_one(polynomial const & p) const {
            return p.size() == 1 && is_one(p[0]);
        }

        void display(std::ostream & out, value * v, bool compact) const {
            if (v == 0)
                out << "0";
            else if (is_nz_rational(v)) 
                qm().display(out, to_mpq(v));
            else {
                rational_function_value * rf = to_rational_function(v);
                if (is_rational_one(rf->den())) {
                    display_polynomial_expr(out, rf->num(), rf->ext(), compact);
                }
                else if (is_rational_one(rf->num())) {
                    out << "1/(";
                    display_polynomial_expr(out, rf->den(), rf->ext(), compact);
                    out << ")";
                }
                else {
                    out << "(";
                    display_polynomial_expr(out, rf->num(), rf->ext(), compact);
                    out << ")/(";
                    display_polynomial_expr(out, rf->den(), rf->ext(), compact);
                    out << ")";
                }
            }
        }

        void display_compact(std::ostream & out, numeral const & a) const {
            collect_algebraic_refs c;
            c.mark(a.m_value);
            if (c.m_found.empty()) {
                display(out, a.m_value, true);
            }
            else {
                std::sort(c.m_found.begin(), c.m_found.end(), rank_lt_proc());
                out << "[";
                display(out, a.m_value, true);
                for (unsigned i = 0; i < c.m_found.size(); i++) {
                    algebraic * ext = c.m_found[i];
                    out << ", r!" << ext->idx() << " = ";
                    display_algebraic_def(out, ext, true);
                }
                out << "]";
            }
        }
        
        void display(std::ostream & out, numeral const & a) const {
            display(out, a.m_value, false);
        }

        void display_non_rational_in_decimal(std::ostream & out, numeral const & a, unsigned precision) {
            SASSERT(!is_zero(a));
            SASSERT(!is_nz_rational(a));
            mpbqi const & i = interval(a.m_value);
            if (check_precision(i, precision*4)) {
                // hack
                if (bqm().is_int(i.lower())) 
                    bqm().display_decimal(out, i.upper(), precision);
                else
                    bqm().display_decimal(out, i.lower(), precision);
            }
            else {
                out << "?";
            }
        }
        
        void display_decimal(std::ostream & out, numeral const & a, unsigned precision) const {
            if (is_zero(a)) {
                out << "0";
            }
            else if (is_nz_rational(a)) {
                qm().display_decimal(out, to_mpq(a), precision);
            }
            else {
                const_cast<imp*>(this)->display_non_rational_in_decimal(out, a, precision);
            }
        }

        void display_interval(std::ostream & out, numeral const & a) const {
            if (is_zero(a))
                out << "[0, 0]";
            else
                bqim().display(out, interval(a.m_value));
        }
    };

    manager::manager(unsynch_mpq_manager & m, params_ref const & p, small_object_allocator * a) {
        m_imp = alloc(imp, m, p, a);
    }
        
    manager::~manager() {
        dealloc(m_imp);
    }

    void manager::get_param_descrs(param_descrs & r) {
        // TODO
    }

    void manager::set_cancel(bool f) {
        m_imp->set_cancel(f);
    }

    void manager::updt_params(params_ref const & p) {
        m_imp->updt_params(p);
    }

    unsynch_mpq_manager & manager::qm() const {
        return m_imp->m_qm;
    }

    void manager::del(numeral & a) {
        m_imp->del(a);
    }

    void manager::mk_infinitesimal(char const * n, numeral & r) {
        m_imp->mk_infinitesimal(n, r);
    }

    void manager::mk_infinitesimal(numeral & r) {
        m_imp->mk_infinitesimal(r);
    }
        
    void manager::mk_transcendental(char const * n, mk_interval & proc, numeral & r) {
        m_imp->mk_transcendental(n, proc, r);
    }

    void manager::mk_transcendental(mk_interval & proc, numeral & r) {
        m_imp->mk_transcendental(proc, r);
    }

    void manager::isolate_roots(unsigned n, numeral const * as, numeral_vector & roots) {
        m_imp->isolate_roots(n, as, roots);
    }

    void manager::reset(numeral & a) {
        m_imp->reset(a);
    }

    int manager::sign(numeral const & a) {
        return m_imp->sign(a);
    }
        
    bool manager::is_zero(numeral const & a) {
        return sign(a) == 0;
    }

    bool manager::is_pos(numeral const & a) {
        return sign(a) > 0;
    }

    bool manager::is_neg(numeral const & a) {
        return sign(a) < 0;
    }

    bool manager::is_int(numeral const & a) {
        return m_imp->is_int(a);
    }
        
    bool manager::is_real(numeral const & a) {
        return m_imp->is_real(a);
    }
        
    void manager::set(numeral & a, int n) {
        m_imp->set(a, n);
    }

    void manager::set(numeral & a, mpz const & n) {
        m_imp->set(a, n);
    }

    void manager::set(numeral & a, mpq const & n) {
        m_imp->set(a, n);
    }

    void manager::set(numeral & a, numeral const & n) {
        m_imp->set(a, n);
    }

    void manager::swap(numeral & a, numeral & b) {
        std::swap(a.m_value, b.m_value);
    }

    void manager::root(numeral const & a, unsigned k, numeral & b) {
        m_imp->root(a, k, b);
    }
      
    void manager::power(numeral const & a, unsigned k, numeral & b) {
        m_imp->power(a, k, b);
    }

    void manager::add(numeral const & a, numeral const & b, numeral & c) {
        m_imp->add(a, b, c);
    }

    void manager::add(numeral const & a, mpz const & b, numeral & c) {
        scoped_numeral _b(*this);
        set(_b, b);
        add(a, _b, c);
    }

    void manager::sub(numeral const & a, numeral const & b, numeral & c) {
        m_imp->sub(a, b, c);
    }

    void manager::mul(numeral const & a, numeral const & b, numeral & c) {
        m_imp->mul(a, b, c);
    }

    void manager::neg(numeral & a) {
        m_imp->neg(a);
    }

    void manager::inv(numeral & a) {
        m_imp->inv(a);
    }

    void manager::div(numeral const & a, numeral const & b, numeral & c) {
        m_imp->div(a, b, c);
    }

    int manager::compare(numeral const & a, numeral const & b) {
        return m_imp->compare(a, b);
    }

    bool manager::eq(numeral const & a, numeral const & b) {
        return compare(a, b) == 0;
    }

    bool manager::eq(numeral const & a, mpq const & b) {
        scoped_numeral _b(*this);
        set(_b, b);
        return eq(a, _b);
    }

    bool manager::eq(numeral const & a, mpz const & b) {
        scoped_numeral _b(*this);
        set(_b, b);
        return eq(a, _b);
    }

    bool manager::lt(numeral const & a, numeral const & b) {
        return compare(a, b) < 0;
    }

    bool manager::lt(numeral const & a, mpq const & b) {
        scoped_numeral _b(*this);
        set(_b, b);
        return lt(a, _b);
    }

    bool manager::lt(numeral const & a, mpz const & b) {
        scoped_numeral _b(*this);
        set(_b, b);
        return lt(a, _b);
    }

    bool manager::gt(numeral const & a, mpq const & b) {
        scoped_numeral _b(*this);
        set(_b, b);
        return gt(a, _b);
    }

    bool manager::gt(numeral const & a, mpz const & b) {
        scoped_numeral _b(*this);
        set(_b, b);
        return gt(a, _b);
    }

    void manager::select(numeral const & prev, numeral const & next, numeral & result) {
        m_imp->select(prev, next, result);
    }
        
    void manager::display(std::ostream & out, numeral const & a) const {
        m_imp->display(out, a);
    }

    void manager::display_decimal(std::ostream & out, numeral const & a, unsigned precision) const {
        m_imp->display_decimal(out, a, precision);
    }

    void manager::display_interval(std::ostream & out, numeral const & a) const {
        m_imp->display_interval(out, a);
    }

};
