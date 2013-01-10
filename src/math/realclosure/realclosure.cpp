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
#include"mpz_matrix.h"
#include"interval_def.h"
#include"obj_ref.h"
#include"ref_vector.h"
#include"ref_buffer.h"
#include"cooperate.h"

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
            // division is not precise
            static bool precise() { return false; }
            static bool field() { return true; }
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
        unsigned m_ref_count;  //!< Reference counter
        bool     m_rational;   //!< True if the value is represented as an abitrary precision rational value.
        mpbqi    m_interval;   //!< approximation as an interval with binary rational end-points
        // When performing an operation OP, we may have to make the width (upper - lower) of m_interval very small.
        // The precision (i.e., a small interval) needed for executing OP is usually unnecessary for subsequent operations,
        // This unnecessary precision will only slowdown the subsequent operations that do not need it.
        // To cope with this issue, we cache the value m_interval in m_old_interval whenever the width of m_interval is below
        // a give threshold. Then, after finishing OP, we restore the old_interval.
        mpbqi *  m_old_interval; 
        value(bool rat):m_ref_count(0), m_rational(rat), m_old_interval(0) {}
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

    // ---------------------------------
    //
    // Field Extensions
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
    
    /**
       \brief Sign condition object, it encodes one conjunct of a sign assignment.
       If has to keep following m_prev to obtain the whole sign condition
    */
    struct sign_condition {
        unsigned         m_q_idx:31; // Sign condition for the polynomial at position m_q_idx in the field m_qs of sign_det structure
        unsigned         m_mark:1;   // auxiliary mark used during deletion
        int              m_sign;     // Sign of the polynomial associated with m_q_idx
        sign_condition * m_prev;     // Antecedent
        sign_condition():m_q_idx(0), m_mark(false), m_sign(0), m_prev(0) {}
        sign_condition(unsigned qidx, int sign, sign_condition * prev):m_q_idx(qidx), m_mark(false), m_sign(sign), m_prev(prev) {}

        sign_condition * prev() const { return m_prev; }
        unsigned qidx() const { return m_q_idx; }
        int sign() const { return m_sign; }
    };

    struct sign_det {
        unsigned                m_ref_count;  // sign_det objects may be  shared between different roots of the same polynomial.
        mpz_matrix              M;            // Matrix used in the sign determination
        array<polynomial>       m_prs;        // Polynomials associated with the rows of M
        array<sign_condition *> m_sign_conditions; // Sign conditions associated with the columns of M
        array<polynomial>       m_qs;     // Polynomials used in the sign conditions.
        sign_det():m_ref_count(0) {}
        
        array<polynomial> const & qs() const { return m_qs; }
        sign_condition * sc(unsigned idx) const { return m_sign_conditions[idx]; }
    };

    struct algebraic : public extension {
        polynomial   m_p;
        sign_det *   m_sign_det; //!< != 0         if m_interval constains more than one root of m_p.
        unsigned     m_sdt_idx;   //!< != UINT_MAX  if m_sign_det != 0, in this case m_sdt_idx < m_sign_det->m_sign_conditions.size()
        bool         m_real;     //!< True if the polynomial p does not depend on infinitesimal extensions.

        algebraic(unsigned idx):extension(ALGEBRAIC, idx), m_sign_det(0), m_sdt_idx(0), m_real(false) {}

        polynomial const & p() const { return m_p; }
        bool is_real() const { return m_real; }
        sign_det * sdt() const { return m_sign_det; }
        unsigned sdt_idx() const { return m_sdt_idx; }
    };

    struct transcendental : public extension {
        symbol        m_name;
        unsigned      m_k;
        mk_interval & m_proc;
        
        transcendental(unsigned idx, symbol const & n, mk_interval & p):extension(TRANSCENDENTAL, idx), m_name(n), m_k(0), m_proc(p) {}

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

    // ---------------------------------
    //
    // Predefined transcendental mk_interval procs
    //
    // ---------------------------------
    
    struct mk_pi_interval : public mk_interval {
        virtual void operator()(unsigned k, mpqi_manager & im, mpqi_manager::interval & r) {
            im.pi(k, r);
        }
    };

    struct mk_e_interval : public mk_interval {
        virtual void operator()(unsigned k, mpqi_manager & im, mpqi_manager::interval & r) {
            im.e(k, r);
        }
    };

    // ---------------------------------
    //
    // Manager
    //
    // ---------------------------------

    struct manager::imp {
        typedef ref_vector<value, imp> value_ref_vector;
        typedef ref_buffer<value, imp, REALCLOSURE_INI_BUFFER_SIZE> value_ref_buffer;
        typedef obj_ref<value, imp>    value_ref;
        typedef _scoped_interval<mpqi_manager>  scoped_mpqi;
        typedef _scoped_interval<mpbqi_manager> scoped_mpbqi;
        typedef sbuffer<int, REALCLOSURE_INI_BUFFER_SIZE> int_buffer;
        typedef sbuffer<unsigned, REALCLOSURE_INI_BUFFER_SIZE> unsigned_buffer;
        
        small_object_allocator *       m_allocator;
        bool                           m_own_allocator;
        unsynch_mpq_manager &          m_qm;
        mpz_matrix_manager             m_mm;
        mpbq_config::numeral_manager   m_bqm;
        mpqi_manager                   m_qim;
        mpbqi_manager                  m_bqim;
        ptr_vector<extension>          m_extensions[3];
        value *                        m_one;
        mk_pi_interval                 m_mk_pi_interval;
        value *                        m_pi;
        mk_e_interval                  m_mk_e_interval;
        value *                        m_e;
        ptr_vector<value>              m_to_restore; //!< Set of values v s.t. v->m_old_interval != 0
        
        // Parameters
        unsigned                       m_ini_precision; //!< initial precision for transcendentals, infinitesimals, etc.
        unsigned                       m_max_precision; //!< Maximum precision for interval arithmetic techniques, it switches to complete methods after that
        unsigned                       m_inf_precision; //!< 2^m_inf_precision is used as the lower bound of oo and -2^m_inf_precision is used as the upper_bound of -oo
        scoped_mpbq                    m_plus_inf_approx; // lower bound for binary rational intervals used to approximate an infinite positive value
        scoped_mpbq                    m_minus_inf_approx; // upper bound for binary rational intervals used to approximate an infinite negative value

        volatile bool                  m_cancel;

        struct scoped_polynomial_seq {
            typedef ref_buffer<value, imp, REALCLOSURE_INI_SEQ_SIZE> value_seq;
            value_seq          m_seq_coeffs;
            sbuffer<unsigned>  m_begins;     // start position (in m_seq_coeffs) of each polynomial in the sequence
            sbuffer<unsigned>  m_szs;        // size of each polynomial in the sequence 
        public:
            scoped_polynomial_seq(imp & m):m_seq_coeffs(m) {}
            ~scoped_polynomial_seq() {
            }
            
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

            scoped_polynomial_seq & operator=(scoped_polynomial_seq & s) {
                if (this == &s)
                    return *this;
                reset();
                m_seq_coeffs.append(s.m_seq_coeffs);
                m_begins.append(s.m_begins);
                m_szs.append(s.m_szs);
                return *this;
            }
        };

        struct scoped_sign_conditions {
            imp &                                                   m_imp;
            ptr_buffer<sign_condition, REALCLOSURE_INI_BUFFER_SIZE> m_scs;

            scoped_sign_conditions(imp & m):m_imp(m) {}
            ~scoped_sign_conditions() {
                m_imp.del_sign_conditions(m_scs.size(), m_scs.c_ptr());
            }
            
            sign_condition * & operator[](unsigned idx) { return m_scs[idx]; }
            unsigned size() const { return m_scs.size(); }
            bool empty() const { return m_scs.empty(); }
            void push_back(sign_condition * sc) { m_scs.push_back(sc); }
            void release() {
                // release ownership
                m_scs.reset();
            }
            void copy_from(scoped_sign_conditions & scs) {
                SASSERT(this != &scs);
                release();
                m_scs.append(scs.m_scs.size(), scs.m_scs.c_ptr());
                scs.release();
            }
            sign_condition * const * c_ptr() { return m_scs.c_ptr(); }
        };
        
        imp(unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a):
            m_allocator(a == 0 ? alloc(small_object_allocator, "realclosure") : a),
            m_own_allocator(a == 0),
            m_qm(qm),
            m_mm(m_qm, *m_allocator),
            m_bqm(m_qm),
            m_qim(m_qm),
            m_bqim(m_bqm),
            m_plus_inf_approx(m_bqm),
            m_minus_inf_approx(m_bqm) {
            mpq one(1);
            m_one = mk_rational(one);
            inc_ref(m_one);
            m_pi = 0;
            m_e  = 0;
            m_cancel = false;
            
            updt_params(p);
        }

        ~imp() {
            restore_saved_intervals(); // to free memory
            dec_ref(m_one);
            dec_ref(m_pi);
            dec_ref(m_e);
            if (m_own_allocator)
                dealloc(m_allocator);
        }

        // Rational number manager
        unsynch_mpq_manager & qm() const { return m_qm; }

        // Binary rational number manager
        mpbq_config::numeral_manager & bqm() { return m_bqm; }

        // Rational interval manager
        mpqi_manager & qim() { return m_qim; }

        // Binary rational interval manager
        mpbqi_manager & bqim() { return m_bqim; }
        mpbqi_manager const & bqim() const { return m_bqim; }

        // Integer matrix manager
        mpz_matrix_manager & mm() { return m_mm; }

        small_object_allocator & allocator() { return *m_allocator; }

        void checkpoint() {
            if (m_cancel)
                throw exception("canceled");
            cooperate("rcf");
        }

        value * one() const {
            return m_one;
        }

        /**
           \brief Return the magnitude of the given interval.
           The magnitude is an approximation of the size of the interval.
        */
        int magnitude(mpbq const & l, mpbq const & u) {
            SASSERT(bqm().ge(u, l));
            scoped_mpbq w(bqm());
            bqm().sub(u, l, w);
            if (bqm().is_zero(w))
                return INT_MIN;
            SASSERT(bqm().is_pos(w));
            return bqm().magnitude_ub(w);
        }
        
        /**
           \brief Return the magnitude of the given interval.
           The magnitude is an approximation of the size of the interval.
        */
        int magnitude(mpbqi const & i) {
            if (i.lower_is_inf() || i.upper_is_inf())
                return INT_MAX;
            else
                return magnitude(i.lower(), i.upper());
        }

        /**
           \brief Return the magnitude of the given interval.
           The magnitude is an approximation of the size of the interval.
        */
        int magnitude(mpq const & l, mpq const & u) {
            SASSERT(qm().ge(u, l));
            scoped_mpq w(qm());
            qm().sub(u, l, w);
            if (qm().is_zero(w))
                return INT_MIN;
            SASSERT(qm().is_pos(w));
            return static_cast<int>(qm().log2(w.get().numerator())) + 1 - static_cast<int>(qm().log2(w.get().denominator()));
        }

        int magnitude(scoped_mpqi const & i) {
            SASSERT(!i->m_lower_inf && !i->m_upper_inf);
            return magnitude(i->m_lower, i->m_upper);
        }
        
        /**
           \brief Return true if the magnitude of the given interval is less than the parameter m_max_precision.
        */
        bool too_small(mpbqi const & i) {
            return magnitude(i) < -static_cast<int>(m_max_precision);
        }

#define SMALL_UNSIGNED 1 << 16
        static unsigned inc_precision(unsigned prec, unsigned inc) {
            if (prec < SMALL_UNSIGNED)
                return prec + inc;
            else
                return prec;
        }

        struct scoped_set_div_precision {
            mpbq_config::numeral_manager & m_bqm;
            unsigned                       m_old_precision;
            scoped_set_div_precision(mpbq_config::numeral_manager & bqm, unsigned prec):m_bqm(bqm) {
                m_old_precision = m_bqm.m_div_precision;
                m_bqm.m_div_precision = prec;
            }
            ~scoped_set_div_precision() {
                m_bqm.m_div_precision = m_old_precision;
            }
        };

        /**
           \brief c <- a/b with precision prec.
        */
        void div(mpbqi const & a, mpbqi const & b, unsigned prec, mpbqi & c) {
            SASSERT(!contains_zero(a));
            SASSERT(!contains_zero(b));
            scoped_set_div_precision set(bqm(), prec);
            bqim().div(a, b, c);
            SASSERT(!contains_zero(c));
        }

        /**
           \brief Save the current interval (i.e., approximation) of the given value.
        */
        void save_interval(value * v) {
            if (v->m_old_interval != 0)
                return; // interval was already saved.
            m_to_restore.push_back(v);
            inc_ref(v);
            v->m_old_interval = new (allocator()) mpbqi();
            set_interval(*(v->m_old_interval), v->m_interval);
        }

        /**
           \brief Save the current interval (i.e., approximation) of the given value IF it is too small (i.e., too_small(v) == True).
        */
        void save_interval_if_too_small(value * v) {
            if (too_small(v->m_interval))
                save_interval(v);
        }

        /**
           \brief Restore the saved intervals (approximations) of RCF values.
        */
        void restore_saved_intervals() {
            unsigned sz = m_to_restore.size();
            for (unsigned i = 0; i < sz; i++) {
                value * v = m_to_restore[i];
                set_interval(v->m_interval, *(v->m_old_interval));
                bqim().del(*(v->m_old_interval));
                allocator().deallocate(sizeof(mpbqi), v->m_old_interval);
                v->m_old_interval = 0;
                dec_ref(v);
            }
            m_to_restore.reset();
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

        unsigned next_algebraic_idx() {
            cleanup(extension::ALGEBRAIC);
            return m_extensions[extension::ALGEBRAIC].size();
        }
        
        void set_cancel(bool f) {
            m_cancel = f;
        }
        
        void updt_params(params_ref const & p) {
            m_ini_precision  = p.get_uint("initial_precision", 24);
            m_inf_precision  = p.get_uint("inf_precision", 24);
            m_max_precision  = p.get_uint("max_precision", 64); // == 1/2^64  for interval arithmetic methods, it switches to complete methods after that.
            bqm().power(mpbq(2), m_inf_precision, m_plus_inf_approx);
            bqm().set(m_minus_inf_approx, m_plus_inf_approx);
            bqm().neg(m_minus_inf_approx);
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

        void finalize(array<polynomial> & ps) {
            for (unsigned i = 0; i < ps.size(); i++)
                reset_p(ps[i]);
            ps.finalize(allocator());
        }

        void del_sign_condition(sign_condition * sc) {
            allocator().deallocate(sizeof(sign_condition), sc);
        }

        void del_sign_conditions(unsigned sz, sign_condition * const * to_delete) {
            ptr_buffer<sign_condition> all_to_delete;
            for (unsigned i = 0; i < sz; i++) {
                sign_condition * sc = to_delete[i];
                while (sc && sc->m_mark == false) {
                    sc->m_mark = true;
                    all_to_delete.push_back(sc);
                    sc = sc->m_prev;
                }
            }
            for (unsigned i = 0; i < all_to_delete.size(); i++) {
                del_sign_condition(all_to_delete[i]);
            }
        }

        void del_sign_det(sign_det * sd) {
            mm().del(sd->M);
            del_sign_conditions(sd->m_sign_conditions.size(), sd->m_sign_conditions.c_ptr());
            sd->m_sign_conditions.finalize(allocator());
            finalize(sd->m_prs);
            finalize(sd->m_qs);
            allocator().deallocate(sizeof(sign_det), sd);
        }

        void inc_ref_sign_det(sign_det * sd) {
            if (sd != 0)
                sd->m_ref_count++;
        }

        void dec_ref_sign_det(sign_det * sd) {
            if (sd != 0) {
                sd->m_ref_count--;
                if (sd->m_ref_count == 0) {
                    del_sign_det(sd);
                }
            }
        }

        void del_algebraic(algebraic * a) {
            reset_p(a->m_p);
            bqim().del(a->m_interval);
            dec_ref_sign_det(a->m_sign_det);
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

        void del(numeral_vector & v) {
            for (unsigned i = 0; i < v.size(); i++)
                del(v[i]);
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
           \brief Return true if v is represented as rational value minus one.
        */
        bool is_rational_minus_one(value * v) const {
            return !is_zero(v) && is_nz_rational(v) && qm().is_minus_one(to_mpq(v));
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
           \brief Return true if p is the constant polynomial where the coefficient is 
           the rational value 1.

           \remark This is NOT checking whether p is actually equal to 1.
           That is, it is just checking the representation.
        */
        bool is_rational_one(polynomial const & p) const {
            return p.size() == 1 && is_rational_one(p[0]);
        }
        bool is_rational_one(value_ref_buffer const & p) const {
            return p.size() == 1 && is_rational_one(p[0]);
        }

        template<typename T>
        bool is_one(polynomial const & p) const {
            return p.size() == 1 && is_one(p[0]);
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
            if (is_zero(v) || is_nz_rational(v))
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
           \brief Return true if a is an open interval.
        */
        static bool is_open_interval(mpbqi const & a) {
            return a.lower_is_inf() && a.upper_is_inf();
        }

        /**
           \brief Return true if the interval contains zero.
        */
        bool contains_zero(mpbqi const & a) const {
            return bqim().contains_zero(a);
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
           \brief a.lower <- -oo
        */
        void set_lower_inf(mpbqi & a) {
            bqm().reset(a.lower());
            a.set_lower_is_open(true);
            a.set_lower_is_inf(true);
        }

        /**
           \brief a.lower <- 0
        */
        void set_lower_zero(mpbqi & a) {
            bqm().reset(a.lower());
            a.set_lower_is_open(true);
            a.set_lower_is_inf(false);
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
           \brief a.upper <- oo
        */
        void set_upper_inf(mpbqi & a) {
            bqm().reset(a.upper());
            a.set_upper_is_open(true);
            a.set_upper_is_inf(true);
        }

        /**
           \brief a.upper <- 0
        */
        void set_upper_zero(mpbqi & a) {
            bqm().reset(a.upper());
            a.set_upper_is_open(true);
            a.set_upper_is_inf(false);
        }

        /**
           \brief a <- b
        */
        void set_interval(mpbqi & a, mpbqi const & b) {
            set_lower_core(a, b.lower(), b.lower_is_open(), b.lower_is_inf());
            set_upper_core(a, b.upper(), b.upper_is_open(), b.upper_is_inf());
        }

        /**
           \brief a <- [b, b]
        */
        void set_interval(mpbqi & a, mpbq const & b) {
            set_lower_core(a, b, false, false);
            set_upper_core(a, b, false, false);
        }

        sign_condition * mk_sign_condition(unsigned qidx, int sign, sign_condition * prev_sc) {
            return new (allocator()) sign_condition(qidx, sign, prev_sc);
        }

        /**
           \brief Make a rational_function_value using the given extension, numerator and denominator.
           This method does not set the interval. It remains (-oo, oo)
        */
        rational_function_value * mk_rational_function_value_core(extension * ext, unsigned num_sz, value * const * num, unsigned den_sz, value * const * den) {
            rational_function_value * r = alloc(rational_function_value, ext);
            inc_ref_ext(ext);
            set_p(r->num(), num_sz, num);
            set_p(r->den(), den_sz, den);
            r->set_real(is_real(ext) && is_real(num_sz, num) && is_real(den_sz, den));
            return r;
        }         

        /**
           \brief Create a value using the given extension.
        */
        rational_function_value * mk_rational_function_value(extension * ext) {
            value * num[2] = { 0, one() };
            value * den[1] = { one() };
            rational_function_value * v = mk_rational_function_value_core(ext, 2, num, 1, den);
            set_interval(v->interval(), ext->interval());
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
            
            set(r, mk_rational_function_value(eps));

            SASSERT(sign(r) > 0);
            SASSERT(!is_real(r));
        }

        void mk_infinitesimal(char const * n, numeral & r) {
            mk_infinitesimal(symbol(n), r);
        }

        void mk_infinitesimal(numeral & r) {
            mk_infinitesimal(symbol(next_infinitesimal_idx()), r);
        }

        void refine_transcendental_interval(transcendental * t) {
            scoped_mpqi i(qim());
            t->m_k++;
            t->m_proc(t->m_k, qim(), i);
            int m = magnitude(i);
            TRACE("rcf_transcendental", 
                  tout << "refine_transcendental_interval rational: " << m << "\nrational interval: "; 
                  qim().display(tout, i); tout << std::endl;);
            unsigned k;
            if (m >= 0)
                k = m_ini_precision;
            else
                k = inc_precision(-m, 8);
            scoped_mpbq l(bqm());
            mpq_to_mpbqi(i->m_lower, t->interval(), k);
            // save lower
            bqm().set(l, t->interval().lower()); 
            mpq_to_mpbqi(i->m_upper, t->interval(), k);
            bqm().set(t->interval().lower(), l);
        }

        void refine_transcendental_interval(transcendental * t, unsigned prec) {
            while (!check_precision(t->interval(), prec)) {
                TRACE("rcf_transcendental", tout << "refine_transcendental_interval: " << magnitude(t->interval()) << std::endl;);
                checkpoint();
                refine_transcendental_interval(t);
            }
        }

        void mk_transcendental(symbol const & n, mk_interval & proc, numeral & r) {
            unsigned idx = next_transcendental_idx();
            transcendental * t = alloc(transcendental, idx, n, proc);
            m_extensions[extension::TRANSCENDENTAL].push_back(t);
            
            while (contains_zero(t->interval())) {
                checkpoint();
                refine_transcendental_interval(t);
            }
            set(r, mk_rational_function_value(t));

            SASSERT(is_real(r));
        }
        
        void mk_transcendental(char const * p, mk_interval & proc, numeral & r) {
            mk_transcendental(symbol(p), proc, r);
        }

        void mk_transcendental(mk_interval & proc, numeral & r) {
            mk_transcendental(symbol(next_transcendental_idx()), proc, r);
        }

        void mk_pi(numeral & r) {
            if (m_pi) {
                set(r, m_pi);
            }
            else {
                mk_transcendental(symbol("pi"), m_mk_pi_interval, r);
                m_pi = r.m_value;
                inc_ref(m_pi);
            }
        }

        void mk_e(numeral & r) {
            if (m_e) {
                set(r, m_e);
            }
            else {
                mk_transcendental(symbol("e"), m_mk_e_interval, r);
                m_e = r.m_value;
                inc_ref(m_e);
            }
        }
       
        /**
           \brief r <- magnitude of the lower bound of |i|.
           That is, 2^r <= |i|.lower()
           Another way to view it is:
              2^r is smaller than the absolute value of any element in the interval i.

           Return true if succeeded, and false if i contains elements that are infinitely close to 0.
              
           \pre !contains_zero(i)
        */
        bool abs_lower_magnitude(mpbqi const & i, int & r) {
            SASSERT(!contains_zero(i));
            if (bqim().is_P(i)) {
                if (bqm().is_zero(i.lower()))
                    return false;
                r = bqm().magnitude_lb(i.lower());
                return true;
            }
            else {
                SASSERT(bqim().is_N(i));
                if (bqm().is_zero(i.upper()))
                    return false;
                scoped_mpbq tmp(bqm());
                tmp = i.upper();
                bqm().neg(tmp);
                r = bqm().magnitude_lb(tmp);
                return true;
            }
        }

        /**
           \brief r <- magnitude of the upper bound of |i|.
           That is, |i|.upper <= 2^r
           Another way to view it is:
              2^r is bigger than the absolute value of any element in the interval i.

           Return true if succeeded, and false if i is unbounded.
              
           \pre !contains_zero(i)
        */
        bool abs_upper_magnitude(mpbqi const & i, int & r) {
            SASSERT(!contains_zero(i));
            if (bqim().is_P(i)) {
                if (i.upper_is_inf())
                    return false;
                r = bqm().magnitude_ub(i.upper());
                return true;
            }
            else {
                SASSERT(bqim().is_N(i));
                if (i.lower_is_inf())
                    return false;
                scoped_mpbq tmp(bqm());
                tmp = i.lower();
                bqm().neg(tmp);
                r = bqm().magnitude_ub(tmp);
                return true;
            }
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
           
           This procedure returns a N s.t.  2*B <= 2^N
           
           The computation is performed using the intervals associated with the coefficients of 
           the polynomial.

           The procedure may fail if the interval for a_n is of the form  (l, 0) or (0, u).
           Similarly, the procedure will fail if one of the a_{n-k} has an interval of the form (l, oo) or (-oo, u).
           Both cases can only happen if the values of the coefficients depend on infinitesimal values.
        */
        bool pos_root_upper_bound(unsigned n, value * const * p, int & N) {
            SASSERT(n > 1);
            SASSERT(!is_zero(p[n-1]));
            int lc_sign = sign(p[n-1]);
            SASSERT(lc_sign != 0);
            int lc_mag;
            if (!abs_lower_magnitude(interval(p[n-1]), lc_mag))
                return false;
            N = -static_cast<int>(m_ini_precision);
            for (unsigned k = 2; k <= n; k++) {
                value * a = p[n - k];
                if (!is_zero(a) && sign(a) != lc_sign) {
                    int a_mag;
                    if (!abs_upper_magnitude(interval(a), a_mag))
                        return false;
                    int C = (a_mag - lc_mag)/static_cast<int>(k) + 1 /* compensate imprecision on division */ + 1 /* Knuth's bound is 2 x Max {... } */;
                    if (C > N)
                        N = C;
                }
            }
            return true;
        }

        
        /**
           \brief Auxiliary method for creating the intervals of the coefficients of the polynomials p(-x)
           without actually creating p(-x).
           
           'a' is the interval of the i-th coefficient of a polynomial
                a_n * x^n + ... + a_0
        */
        void neg_root_adjust(mpbqi const & a, unsigned i, mpbqi & r) {
            if (i % 2 == 0)
                bqim().neg(a, r);
            else
                bqim().set(r, a);
        }

        /**
           \brief Find negative root lower bound using Knuth's approach.
           
           This is similar to pos_root_upper_bound. In principle, we can use 
           the same algorithm. We just have to adjust the coefficients by using
           the transformation p(-x).
        */
        bool neg_root_lower_bound(unsigned n, value * const * as, int & N) {
            SASSERT(n > 1);
            SASSERT(!is_zero(as[n-1]));
            scoped_mpbqi aux(bqim());
            neg_root_adjust(interval(as[n-1]), n-1, aux);
            int lc_sign = bqim().is_P(aux) ? 1 : -1;
            int lc_mag;
            if (!abs_lower_magnitude(aux, lc_mag))
                return false;
            N = -static_cast<int>(m_ini_precision);
            for (unsigned k = 2; k <= n; k++) {
                value * a = as[n - k];
                if (!is_zero(a)) {
                    neg_root_adjust(interval(as[n-k]), n-k, aux);
                    int a_sign = bqim().is_P(aux) ? 1 : -1;
                    if (a_sign != lc_sign) {
                        int a_mag;
                        if (!abs_upper_magnitude(aux, a_mag))
                            return false;
                        int C = (a_mag - lc_mag)/static_cast<int>(k) + 1 /* compensate imprecision on division */ + 1 /* Knuth's bound is 2 x Max {... } */;
                        if (C > N)
                            N = C;
                    }
                }
            }
            return true;
        }

        /**
           \brief q <- x^{n-1}*p(1/x)

           Given p(x) a_{n-1} * x^{n-1} + ... + a_0, this method stores
           a_0 * x^{n-1} + ... + a_{n-1} into q.
        */
        void reverse(unsigned n, value * const * p, value_ref_buffer & q) {
            unsigned i = n;
            while (i > 0) {
                --i;
                q.push_back(p[i]);
            }
        }

        /**
           \brief To compute the lower bound for positive roots we computer the upper bound for the polynomial q(x) = x^{n-1}*p(1/x).
           Assume U is an upper bound for roots of q(x), i.e., (r > 0 and q(r) = 0) implies r < U.
           Note that if r is a root for q(x), then 1/r is a root for p(x) and 1/U is a lower bound for positive roots of p(x).
           The polynomial q(x) is just p(x) "reversed".
        */
        bool pos_root_lower_bound(unsigned n, value * const * p, int & N) {
            value_ref_buffer q(*this);
            reverse(n, p, q);
            if (pos_root_upper_bound(n, q.c_ptr(), N)) {
                N = -N;
                return true;
            }
            else {
                return false;
            }
        }

        /**
           \brief See comment on pos_root_lower_bound.
        */
        bool neg_root_upper_bound(unsigned n, value * const * p, int & N) {
            value_ref_buffer q(*this);
            reverse(n, p, q);
            if (neg_root_lower_bound(n, q.c_ptr(), N)) {
                N = -N;
                return true;
            }
            else {
                return false;
            }
        }

        /**
           \brief Store in ds all (non-constant) derivatives of p. 
           
           \post d.size() == n-2
        */
        void mk_derivatives(unsigned n, value * const * p, scoped_polynomial_seq & ds) {
            SASSERT(n >= 3); // p is at least quadratic
            SASSERT(!is_zero(p[0])); 
            SASSERT(!is_zero(p[n-1]));
            value_ref_buffer p_prime(*this);
            derivative(n, p, p_prime);
            ds.push(p_prime.size(), p_prime.c_ptr());
            SASSERT(n >= 3);
            for (unsigned i = 0; i < n - 2; i++) {
                SASSERT(ds.size() > 0);
                unsigned prev = ds.size() - 1;
                n = ds.size(prev);
                p = ds.coeffs(prev);
                derivative(n, p, p_prime);
                ds.push(p_prime.size(), p_prime.c_ptr());
            }
        }
        
        /**
           \brief Given polynomials p and q, and an interval, compute the number of 
           roots of p in the interval such that:
              - q is zero
              - q is positive
              - q is negative

           \pre num_roots is the number of roots of p in the given interval.
           
           \remark num_roots == q_eq_0 + q_gt_0 + q_lt_0
        */
        void count_signs_at_zeros(// Input values
                                  unsigned p_sz, value * const * p,  // polynomial p
                                  unsigned q_sz, value * const * q,  // polynomial q
                                  mpbqi const & interval,
                                  int num_roots,                     // number of roots of p in the given interval    
                                  // Output values
                                  int & q_eq_0, int & q_gt_0, int & q_lt_0,
                                  value_ref_buffer & q2) {
            TRACE("rcf_count_signs", 
                  tout << "p: "; display_poly(tout, p_sz, p); tout << "\n";
                  tout << "q: "; display_poly(tout, q_sz, q); tout << "\n";);
            SASSERT(num_roots > 0);
            int r1 = TaQ(p_sz, p, q_sz, q, interval);
            // r1 == q_gt_0 - q_lt_0
            SASSERT(-num_roots <= r1 && r1 <= num_roots);
            if (r1 == num_roots) {
                // q is positive in all roots of p
                q_eq_0 = 0;
                q_gt_0 = num_roots;
                q_lt_0 = 0;
            }
            else if (r1 == -num_roots) {
                // q is negative in all roots of p
                q_eq_0 = 0;
                q_gt_0 = 0;
                q_lt_0 = num_roots;
            }
            else if (r1 == num_roots - 1) {
                // The following assignment is the only possibility
                q_eq_0 = 1;
                q_gt_0 = num_roots - 1;
                q_lt_0 = 0;
            }
            else if (r1 == -(num_roots - 1)) {
                // The following assignment is the only possibility
                q_eq_0 = 1;
                q_gt_0 = 0;
                q_lt_0 = num_roots - 1;
            }
            else {
                // Expensive case
                // q2 <- q^2
                mul(q_sz, q, q_sz, q, q2);
                int r2 = TaQ(p_sz, p, q2.size(), q2.c_ptr(), interval);
                SASSERT(0 <= r2 && r2 <= num_roots);
                // r2 == q_gt_0 + q_lt_0
                SASSERT((r2 + r1) % 2 == 0);
                SASSERT((r2 - r1) % 2 == 0);
                q_eq_0 = num_roots - r2;
                q_gt_0 = (r2 + r1)/2;
                q_lt_0 = (r2 - r1)/2;
            }
            SASSERT(q_eq_0 + q_gt_0 + q_lt_0 == num_roots);
        }

        /**
           \brief Expand the set of Tarski Queries used in the sign determination algorithm.

           taqrs contains the results of TaQ(p, prs[i]; interval)
           We have that taqrs.size() == prs.size()
           
           We produce a new_taqrs and new_prs
           For each pr in new_prs we have
                pr      in new_prs,  TaQ(p, pr; interval) in new_taqrs
                pr*q    in new_prs,  TaQ(p, pr*q; interval) in new_taqrs
                if q2_sz != 0, we also have
                pr*q^2  in new_prs,  TaQ(p, pr*q^2; interval) in new_taqrs
           
        */
        void expand_taqrs(// Input values
                          int_buffer const &              taqrs, 
                          scoped_polynomial_seq const &   prs,
                          unsigned p_sz, value * const *  p,
                          unsigned q_sz, value * const *  q, 
                          bool use_q2, unsigned q2_sz, value * const * q2,
                          mpbqi const &                   interval,
                          // Output values
                          int_buffer &                    new_taqrs,
                          scoped_polynomial_seq &         new_prs
                          ) {
            SASSERT(taqrs.size() == prs.size());
            new_taqrs.reset(); new_prs.reset();
            for (unsigned i = 0; i < taqrs.size(); i++) {
                // Add prs * 1
                new_taqrs.push_back(taqrs[i]);
                new_prs.push(prs.size(i), prs.coeffs(i));
                // Add prs * q
                value_ref_buffer prq(*this);
                mul(prs.size(i), prs.coeffs(i), q_sz, q, prq);
                new_taqrs.push_back(TaQ(p_sz, p, prq.size(), prq.c_ptr(), interval));
                new_prs.push(prq.size(), prq.c_ptr());
                // If use_q2,
                // Add prs * q^2
                if (use_q2) {
                    value_ref_buffer prq2(*this);
                    mul(prs.size(i), prs.coeffs(i), q2_sz, q2, prq2);
                    new_taqrs.push_back(TaQ(p_sz, p, prq2.size(), prq2.c_ptr(), interval));
                    new_prs.push(prq2.size(), prq2.c_ptr());
                }
            }
            SASSERT(new_prs.size() == new_taqrs.size());
            SASSERT(use_q2  || new_prs.size() == 2*prs.size());
            SASSERT(!use_q2 || new_prs.size() == 3*prs.size());
        }

        /**
           \brief In the sign determination algorithm main loop, we keep processing polynomials q,
           and checking whether they discriminate the roots of the target polynomial.
           
           The vectors sc_cardinalities contains the cardinalites of the new realizable sign conditions.
           That is, we started we a sequence of sign conditions 
                     sc_1, ..., sc_n, 
           If q2_used is true, then we expanded this sequence as
                     sc1_1 and q == 0, sc_1 and q > 0, sc_1 and q < 0, ..., sc_n and q == 0, sc_n and q > 0, sc_n and q < 0
           If q2_used is false, then we considered only two possible signs of q.

           Thus, q is useful (i.e., it is a discriminator for the roots of p) IF 
                If !q2_used,   then There is an i s.t. sc_cardinalities[2*i] > 0 && sc_cardinalities[2*i] > 0
                If q2_used,    then There is an i s.t. AtLeatTwo(sc_cardinalities[3*i] > 0, sc_cardinalities[3*i+1] > 0, sc_cardinalities[3*i+2] > 0)
        */
        bool keep_new_sc_assignment(unsigned sz, int const * sc_cardinalities, bool q2_used) {
            SASSERT(q2_used  || sz % 2 == 0);
            SASSERT(!q2_used || sz % 3 == 0);
            if (q2_used) {
                for (unsigned i = 0; i < sz; i += 3) {
                    unsigned c = 0;
                    if (sc_cardinalities[i] > 0)   c++;
                    if (sc_cardinalities[i+1] > 0) c++;
                    if (sc_cardinalities[i+2] > 0) c++;
                    if (c >= 2)
                        return true;
                }
            }
            else {
                for (unsigned i = 0; i < sz; i += 2) {
                    if (sc_cardinalities[i] > 0 && sc_cardinalities[i+1] > 0)
                        return true;
                }
            }
            return false;
        }

        /**
           \brief Store the polynomials in prs into the array of polynomials ps.
        */
        void set_array_p(array<polynomial> & ps, scoped_polynomial_seq const & prs) {
            unsigned sz = prs.size();
            ps.set(allocator(), sz, polynomial());
            for (unsigned i = 0; i < sz; i++) {
                unsigned pi_sz     = prs.size(i);
                value * const * pi = prs.coeffs(i);
                set_p(ps[i], pi_sz, pi);
            }
        }

        /**
           \brief Create a "sign determination" data-structure for an algebraic extension.
           
           The new object will assume the ownership of the elements stored in M and scs. 
           M and scs will be empty after this operation.
        */
        sign_det * mk_sign_det(mpz_matrix & M, scoped_polynomial_seq const & prs, scoped_polynomial_seq const & qs, scoped_sign_conditions & scs) {
            sign_det * r = new (allocator()) sign_det();
            r->M.swap(M);
            set_array_p(r->m_prs, prs);
            set_array_p(r->m_qs,  qs);
            r->m_sign_conditions.set(allocator(), scs.size(), scs.c_ptr());
            scs.release();
            return r;
        }

        /**
           \brief Create a new algebraic extension
         */
        algebraic * mk_algebraic(unsigned p_sz, value * const * p, mpbqi const & interval, sign_det * sd, unsigned sdt_idx) {
            unsigned idx = next_algebraic_idx();
            algebraic * r = new (allocator()) algebraic(idx);
            m_extensions[extension::ALGEBRAIC].push_back(r);
            
            set_p(r->m_p, p_sz, p);
            set_interval(r->m_interval, interval);
            r->m_sign_det = sd;
            inc_ref_sign_det(sd);
            r->m_sdt_idx  = sdt_idx;
            r->m_real     = is_real(p_sz, p);

            return r;
        }

        /**
           \brief Add a new root of p that is isolated by (interval, sd, sdt_idx) to roots.
        */
        void add_root(unsigned p_sz, value * const * p, mpbqi const & interval, sign_det * sd, unsigned sdt_idx, numeral_vector & roots) {
            algebraic * a = mk_algebraic(p_sz, p, interval, sd, sdt_idx);
            numeral r;
            set(r, mk_rational_function_value(a));
            roots.push_back(r);
        }

        /**
           \brief Isolate roots of p in the given interval using sign conditions to distinguish between them.
           We need this method when the polynomial contains roots that are infinitesimally close to each other.
           For example, given an infinitesimal eps, the polynomial (x - 1)(x - 1 - eps) == (1 + eps) + (- 2 - eps)*x + x^2 
           has two roots 1 and 1+eps, we can't isolate these roots using intervals with binary rational end points.
           In this case, we use the signs of (some of the) derivatives in the roots.
           By Thom's lemma, we know we can always use the signs of the derivatives to distinguish between different roots.
           
           Remark: the polynomials do not need to be the derivatives of p. We use derivatives because a simple
           sequential search can be used to find the set of polynomials that can be used to distinguish between
           the different roots.

           \pre num_roots is the number of roots in the given interval
        */
        void sign_det_isolate_roots(unsigned p_sz, value * const * p, int num_roots, mpbqi const & interval, numeral_vector & roots) {
            SASSERT(num_roots >= 2);
            scoped_polynomial_seq der_seq(*this);
            mk_derivatives(p_sz, p, der_seq);
            
            CASSERT("rcf_isolate_roots", TaQ_1(p_sz, p, interval) == num_roots);
            scoped_mpz_matrix M_s(mm());
            mm().mk(1, 1, M_s);
            M_s.set(0, 0, 1);
            
            // Sequence of polynomials associated with each row of M_s
            scoped_polynomial_seq prs(*this); 
            value * one_p[] = { one() };
            prs.push(1, one_p); // start with the polynomial one

            // For i in [0, poly_rows.size()), taqrs[i] == TaQ(prs[i], p; interval)
            int_buffer taqrs;
            taqrs.push_back(num_roots);

            // Sequence of polynomials used to discriminate the roots of p
            scoped_polynomial_seq qs(*this);

            // Sequence of sign conditions associated with the columns of M_s
            // These are sign conditions on the polynomials in qs.
            scoped_sign_conditions scs(*this);
            scs.push_back(0);

            // Starting configuration
            // 
            // M_s   = {{1}}         Matrix of size 1x1 containing the value 1
            // prs   = [1]           Sequence of size 1 containing the constant polynomial 1 (one is always the first element of this sequence)
            // taqrs = [num_roots]   Sequence of size 1 containing the integer num_roots
            // scs   = [0]           Sequence of size 1 with the empty sign condition (i.e., NULL pointer)
            // qs    = {}            Empty set
            //

            scoped_mpz_matrix      new_M_s(mm());
            int_buffer             new_taqrs;
            scoped_polynomial_seq  new_prs(*this);
            scoped_sign_conditions new_scs(*this);
            
            int_buffer            sc_cardinalities;
            unsigned_buffer       cols_to_keep;
            unsigned_buffer       new_row_idxs;

            unsigned i = der_seq.size();
            // We perform the search backwards because the degrees are in decreasing order.
            while (i > 0) {
                --i;
                checkpoint();
                SASSERT(M_s.m() == M_s.n());
                SASSERT(M_s.m() == taqrs.size());
                SASSERT(M_s.m() == scs.size());
                TRACE("rcf_sign_det",
                      tout << M_s;
                      for (unsigned j = 0; j < scs.size(); j++) {
                          display_sign_conditions(tout, scs[j]); 
                          tout << " = " << taqrs[j] << "\n";
                      }
                      tout << "qs:\n";
                      for (unsigned j = 0; j < qs.size(); j++) {
                          display_poly(tout, qs.size(j), qs.coeffs(j)); tout << "\n";
                      });
                // We keep executing this loop until we have only one root for each sign condition in scs.
                // When this happens the polynomials in qs are the ones used to discriminate the roots of p.
                unsigned q_sz     = der_seq.size(i);
                value * const * q = der_seq.coeffs(i);
                // q is a derivative of p.
                int q_eq_0, q_gt_0, q_lt_0;
                value_ref_buffer q2(*this);
                count_signs_at_zeros(p_sz, p, q_sz, q, interval, num_roots, q_eq_0, q_gt_0, q_lt_0, q2);
                TRACE("rcf_sign_det",
                      tout << "q: "; display_poly(tout, q_sz, q); tout << "\n";
                      tout << "#(q == 0): " << q_eq_0 << ", #(q > 0): " << q_gt_0 << ", #(q < 0): " << q_lt_0 << "\n";);
                bool use_q2;
                scoped_mpz_matrix M(mm());
                if      (q_eq_0 > 0  && q_gt_0 > 0  && q_lt_0 == 0) {
                    // M <- {{1, 1}, 
                    //       {0, 1}}
                    mm().mk(2,2,M);
                    M.set(0,0, 1); M.set(0,1, 1); 
                    M.set(1,0, 0); M.set(1,1, 1);
                    use_q2 = false;
                }
                else if (q_eq_0 > 0  && q_gt_0 == 0 && q_lt_0 > 0)  {
                    // M <- {{1, 1}, 
                    //       {0, -1}}
                    mm().mk(2,2,M);
                    M.set(0,0, 1); M.set(0,1,  1); 
                    M.set(1,0, 0); M.set(1,1, -1);
                    use_q2 = false;
                }
                else if (q_eq_0 == 0 && q_gt_0 > 0  && q_lt_0 > 0)  {
                    // M <- {{1, 1}, 
                    //       {1, -1}}
                    mm().mk(2,2,M);
                    M.set(0,0, 1); M.set(0,1,  1); 
                    M.set(1,0, 1); M.set(1,1, -1);
                    use_q2 = false;
                }
                else if (q_eq_0 > 0  && q_gt_0 > 0  && q_lt_0 > 0)  {
                    // M <- {{1, 1,  1}, 
                    //       {0, 1, -1},
                    //       {0, 1,  1}}
                    mm().mk(3,3,M);
                    M.set(0,0, 1); M.set(0,1, 1); M.set(0,2,  1); 
                    M.set(1,0, 0); M.set(1,1, 1); M.set(1,2, -1);
                    M.set(2,0, 0); M.set(2,1, 1); M.set(2,2,  1);
                    use_q2 = true;
                    SASSERT(q2.size() > 0);
                }
                else {
                    // skip q since its sign does not discriminate the roots of p
                    continue;
                }
                mm().tensor_product(M_s, M, new_M_s);
                expand_taqrs(taqrs, prs, p_sz, p, q_sz, q, use_q2, q2.size(), q2.c_ptr(), interval,
                             // --->
                             new_taqrs, new_prs);
                SASSERT(new_M_s.n() == new_M_s.m());           // it is a square matrix
                SASSERT(new_M_s.m() == new_taqrs.size());  
                SASSERT(new_M_s.m() == new_prs.size());
                // The system must have a solution
                sc_cardinalities.resize(new_taqrs.size());
                // Solve
                //    new_M_s * sc_cardinalities = new_taqrs
                VERIFY(mm().solve(new_M_s, sc_cardinalities.c_ptr(), new_taqrs.c_ptr()));
                TRACE("rcf_sign_det", tout << "solution: "; for (unsigned i = 0; i < sc_cardinalities.size(); i++) { tout << sc_cardinalities[i] << " "; } tout << "\n";);
                // The solution must contain only positive values <= num_roots
                DEBUG_CODE(for (unsigned j = 0; j < sc_cardinalities.size(); j++) { SASSERT(0 <= sc_cardinalities[j] && sc_cardinalities[j] <= num_roots); });
                // We should keep q only if it discriminated something.
                // That is, 
                //   If !use_q2,   then There is an i s.t. sc_cardinalities[2*i] > 0 && sc_cardinalities[2*i] > 0
                //   If use_q2,    then There is an i s.t. AtLeatTwo(sc_cardinalities[3*i] > 0, sc_cardinalities[3*i+1] > 0, sc_cardinalities[3*i+2] > 0)
                if (!keep_new_sc_assignment(sc_cardinalities.size(), sc_cardinalities.c_ptr(), use_q2)) {
                    // skip q since it did not reduced the cardinality of the existing sign conditions.
                    continue; 
                }
                // keep q
                unsigned q_idx = qs.size();
                qs.push(q_sz, q);
                // We remove the columns associated with sign conditions that have cardinality zero, 
                // and create new extended sign condition objects for the ones that have cardinality > 0.
                cols_to_keep.reset();
                unsigned j = 0; unsigned k = 0;
                unsigned step_sz = use_q2 ? 3 : 2;
                bool all_one = true;
                while (j < sc_cardinalities.size()) {
                    sign_condition * sc = scs[k];
                    k++;
                    for (unsigned s = 0; s < step_sz; s++) {
                        // Remark: the second row of M contains the sign for q
                        if (sc_cardinalities[j] > 0) {
                            new_scs.push_back(mk_sign_condition(q_idx, M.get_int(1, s), sc)); 
                            cols_to_keep.push_back(j);
                        }
                        if (sc_cardinalities[j] > 1) 
                            all_one = false;
                        j++;
                    }
                }
                // Update scs with new_scs
                scs.copy_from(new_scs); 
                SASSERT(new_scs.empty());
                // Update M_s
                mm().filter_cols(new_M_s, cols_to_keep.size(), cols_to_keep.c_ptr(), M_s);
                SASSERT(M_s.n() == cols_to_keep.size());
                new_row_idxs.resize(cols_to_keep.size(), 0);
                unsigned new_num_rows = mm().linear_independent_rows(M_s, new_row_idxs.c_ptr(), M_s);
                SASSERT(new_num_rows == cols_to_keep.size());
                // Update taqrs and prs
                prs.reset();
                taqrs.reset();
                for (unsigned j = 0; j < new_num_rows; j++) {
                    unsigned rid = new_row_idxs[j];
                    prs.push(new_prs.size(rid), new_prs.coeffs(rid));
                    taqrs.push_back(new_taqrs[rid]);
                }
                if (all_one)  {
                    // Stop each remaining sign condition in scs has cardinality one
                    // So, they are discriminating the roots of p.
                    break; 
                }
            }
            TRACE("rcf_sign_det",
                  tout << "Final state\n";
                  display_poly(tout, p_sz, p); tout << "\n";
                  tout << M_s;
                  for (unsigned j = 0; j < scs.size(); j++) {
                      display_sign_conditions(tout, scs[j]); 
                      tout << " = " << taqrs[j] << "\n";
                  }
                  tout << "qs:\n";
                  for (unsigned j = 0; j < qs.size(); j++) {
                      display_poly(tout, qs.size(j), qs.coeffs(j)); tout << "\n";
                  }
                  tout << "prs:\n";
                  for (unsigned j = 0; j < prs.size(); j++) {
                      display_poly(tout, prs.size(j), prs.coeffs(j)); tout << "\n";
                  });
            SASSERT(M_s.n() == M_s.m()); SASSERT(M_s.n() == static_cast<unsigned>(num_roots));
            sign_det * sd = mk_sign_det(M_s, prs, qs, scs);
            for (unsigned idx = 0; idx < static_cast<unsigned>(num_roots); idx++) {
                add_root(p_sz, p, interval, sd, idx, roots);
            }
        }

        /**
           \brief Return true if p is a polynomial of the form a_{n-1}*x^{n-1} + a_0
        */
        bool is_nz_binomial(unsigned n, value * const * p) {
            SASSERT(n >= 2);
            SASSERT(!is_zero(p[0]));
            SASSERT(!is_zero(p[n-1]));
            for (unsigned i = 1; i < n - 1; i++) {
                if (!is_zero(p[i]))
                    return false;
            }
            return true;
        }

        /**
           \brief magnitude -> mpbq
        */
        void magnitude_to_mpbq(int mag, bool sign, mpbq & r) {
            if (mag < 0) {
                bqm().set(r, mpbq(1, -mag));
            }
            else {
                bqm().set(r, mpbq(2));
                bqm().power(r, mag);
            }
            if (sign)
                bqm().neg(r);
        }

        /**
           \brief Convert magnitudes for negative roots lower and upper bounds into an interval.
        */
        void mk_neg_interval(bool has_neg_lower, int neg_lower_N, bool has_neg_upper, int neg_upper_N, mpbqi & r) {
            scoped_mpbq aux(bqm());
            if (!has_neg_lower) {
                set_lower_inf(r);
            }
            else {
                magnitude_to_mpbq(neg_lower_N, true, aux);
                set_lower(r, aux);
            }
            if (!has_neg_upper) {
                set_upper_zero(r);
            }
            else {
                magnitude_to_mpbq(neg_upper_N, true, aux);
                set_upper(r, aux);
            }
        }

        /**
           \brief Convert magnitudes for negative roots lower and upper bounds into an interval.
        */
        void mk_pos_interval(bool has_pos_lower, int pos_lower_N, bool has_pos_upper, int pos_upper_N, mpbqi & r) {
            scoped_mpbq aux(bqm());
            if (!has_pos_lower) {
                set_lower_zero(r);
            }
            else {
                magnitude_to_mpbq(pos_lower_N, false, aux);
                set_lower(r, aux);
            }
            if (!has_pos_upper) {
                set_upper_inf(r);
            }
            else {
                magnitude_to_mpbq(pos_upper_N, false, aux);
                set_upper(r, aux);
            }
        }
        
        /**
           \brief Root isolation for polynomials that are
                   - nonlinear (degree > 2)
                   - zero is not a root
                   - square free
                   - nonconstant
        */
        void nl_nz_sqf_isolate_roots(unsigned n, value * const * p, numeral_vector & roots) {
            SASSERT(n > 2);
            SASSERT(!is_zero(p[0])); 
            SASSERT(!is_zero(p[n-1]));
            int pos_lower_N, pos_upper_N, neg_lower_N, neg_upper_N;
            bool has_neg_lower = neg_root_lower_bound(n, p, neg_lower_N);
            bool has_neg_upper = neg_root_upper_bound(n, p, neg_upper_N);
            bool has_pos_lower = pos_root_lower_bound(n, p, pos_lower_N);
            bool has_pos_upper = pos_root_upper_bound(n, p, pos_upper_N);
            TRACE("rcf_isolate", 
                  display_poly(tout, n, p); tout << "\n";
                  if (has_neg_lower) tout << "-2^" << neg_lower_N; else tout << "-oo";
                  tout << " < neg-roots < ";
                  if (has_neg_upper) tout << "-2^" << neg_upper_N; else tout << "0";
                  tout << "\n";
                  if (has_pos_lower) tout << "2^" << pos_lower_N; else tout << "0";
                  tout << " < pos-roots < ";
                  if (has_pos_upper) tout << "2^" << pos_upper_N; else tout << "oo";
                  tout << "\n";);
            // Compute the number of positive and negative roots
            scoped_polynomial_seq seq(*this);
            sturm_seq(n, p, seq);
            scoped_mpbqi minf_zero(bqim());
            set_lower_inf(minf_zero);
            set_upper_zero(minf_zero);
            int num_neg_roots = TaQ(seq, minf_zero);
            scoped_mpbqi zero_inf(bqim());
            set_lower_zero(zero_inf);
            set_upper_inf(zero_inf);
            int num_pos_roots = TaQ(seq, zero_inf);
            TRACE("rcf_isolate", 
                  tout << "num_neg_roots: " << num_neg_roots << "\n";
                  tout << "num_pos_roots: " << num_pos_roots << "\n";);
            scoped_mpbqi pos_interval(bqim());
            scoped_mpbqi neg_interval(bqim());
            mk_neg_interval(has_neg_lower, neg_lower_N, has_neg_upper, neg_upper_N, neg_interval);
            mk_pos_interval(has_pos_lower, pos_lower_N, has_pos_upper, pos_upper_N, pos_interval);
            if (num_neg_roots > 0) {
                if (num_neg_roots == 1) {
                    add_root(n, p, neg_interval, 0, UINT_MAX, roots);
                }
                else {
                    // TODO bisection
                    sign_det_isolate_roots(n, p, num_neg_roots, minf_zero, roots);
                }
            }
            
            if (num_pos_roots > 0) {
                if (num_pos_roots == 1) {
                    add_root(n, p, pos_interval, 0, UINT_MAX, roots);
                }
                else {
                    // TODO bisection
                    sign_det_isolate_roots(n, p, num_pos_roots, zero_inf, roots);
                }
            }
        }

        /**
           \brief Root isolation for polynomials that are
                   - zero is not a root
                   - square free
                   - nonconstant
        */
        void nz_sqf_isolate_roots(unsigned n, value * const * p, numeral_vector & roots) {
            SASSERT(n > 1);
            SASSERT(!is_zero(p[0])); 
            SASSERT(!is_zero(p[n-1]));
            if (n == 2) {
                // we don't need a field extension for linear polynomials.
                numeral r;
                value_ref v(*this);
                neg(p[0], v);
                div(v, p[1], v);
                set(r, v);
                roots.push_back(r);
            }
            else {
                nl_nz_sqf_isolate_roots(n, p, roots); 
            }
        }
        
        /**
           \brief Root isolation for polynomials where 0 is not a root.
        */
        void nz_isolate_roots(unsigned n, value * const * p, numeral_vector & roots) {
            TRACE("rcf_isolate", 
                  tout << "nz_isolate_roots\n";
                  display_poly(tout, n, p); tout << "\n";);
            SASSERT(n > 0);
            SASSERT(!is_zero(p[0])); 
            SASSERT(!is_zero(p[n-1]));
            if (n == 1) {
                // constant polynomial
                return; 
            }
            value_ref_buffer sqf(*this);
            square_free(n, p, sqf);
            nz_sqf_isolate_roots(sqf.size(), sqf.c_ptr(), roots);
        }

        /**
           \brief Root isolation entry point.
        */
        void isolate_roots(unsigned n, numeral const * p, numeral_vector & roots) {
            TRACE("rcf_isolate_bug", tout << "isolate_roots: "; for (unsigned i = 0; i < n; i++) { display(tout, p[i]); tout << " "; } tout << "\n";);
            SASSERT(n > 0);
            SASSERT(!is_zero(p[n-1]));
            if (n == 1) {
                // constant polynomial
                return; 
            }
            unsigned i = 0;
            for (; i < n; i++) {
                if (!is_zero(p[i]))
                    break;
            }
            SASSERT(i < n);
            SASSERT(!is_zero(p[i]));
            ptr_buffer<value> nz_p;
            for (; i < n; i++)
                nz_p.push_back(p[i].m_value);
            nz_isolate_roots(nz_p.size(), nz_p.c_ptr(), roots);
            if (nz_p.size() < n) {
                // zero is a root
                roots.push_back(numeral());
            }
        }

        void reset(numeral & a) {
            del(a);
            SASSERT(is_zero(a));
        }

        int sign(value * a) {
            if (is_zero(a))
                return 0;
            else if (is_nz_rational(a)) {
                return qm().is_pos(to_mpq(a)) ? 1 : -1;
            }
            else {
                SASSERT(!contains_zero(a->interval()));
                return bqim().is_P(a->interval()) ? 1 : -1;
            }
        }

        int sign(numeral const & a) {
            return sign(a.m_value);
        }
        
        /**
           \brief Return true the given rational function value is actually an integer.

           \pre a is a rational function (algebraic) extension.

           \remark If a is actually an integer, this method is also update its representation.
        */
        bool is_algebraic_int(numeral const & a) {
            SASSERT(is_rational_function(a));
            SASSERT(to_rational_function(a)->ext()->is_algebraic());
            
            // TODO
            return false;
        }

        /**
           \brief Return true if a is an integer
        */
        bool is_int(numeral const & a) {
            if (is_zero(a))
                return true;
            else if (is_nz_rational(a)) 
                return qm().is_int(to_mpq(a));
            else {
                rational_function_value * rf = to_rational_function(a);
                switch (rf->ext()->knd()) {
                case extension::TRANSCENDENTAL: return false;
                case extension::INFINITESIMAL:  return false;
                case extension::ALGEBRAIC: return is_algebraic_int(a);
                default:
                    UNREACHABLE();
                    return false;
                }
            }
        }

        /**
           \brief Return true if v does not depend on infinitesimal extensions.
        */
        bool is_real(value * v) const {
            if (is_zero(v) || is_nz_rational(v))
                return true;
            else
                return to_rational_function(v)->is_real();
        }
        
        /**
           \brief Return true if a does not depend on infinitesimal extensions.
        */
        bool is_real(numeral const & a) const {
            return is_real(a.m_value);
        }

        static void swap(mpbqi & a, mpbqi & b) {
            realclosure::swap(a, b);
        }

        /**
           \brief Store in interval an approximation of the rational number q with precision k.
           interval has binary rational end-points and the width is <= 1/2^k
        */
        void mpq_to_mpbqi(mpq const & q, mpbqi & interval, unsigned k) {
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
                while (contains_zero(interval) || !check_precision(interval, k) || bqm().is_zero(interval.lower()) || bqm().is_zero(interval.upper())) {
                    checkpoint();
                    bqm().refine_lower(q, interval.lower(), interval.upper());
                    bqm().refine_upper(q, interval.lower(), interval.upper());
                }
            }
        }

        void initialize_rational_value_interval(value * a) {
            // For rational values, we only compute the binary intervals if needed.
            SASSERT(is_nz_rational(a));
            mpq_to_mpbqi(to_mpq(a), a->m_interval, m_ini_precision);
        }

        mpbqi & interval(value * a) const {
            SASSERT(a != 0);
            if (contains_zero(a->m_interval)) {
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

        rational_value * mk_rational(mpbq const & v) {
            scoped_mpq v_q(qm()); // v as a rational
            ::to_mpq(qm(), v, v_q);
            return mk_rational(v_q);
        }

        void reset_interval(value * a) {
            bqim().reset(a->m_interval);
        }

        template<typename T>
        void update_mpq_value(value * a, T & v) {
            SASSERT(is_nz_rational(a));
            qm().set(to_mpq(a), v);
            reset_interval(a);
        }

        template<typename T>
        void update_mpq_value(numeral & a, T & v) {
            update_mpq_value(a.m_value, v);
        }

        /**
           \brief a <- n
        */
        void set(numeral & a, int n) {
            if (n == 0) {
                reset(a);
                return;
            }
            
            del(a);
            a.m_value = mk_rational();
            inc_ref(a.m_value);
            update_mpq_value(a, n);
        }

        /**
           \brief a <- n
        */
        void set(numeral & a, mpz const & n) {
            if (qm().is_zero(n)) {
                reset(a);
                return;
            }

            del(a);
            a.m_value = mk_rational();
            inc_ref(a.m_value);
            update_mpq_value(a, n);
        }
        
        /**
           \brief a <- n
        */
        void set(numeral & a, mpq const & n) {
            if (qm().is_zero(n)) {
                reset(a);
                return;
            }
            del(a);
            a.m_value = mk_rational();
            inc_ref(a.m_value);
            update_mpq_value(a, n);
        }
        
        /**
           \brief a <- n
        */
        void set(numeral & a, numeral const & n) {
            inc_ref(n.m_value);
            dec_ref(a.m_value);
            a.m_value = n.m_value;
        }

        /**
           \brief a <- b^{1/k}
        */
        void root(numeral const & a, unsigned k, numeral & b) {
            if (k == 0)
                throw exception("0-th root is indeterminate");
            
            if (k == 1 || is_zero(a)) {
                set(b, a);
                return;
            }

            if (sign(a) < 0 && k % 2 == 0)
                throw exception("even root of negative number");
            
            // create the polynomial p of the form x^k - a
            value_ref_buffer p(*this);
            value_ref neg_a(*this);
            neg(a.m_value, neg_a);
            p.push_back(neg_a);
            for (unsigned i = 0; i < k - 1; i++)
                p.push_back(0);
            p.push_back(one());
            
            numeral_vector roots;
            nz_isolate_roots(p.size(), p.c_ptr(), roots);
            SASSERT(roots.size() == 1 || roots.size() == 2);
            if (roots.size() == 1 || sign(roots[0].m_value) > 0) {
                set(b, roots[0]);
            }
            else {
                SASSERT(roots.size() == 2);
                SASSERT(sign(roots[1].m_value) > 0);
                set(b, roots[1]);
            }
            del(roots);
        }
      
        /**
           \brief a <- b^k
        */
        void power(numeral const & a, unsigned k, numeral & b) {
            unsigned mask = 1;
            value_ref power(*this);
            value_ref _b(*this);
            power = a.m_value;
            _b = one();
            while (mask <= k) {
                checkpoint();
                if (mask & k)
                    mul(_b, power, _b);
                mul(power, power, power);
                mask = mask << 1;
            }
            set(b, _b);
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
            SASSERT(p1 != r.c_ptr());
            SASSERT(p2 != r.c_ptr());
            r.reset();
            value_ref a_i(*this);
            unsigned min = std::min(sz1, sz2);
            unsigned i = 0;
            for (; i < min; i++) {
                add(p1[i], p2[i], a_i);
                r.push_back(a_i);
            }
            for (; i < sz1; i++)
                r.push_back(p1[i]);
            for (; i < sz2; i++)
                r.push_back(p2[i]);
            SASSERT(r.size() == std::max(sz1, sz2));
            adjust_size(r);
        }

        /**
           \brief r <- p + a
        */
        void add(unsigned sz, value * const * p, value * a, value_ref_buffer & r) {
            SASSERT(p != r.c_ptr());
            SASSERT(sz > 0);
            r.reset();
            value_ref a_0(*this);
            add(p[0], a, a_0);
            r.push_back(a_0);
            r.append(sz - 1, p + 1);
            adjust_size(r);
        }

        /**
           \brief r <- p1 - p2
        */
        void sub(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & r) {
            SASSERT(p1 != r.c_ptr());
            SASSERT(p2 != r.c_ptr());
            r.reset();
            value_ref a_i(*this);
            unsigned min = std::min(sz1, sz2);
            unsigned i = 0;
            for (; i < min; i++) {
                sub(p1[i], p2[i], a_i);
                r.push_back(a_i);
            }
            for (; i < sz1; i++)
                r.push_back(p1[i]);
            for (; i < sz2; i++) {
                neg(p2[i], a_i);
                r.push_back(a_i);
            }
            SASSERT(r.size() == std::max(sz1, sz2));
            adjust_size(r);
        }

        /**
           \brief r <- p - a
        */
        void sub(unsigned sz, value * const * p, value * a, value_ref_buffer & r) {
            SASSERT(p != r.c_ptr());
            SASSERT(sz > 0);
            r.reset();
            value_ref a_0(*this);
            sub(p[0], a, a_0);
            r.push_back(a_0);
            r.append(sz - 1, p + 1);
            adjust_size(r);
        }

        /**
           \brief r <- a * p
        */
        void mul(value * a, unsigned sz, value * const * p, value_ref_buffer & r) {
            SASSERT(p != r.c_ptr());
            r.reset();
            if (a == 0) 
                return;
            value_ref a_i(*this);
            for (unsigned i = 0; i < sz; i++) {
                mul(a, p[i], a_i);
                r.push_back(a_i);
            }
        }

        /**
           \brief r <- p1 * p2
        */
        void mul(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & r) {
            SASSERT(p1 != r.c_ptr());
            SASSERT(p2 != r.c_ptr());
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
                    mul(p1[i], p2[j], tmp);
                    add(r[i+j], tmp, tmp);
                    r.set(i+j, tmp);
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
            value_ref a_i(*this);
            unsigned sz = p.size();
            for (unsigned i = 0; i < sz; i++) {
                div(p[i], a, a_i);
                p.set(i, a_i);
            }
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
                    value_ref aux(*this);
                    while (true) {
                        checkpoint();
                        sz1 = r.size();
                        if (sz1 < sz2) {
                            adjust_size(q);
                            break;
                        }
                        unsigned m_n = sz1 - sz2; // m-n            
                        div(r[sz1 - 1], b_n, ratio);
                        // q[m_n] <- q[m_n] + r[sz1 - 1]/b_n
                        add(q[m_n], ratio, aux);
                        q.set(m_n, aux);
                        for (unsigned i = 0; i < sz2 - 1; i++) {
                            // r[i + m_n] <- r[i + m_n] - ratio * p2[i]
                            mul(ratio, p2[i], aux);
                            sub(r[i + m_n], aux, aux);
                            r.set(i + m_n, aux);
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
           \brief r <- p/a
        */
        void div(unsigned sz, value * const * p, value * a, value_ref_buffer & r) {
            value_ref a_i(*this);
            for (unsigned i = 0; i < sz; i++) {
                div(p[i], a, a_i);
                r.push_back(a_i);
            }
        }

        /**
           \brief r <- rem(p1, p2)
        */
        void rem(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & r) {
            SASSERT(p1 != r.c_ptr());
            SASSERT(p2 != r.c_ptr());
            TRACE("rcf_rem", 
                  tout << "rem\n";
                  display_poly(tout, sz1, p1); tout << "\n";
                  display_poly(tout, sz2, p2); tout << "\n";);
            r.reset();
            SASSERT(sz2 > 0);
            if (sz2 == 1)
                return;
            r.append(sz1, p1);
            if (sz1 <= 1)
                return; // r is p1
            value * b_n = p2[sz2 - 1];
            value_ref ratio(*this);
            value_ref new_a(*this);
            SASSERT(b_n != 0);
            while (true) {
                checkpoint();
                sz1 = r.size();
                if (sz1 < sz2) {
                    TRACE("rcf_rem", tout << "rem result\n"; display_poly(tout, r.size(), r.c_ptr()); tout << "\n";);
                    return;
                }
                unsigned m_n = sz1 - sz2;
                div(r[sz1 - 1], b_n, ratio);
                for (unsigned i = 0; i < sz2 - 1; i++) {
                    mul(ratio, p2[i], new_a);
                    sub(r[i + m_n], new_a, new_a);
                    r.set(i + m_n, new_a);
                }
                r.shrink(sz1 - 1);
                adjust_size(r);
            }
        }

        /**
           \brief r <- -p
        */
        void neg(unsigned sz, value * const * p, value_ref_buffer & r) {
            SASSERT(p != r.c_ptr());
            r.reset();
            value_ref a_i(*this);
            for (unsigned i = 0; i < sz; i++) {
                neg(p[i], a_i);
                r.push_back(a_i);
            }
        }
        
        /**
           \brief r <- -r
        */
        void neg(value_ref_buffer & r) {
            value_ref a_i(*this);
            unsigned sz = r.size();
            for (unsigned i = 0; i < sz; i++) {
                neg(r[i], a_i);
                r.set(i, a_i);
            }
        }

        /**
           \brief p <- -p
        */
        void neg(polynomial & p) {
            value_ref a_i(*this);
            unsigned sz = p.size();
            for (unsigned i = 0; i < sz; i++) {
                neg(p[i], a_i);
                inc_ref(a_i.get());
                dec_ref(p[i]);
                p[i] = a_i.get();
            }
        }

        /**
           \brief r <- srem(p1, p2)  
           Signed remainder
        */
        void srem(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & r) {
            SASSERT(p1 != r.c_ptr());
            SASSERT(p2 != r.c_ptr());
            rem(sz1, p1, sz2, p2, r);
            neg(r);
        }
        
        /**
           \brief Force the leading coefficient of p to be 1.
        */
        void mk_monic(value_ref_buffer & p) {
            unsigned sz = p.size();
            if (sz > 0) {
                value_ref a_i(*this);
                SASSERT(p[sz-1] != 0);
                if (!is_rational_one(p[sz-1])) {
                    for (unsigned i = 0; i < sz - 1; i++) {
                        div(p[i], p[sz-1], a_i);
                        p.set(i, a_i);
                    }
                    p.set(sz-1, one());
                }
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
                value_ref_buffer R(*this);
                A.append(sz1, p1);
                B.append(sz2, p2);
                while (true) {
                    TRACE("rcf_gcd",
                          tout << "A: "; display_poly(tout, A.size(), A.c_ptr()); tout << "\n";
                          tout << "B: "; display_poly(tout, B.size(), B.c_ptr()); tout << "\n";);
                    if (B.empty()) {
                        mk_monic(A);
                        r = A;
                        TRACE("rcf_gcd",
                              tout << "gcd result: "; display_poly(tout, r.size(), r.c_ptr()); tout << "\n";);
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
                    value_ref a_i(*this);
                    a_i = mk_rational(i_mpq);
                    mul(a_i, p[i], a_i);
                    r.push_back(a_i);
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
            value_ref_buffer p1_prime(*this);
            value_ref_buffer p1_prime_p2(*this);
            seq.push(sz1, p1);
            derivative(sz1, p1, p1_prime);
            mul(p1_prime.size(), p1_prime.c_ptr(), sz2, p2, p1_prime_p2);
            seq.push(p1_prime_p2.size(), p1_prime_p2.c_ptr());
            sturm_seq_core(seq);
        }
        
        /**
           \brief Return the sign of p(0)
        */
        int eval_sign_at_zero(unsigned n, value * const * p) {
            if (n == 0)
                return 0;
            return sign(p[0]);
        }

        /**
           \brief Return the sign of p(oo)
        */
        int eval_sign_at_plus_inf(unsigned n, value * const * p) {
            if (n == 0)
                return 0;
            SASSERT(!is_zero(p[n-1])); // p is well formed
            return sign(p[n-1]);
        }
        
        /**
           \brief Return the sign of p(-oo)
        */
        int eval_sign_at_minus_inf(unsigned n, value * const * p) {
            if (n == 0)
                return 0;
            SASSERT(!is_zero(p[n-1])); // p is well formed
            unsigned degree = n - 1;
            if (degree % 2 == 0)
                return sign(p[n - 1]);
            else
                return -sign(p[n - 1]);
        }

        /**
           \brief Store in r an approximation (as an interval) for the interval p(b).
           
           \pre n >= 2
        */
        void eval_sign_at_approx(unsigned n, value * const * p, mpbq const & b, mpbqi & r) {
            SASSERT(n >= 2);
            // We compute r using the Horner Sequence
            //  ((a_{n-1}*b + a_{n-2})*b + a_{n-3})*b + a_{n-4} ...
            // where a_i's are the intervals associated with coefficients of p.
            SASSERT(n > 0);
            SASSERT(p[n - 1] != 0);
            scoped_mpbqi bi(bqim());
            set_interval(bi, b);  // bi <- [b, b]
            // r <- a_n * bi
            bqim().mul(interval(p[n - 1]), bi, r); 
            unsigned i = n - 1;
            while (i > 0) {
                checkpoint();
                --i;
                if (p[i] != 0)
                    bqim().add(r, interval(p[i]), r);
                if (i > 0)
                    bqim().mul(r, bi, r);
            }
        }

        /**
           \brief We say a polynomial has "refinable" approximated coefficients if the intervals 
           approximating the coefficients do not have -oo or oo as lower/upper bounds.
        */
        bool has_refineable_approx_coeffs(unsigned n, value * const * p) {
            for (unsigned i = 0; i < n; i++) {
                if (p[i] != 0) {
                    mpbqi & a_i = interval(p[i]);
                    if (a_i.lower_is_inf() || a_i.upper_is_inf())
                        return false;
                }
            }
            return true;
        }

        /**
           \brief Evaluate the sign of p(b) by computing a value object.
        */
        int expensive_eval_sign_at(unsigned n, value * const * p, mpbq const & b) {
            SASSERT(n > 0);
            SASSERT(p[n - 1] != 0);
            value_ref bv(*this);
            bv = mk_rational(b);
            // We compute the result using the Horner Sequence
            //  ((a_{n-1}*bv + a_{n-2})*bv + a_{n-3})*bv + a_{n-4} ...
            // where a_i's are the coefficients of p.
            value_ref r(*this);
            // r <- a_{n-1} * bv
            mul(p[n - 1], bv, r);
            unsigned i = n - 1;
            while (i > 0) {
                checkpoint();
                --i;
                if (p[i] != 0)
                    add(r, p[i], r); // r <- r + a_i
                if (i > 0)
                    mul(r, bv, r); // r <- r * bv
            }
            return sign(r);
        }

        /**
           \brief Find the magnitude of the biggest interval use to approximate coefficients of p.

           \pre has_refineable_approx_coeffs(n, p)
        */
        int find_biggest_interval_magnitude(unsigned n, value * const * p) {
            int r = INT_MIN;
            for (unsigned i = 0; i < n; i++) {
                if (p[i] != 0) {
                    mpbqi & a_i = interval(p[i]);
                    SASSERT(!a_i.lower_is_inf() && !a_i.upper_is_inf());
                    int m = magnitude(a_i);
                    if (m > r)
                        r = m;
                }
            }
            return r;
        }
        
        /**
           \brief Return the sign of p(b)
        */
        int eval_sign_at(unsigned n, value * const * p, mpbq const & b) {
            scoped_mpbqi r(bqim());
            eval_sign_at_approx(n, p, b, r);
            if (!bqim().contains_zero(r)) {
                // we are done
                return bqim().is_P(r) ? 1 : -1;
            }
            else if (!has_refineable_approx_coeffs(n, p)) {
                return expensive_eval_sign_at(n, p, b);
            }
            else {
                int m = find_biggest_interval_magnitude(n, p);
                unsigned prec;
                if (m >= 0)
                    prec = 1;
                else 
                    prec = -m;
                SASSERT(prec >= 1);
                while (prec <= m_max_precision) {
                    checkpoint();
                    if (!refine_coeffs_interval(n, p, prec)) {
                        // Failed to refine intervals, p must depend on infinitesimal values.
                        // This can happen even if all intervals of coefficients of p are bounded.
                        return expensive_eval_sign_at(n, p, b);
                    }
                    eval_sign_at_approx(n, p, b, r);
                    if (!bqim().contains_zero(r)) {
                        // we are done
                        return bqim().is_P(r) ? 1 : -1;
                    }
                    prec++; // increase precision and try again.
                }
                return expensive_eval_sign_at(n, p, b);
            }
        }

        enum location {
            ZERO,
            MINUS_INF,
            PLUS_INF,
            MPBQ
        };
        
        /**
           \brief Compute the number of sign variations at position (loc, b) in the given polynomial sequence.
           The position (loc, b) should be interpreted in the following way:
           
           - (ZERO, *)      -> number of sign variations at 0.
           - (MINUS_INF, *) -> number of sign variations at -oo.
           - (PLUS_INF, *)  -> number of sign variations at oo.
           - (MPBQ, b)      -> number of sign variations at binary rational b.
        */
        unsigned sign_variations_at_core(scoped_polynomial_seq const & seq, location loc, mpbq const & b) {
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
                value * const * p = seq.coeffs(i);
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
        
        unsigned sign_variations_at_minus_inf(scoped_polynomial_seq const & seq) {
            mpbq dummy(0);
            return sign_variations_at_core(seq, MINUS_INF, dummy);
        }

        unsigned sign_variations_at_plus_inf(scoped_polynomial_seq const & seq) {
            mpbq dummy(0);
            return sign_variations_at_core(seq, PLUS_INF, dummy);
        }
        
        unsigned sign_variations_at_zero(scoped_polynomial_seq const & seq) {
            mpbq dummy(0);
            return sign_variations_at_core(seq, ZERO, dummy);
        }
        
        unsigned sign_variations_at(scoped_polynomial_seq const & seq, mpbq const & b) {
            return sign_variations_at_core(seq, MPBQ, b);
        }

        /**
           \brief Given a polynomial Sturm sequence seq for (P; P' * Q) and an interval (a, b], it returns
                 TaQ(Q, P; a, b) = 
                    #{ x \in (a, b] | P(x) = 0 and Q(x) > 0 }
                    -
                    #{ x \in (a, b] | P(x) = 0 and Q(x) < 0 }

           \remark This method ignores whether the interval end-points are closed or open.
        */
        int TaQ(scoped_polynomial_seq & seq, mpbqi const & interval) {
            int a, b;
            if (interval.lower_is_inf())
                a = sign_variations_at_minus_inf(seq);
            else if (bqm().is_zero(interval.lower()))
                a = sign_variations_at_zero(seq);
            else
                a = sign_variations_at(seq, interval.lower());

            if (interval.upper_is_inf())
                b = sign_variations_at_plus_inf(seq);
            else if (bqm().is_zero(interval.upper()))
                b = sign_variations_at_zero(seq);
            else
                b = sign_variations_at(seq, interval.upper());
            
            return a - b;
        }
        
        /**
           \brief Return TaQ(Q, P; a, b) = 
                    #{ x \in (a, b] | P(x) = 0 and Q(x) > 0 }
                    -
                    #{ x \in (a, b] | P(x) = 0 and Q(x) < 0 }

           \remark This method ignores whether the interval end-points are closed or open.
        */
        int TaQ(unsigned p_sz, value * const * p, unsigned q_sz, value * const * q, mpbqi const & interval) {
            scoped_polynomial_seq seq(*this);
            sturm_tarski_seq(p_sz, p, q_sz, q, seq);
            return TaQ(seq, interval);
        }

        /**
           \brief Return TaQ(1, P; a, b) = 
                    #{ x \in (a, b] | P(x) = 0 }
                    
           \remark This method ignores whether the interval end-points are closed or open.
        */
        int TaQ_1(unsigned p_sz, value * const * p, mpbqi const & interval) {
            scoped_polynomial_seq seq(*this);
            sturm_seq(p_sz, p, seq);
            return TaQ(seq, interval);
        }
            
        void refine_rational_interval(rational_value * v, unsigned prec) {
            mpbqi & i = interval(v);
            if (!i.lower_is_open() && !i.lower_is_open()) {
                SASSERT(bqm().eq(i.lower(), i.upper()));
                return;
            }
            while (!check_precision(i, prec)) {
                checkpoint();
                bqm().refine_lower(to_mpq(v), i.lower(), i.upper());
                bqm().refine_upper(to_mpq(v), i.lower(), i.upper());
            }
        }

        /**
           \brief Refine the interval for each coefficient of in the polynomial p.
        */
        bool refine_coeffs_interval(unsigned n, value * const * p, unsigned prec) {
            for (unsigned i = 0; i < n; i++) {
                if (p[i] != 0 && !refine_interval(p[i], prec))
                    return false;
            }
            return true;
        }

        /**
           \brief Refine the interval for each coefficient of in the polynomial p.
        */
        bool refine_coeffs_interval(polynomial const & p, unsigned prec) {
            return refine_coeffs_interval(p.size(), p.c_ptr(), prec);
        }

        /**
           \brief Store in r the interval p(v).
        */
        void polynomial_interval(polynomial const & p, mpbqi const & v, mpbqi & r) {
            // We compute r using the Horner Sequence
            //  ((a_n * v + a_{n-1})*v + a_{n-2})*v + a_{n-3} ...
            // where a_i's are the coefficients of p.
            unsigned sz = p.size();
            if (sz == 1) {
                bqim().set(r, interval(p[0]));
            }
            else {
                SASSERT(sz > 0);
                SASSERT(p[sz - 1] != 0);
                // r <- a_n * v
                bqim().mul(interval(p[sz-1]), v, r); 
                unsigned i = sz - 1;
                while (i > 0) {
                    --i;
                    if (p[i] != 0)
                        bqim().add(r, interval(p[i]), r);
                    if (i > 0)
                        bqim().mul(r, v, r);
                }
            }
        }

        /**
           \brief Update the interval of v by using the intervals of 
           extension and coefficients of the rational function.
        */
        void update_rf_interval(rational_function_value * v, unsigned prec) {
            if (is_rational_one(v->den())) {
                polynomial_interval(v->num(), v->ext()->interval(), v->interval());
            }
            else  {
                scoped_mpbqi num_i(bqim()), den_i(bqim());
                polynomial_interval(v->num(), v->ext()->interval(), num_i);
                polynomial_interval(v->den(), v->ext()->interval(), den_i);
                div(num_i, den_i, inc_precision(prec, 2), v->interval());
            }
        }

        void refine_transcendental_interval(rational_function_value * v, unsigned prec) {
            SASSERT(v->ext()->is_transcendental());
            polynomial const & n = v->num();
            polynomial const & d = v->den();
            unsigned _prec = prec;
            while (true) {
                VERIFY(refine_coeffs_interval(n, _prec)); // must return true because a transcendental never depends on an infinitesimal
                VERIFY(refine_coeffs_interval(d, _prec)); // must return true because a transcendental never depends on an infinitesimal
                refine_transcendental_interval(to_transcendental(v->ext()), _prec);
                update_rf_interval(v, prec);
                
                TRACE("rcf_transcendental", tout << "after update_rf_interval: " << magnitude(v->interval()) << " ";
                      bqim().display(tout, v->interval()); tout << std::endl;);
                
                if (check_precision(v->interval(), prec))
                    return;
                _prec++;
            }
        }

        bool refine_infinitesimal_interval(rational_function_value * v, unsigned prec) {
            SASSERT(v->ext()->is_infinitesimal());
            polynomial const & numerator   = v->num();
            polynomial const & denominator = v->den();
            unsigned num_idx = first_non_zero(numerator);
            unsigned den_idx = first_non_zero(denominator);
            if (num_idx == 0 && den_idx == 0) {
                unsigned _prec = prec;
                while (true) {
                    refine_interval(numerator[num_idx],   _prec);
                    refine_interval(denominator[num_idx], _prec);
                    mpbqi const & num_i = interval(numerator[num_idx]);
                    mpbqi const & den_i = interval(denominator[num_idx]);
                    SASSERT(!contains_zero(num_i));
                    SASSERT(!contains_zero(den_i));
                    if (is_open_interval(num_i) && is_open_interval(den_i)) {
                        // This case is simple because adding/subtracting infinitesimal quantities, will
                        // not change the interval.
                        div(num_i, den_i, inc_precision(prec, 2), v->interval());
                    }
                    else {
                        // The intervals num_i and den_i may not be open.
                        // Example: numerator[num_idx] or denominator[num_idx] are rationals
                        // that can be precisely represented as binary rationals.
                        scoped_mpbqi new_num_i(bqim());
                        scoped_mpbqi new_den_i(bqim());
                        mpbq tiny_value(1, _prec*2);
                        if (numerator.size() > 1)
                            add_infinitesimal(num_i, sign_of_first_non_zero(numerator, 1) > 0,   tiny_value, new_num_i);
                        else
                            bqim().set(new_num_i, num_i);
                        if (denominator.size() > 1)
                            add_infinitesimal(den_i, sign_of_first_non_zero(denominator, 1) > 0, tiny_value, new_den_i);
                        else
                            bqim().set(new_den_i, den_i);
                        div(new_num_i, new_den_i, inc_precision(prec, 2), v->interval());
                    }
                    if (check_precision(v->interval(), prec))
                        return true;
                    _prec++;
                }
            }
            else { 
                // The following condition must hold because gcd(numerator, denominator) == 1
                // If num_idx > 0 and den_idx > 0, eps^{min(num_idx, den_idx)} is a factor of gcd(numerator, denominator) 
                SASSERT(num_idx ==  0 || den_idx == 0);
                int s = sign(numerator[num_idx]) * sign(denominator[den_idx]);
                // The following must hold since numerator[num_idx] and denominator[den_idx] are not zero.
                SASSERT(s != 0); 
                if (num_idx == 0) {
                    SASSERT(den_idx > 0);
                    // |v| is bigger than any binary rational
                    // Interval can't be refined. There is no way to isolate an infinity with an interval with binary rational end points.
                    return false;
                }
                else {
                    SASSERT(num_idx > 0);
                    SASSERT(den_idx == 0);
                    // |v| is infinitely close to zero.
                    if (s == 1) {
                        // it is close from above
                        set_lower(v->interval(), mpbq(0));
                        set_upper(v->interval(), mpbq(1, prec));
                    }
                    else {
                        // it is close from below
                        set_lower(v->interval(), mpbq(-1, prec));
                        set_upper(v->interval(), mpbq(0));
                    }
                    return true;
                }
            }
        }

        bool refine_algebraic_interval(algebraic * a, unsigned prec) {
            if (a->sdt() != 0) {
                // we can't bisect the interval, since it contains more than one root.
                return false;
            }
            else {
                mpbqi & a_i = a->interval();
                SASSERT(!a_i.lower_is_inf() && !a_i.upper_is_inf());
                int  lower_sign = INT_MIN;
                while (!check_precision(a_i, prec)) {
                    checkpoint();
                    SASSERT(!bqm().eq(a_i.lower(), a_i.upper()));
                    scoped_mpbq m(bqm());
                    bqm().add(a_i.lower(), a_i.upper(), m);
                    bqm().div2(m);
                    int mid_sign   = eval_sign_at(a->p().size(), a->p().c_ptr(), m);
                    if (mid_sign == 0) {
                        // found the actual root
                        // set interval [m, m]
                        set_lower(a_i, m, false);
                        set_upper(a_i, m, false);
                        return true;
                    }
                    else {
                        SASSERT(mid_sign == 1 || mid_sign == -1);
                        if (lower_sign == INT_MIN) {
                            // initialize lower_sign
                            lower_sign = eval_sign_at(a->p().size(), a->p().c_ptr(), a_i.lower());
                        }
                        SASSERT(lower_sign == 1 || lower_sign == -1);
                        if (mid_sign == lower_sign) {
                            // improved lower bound
                            set_lower(a_i, m);
                        }
                        else {
                            // improved upper bound
                            set_upper(a_i, m);
                        }
                    }
                }
                return true;
            }
        }

        bool refine_algebraic_interval(rational_function_value * v, unsigned prec) {
            SASSERT(v->ext()->is_algebraic());
            polynomial const & n = v->num();
            polynomial const & d = v->den();
            unsigned _prec = prec;
            while (true) {
                if (!refine_coeffs_interval(n, _prec) ||
                    !refine_coeffs_interval(d, _prec) || 
                    !refine_algebraic_interval(to_algebraic(v->ext()), _prec))
                    return false;

                update_rf_interval(v, prec);
                TRACE("rcf_algebraic", tout << "after update_rf_interval: " << magnitude(v->interval()) << " "; bqim().display(tout, v->interval()); tout << std::endl;);
                if (check_precision(v->interval(), prec))
                    return true;
                _prec++;
            }
        }

        /**
           \brief Refine the interval of v to the desired precision (1/2^prec).
           Return false in case of failure. A failure can only happen if v depends on infinitesimal values.
        */
        bool refine_interval(value * v, unsigned prec) {
            checkpoint();
            SASSERT(!is_zero(v));
            int m = magnitude(interval(v));
            if (m == INT_MIN || (m < 0 && static_cast<unsigned>(-m) > prec))
                return true;
            save_interval_if_too_small(v);
            if (is_nz_rational(v)) {
                refine_rational_interval(to_nz_rational(v), prec);
                return true;
            }
            else { 
                rational_function_value * rf = to_rational_function(v);
                if (rf->ext()->is_transcendental()) {
                    refine_transcendental_interval(rf, prec);
                    return true;
                }
                else if (rf->ext()->is_infinitesimal())
                    return refine_infinitesimal_interval(rf, prec);
                else
                    return refine_algebraic_interval(rf, prec);
            }
        }

        /**
           \brief Return the position of the first non-zero coefficient of p.
         */
        static unsigned first_non_zero(polynomial const & p) {
            unsigned sz = p.size();
            for (unsigned i = 0; i < sz; i++) {
                if (p[i] != 0)
                    return i;
            }
            UNREACHABLE();
            return UINT_MAX;
        }

        /**
           \brief Return the sign of the first non zero coefficient starting at position start_idx
        */
        int sign_of_first_non_zero(polynomial const & p, unsigned start_idx) {
            unsigned sz = p.size();
            SASSERT(start_idx < sz);
            for (unsigned i = start_idx; i < sz; i++) {
                if (p[i] != 0)
                    return sign(p[i]);
            }
            UNREACHABLE();
            return 0;
        }
        
        /**
           out <- in + infinitesimal (if plus_eps == true) 
           out <- in - infinitesimal (if plus_eps == false)

           We use the following rules for performing the assignment
           
           If plus_eps == True
               If lower(in) == v (closed or open), then lower(out) == v and open
               If upper(in) == v and open,         then upper(out) == v and open
               If upper(in) == v and closed,       then upper(out) == new_v and open
                        where new_v is v + tiny_value / 2^k, where k is the smallest natural such that sign(new_v) == sign(v)
           If plus_eps == False
               If lower(in) == v and open,         then lower(out) == v and open
               If lower(in) == v and closed,       then lower(out) == new_v and open 
               If upper(in) == v (closed or open), then upper(out) == v and open
                        where new_v is v - tiny_value / 2^k, where k is the smallest natural such that sign(new_v) == sign(v)
        */
        void add_infinitesimal(mpbqi const & in, bool plus_eps, mpbq const & tiny_value, mpbqi & out) {
            set_interval(out, in);
            out.set_lower_is_open(true);
            out.set_upper_is_open(true);
            if (plus_eps) {
                if (!in.upper_is_open()) {
                    scoped_mpbq tval(bqm());
                    tval = tiny_value;
                    while (true) {
                        bqm().add(in.upper(), tval, out.upper());
                        if (bqm().is_pos(in.upper()) == bqm().is_pos(out.upper()))
                            return;
                        bqm().div2(tval);
                        checkpoint();
                    }
                }
            }
            else {
                if (!in.lower_is_open()) {
                    scoped_mpbq tval(bqm());
                    tval = tiny_value;
                    while (true) {
                        bqm().sub(in.lower(), tval, out.lower());
                        if (bqm().is_pos(in.lower()) == bqm().is_pos(out.lower()))
                            return;
                        bqm().div2(tval);
                        checkpoint();
                    }
                }
            }
        }

        /**
           \brief Determine the sign of an element of Q(trans_0, ..., trans_n)
        */
        void determine_transcendental_sign(rational_function_value * v) {
            // Remark: the sign of a rational function value on an transcendental is never zero.
            // Reason: The transcendental can be the root of a polynomial.
            SASSERT(v->ext()->is_transcendental());
            int m = magnitude(v->interval());
            unsigned prec = 1;
            if (m < 0)
                prec = static_cast<unsigned>(-m) + 1;
            while (contains_zero(v->interval())) {
                refine_transcendental_interval(v, prec);
                prec++;
            }
        }

        /**
           \brief Determine the sign of an element of Q(trans_0, ..., trans_n, eps_0, ..., eps_m)
        */
        void determine_infinitesimal_sign(rational_function_value * v) {
            // Remark: the sign of a rational function value on an infinitesimal is never zero.
            // Reason: An infinitesimal eps is transcendental in any field K. So, it can't be the root
            // of a polynomial.
            SASSERT(v->ext()->is_infinitesimal());
            polynomial const & numerator   = v->num();
            polynomial const & denominator = v->den();
            unsigned num_idx = first_non_zero(numerator);
            unsigned den_idx = first_non_zero(denominator);
            if (num_idx == 0 && den_idx == 0) {
                mpbqi const & num_i = interval(numerator[num_idx]);
                mpbqi const & den_i = interval(denominator[num_idx]);
                SASSERT(!contains_zero(num_i));
                SASSERT(!contains_zero(den_i));
                if (is_open_interval(num_i) && is_open_interval(den_i)) {
                    // This case is simple because adding/subtracting infinitesimal quantities, will
                    // not change the interval.
                    div(num_i, den_i, m_ini_precision, v->interval());
                }
                else {
                    // The intervals num_i and den_i may not be open.
                    // Example: numerator[num_idx] or denominator[num_idx] are rationals
                    // that can be precisely represented as binary rationals.
                    scoped_mpbqi new_num_i(bqim());
                    scoped_mpbqi new_den_i(bqim());
                    mpbq tiny_value(1, m_ini_precision); // 1/2^{m_ini_precision}
                    if (numerator.size() > 1)
                        add_infinitesimal(num_i, sign_of_first_non_zero(numerator, 1) > 0,   tiny_value, new_num_i);
                    else
                        bqim().set(new_num_i, num_i);
                    if (denominator.size() > 1)
                        add_infinitesimal(den_i, sign_of_first_non_zero(denominator, 1) > 0, tiny_value, new_den_i);
                    else
                        bqim().set(new_den_i, den_i);
                    div(new_num_i, new_den_i, m_ini_precision, v->interval());
                }
            }
            else { 
                // The following condition must hold because gcd(numerator, denominator) == 1
                // If num_idx > 0 and den_idx > 0, eps^{min(num_idx, den_idx)} is a factor of gcd(numerator, denominator) 
                SASSERT(num_idx ==  0 || den_idx == 0);
                int s = sign(numerator[num_idx]) * sign(denominator[den_idx]);
                // The following must hold since numerator[num_idx] and denominator[den_idx] are not zero.
                SASSERT(s != 0); 
                if (num_idx == 0) {
                    SASSERT(den_idx > 0);
                    // |v| is bigger than any binary rational
                    if (s == 1) {
                        // it is "oo"
                        set_lower(v->interval(), m_plus_inf_approx);
                        set_upper_inf(v->interval());
                    }
                    else {
                        // it is "-oo"
                        set_lower_inf(v->interval());
                        set_upper(v->interval(), m_minus_inf_approx);
                    }
                }
                else {
                    SASSERT(num_idx > 0);
                    SASSERT(den_idx == 0);
                    // |v| is infinitely close to zero.
                    if (s == 1) {
                        // it is close from above
                        set_lower(v->interval(), mpbq(0));
                        set_upper(v->interval(), mpbq(1, m_ini_precision));
                    }
                    else {
                        // it is close from below
                        set_lower(v->interval(), mpbq(-1, m_ini_precision));
                        set_upper(v->interval(), mpbq(0));
                    }
                }
            }
            SASSERT(!contains_zero(v->interval()));
        }

        bool determine_algebraic_sign(rational_function_value * v) {
            // TODO
            return false;
        }

        /**
           \brief Determine the sign of the new rational function value.
           The idea is to keep refinining the interval until interval of v does not contain 0.
           After a couple of steps we switch to expensive sign determination procedure.

           Return false if v is actually zero.
        */
        bool determine_sign(rational_function_value * v) {
            if (!contains_zero(v->interval()))
                return true;
            switch (v->ext()->knd()) {
            case extension::TRANSCENDENTAL: determine_transcendental_sign(v); return true; // it is never zero
            case extension::INFINITESIMAL:  determine_infinitesimal_sign(v); return true; // it is never zero
            case extension::ALGEBRAIC:      return determine_algebraic_sign(v);
            default:
                UNREACHABLE();
                return false;
            }
        }

        bool determine_sign(value_ref & r) {
            SASSERT(is_rational_function(r.get()));
            return determine_sign(to_rational_function(r.get()));
        }

        /**
           \brief Set new_p1 and new_p2 using the following normalization rules:
           - new_p1 <- p1/p2[0];       new_p2 <- one              IF  sz2 == 1
           - new_p1 <- one;            new_p2 <- p2/p1[0];        IF  sz1 == 1
           - new_p1 <- p1/gcd(p1, p2); new_p2 <- p2/gcd(p1, p2);  Otherwise
        */
        void normalize(unsigned sz1, value * const * p1, unsigned sz2, value * const * p2, value_ref_buffer & new_p1, value_ref_buffer & new_p2) {
            SASSERT(sz1 > 0 && sz2 > 0);
            if (sz2 == 1) {
                // - new_p1 <- p1/p2[0];       new_p2 <- one              IF  sz2 == 1
                div(sz1, p1, p2[0], new_p1);
                new_p2.reset(); new_p2.push_back(one());
            }
            else if (sz1 == 1) {
                SASSERT(sz2 > 1);
                // - new_p1 <- one;            new_p2 <- p2/p1[0];        IF  sz1 == 1
                new_p1.reset(); new_p1.push_back(one());
                div(sz2, p2, p1[0], new_p2);
            }
            else {
                // - new_p1 <- p1/gcd(p1, p2); new_p2 <- p2/gcd(p1, p2);  Otherwise
                value_ref_buffer g(*this);
                gcd(sz1, p1, sz2, p2, g);
                if (is_rational_one(g)) {
                    new_p1.append(sz1, p1);
                    new_p2.append(sz2, p2);
                }
                else if (g.size() == sz1 || g.size() == sz2) {
                    // After dividing p1 and p2 by g, one of the quotients will have size 1.
                    // Thus, we have to apply the first two rules again.
                    value_ref_buffer tmp_p1(*this);
                    value_ref_buffer tmp_p2(*this);
                    div(sz1, p1, g.size(), g.c_ptr(), tmp_p1);
                    div(sz2, p2, g.size(), g.c_ptr(), tmp_p2);
                    if (tmp_p2.size() == 1) {
                        div(tmp_p1.size(), tmp_p1.c_ptr(), tmp_p2[0], new_p1);
                        new_p2.reset(); new_p2.push_back(one());
                    }
                    else if (tmp_p1.size() == 1) {
                        SASSERT(tmp_p2.size() > 1);
                        new_p1.reset(); new_p1.push_back(one());
                        div(tmp_p2.size(), tmp_p2.c_ptr(), tmp_p1[0], new_p2);
                    }
                    else {
                        UNREACHABLE();
                    }
                }
                else {
                    div(sz1, p1, g.size(), g.c_ptr(), new_p1);
                    div(sz2, p2, g.size(), g.c_ptr(), new_p2);
                    SASSERT(new_p1.size() > 1);
                    SASSERT(new_p2.size() > 1);
                }
            }
        }

        /**
           \brief Create a new value using the a->ext(), and the given numerator and denominator.
           Use interval(a) + interval(b) as an initial approximation for the interval of the result, and invoke determine_sign()
        */
        void mk_add_value(rational_function_value * a, value * b, unsigned num_sz, value * const * num, unsigned den_sz, value * const * den, value_ref & r) {
            SASSERT(num_sz > 0 && den_sz > 0);
            if (num_sz == 1 && den_sz == 1) {
                // In this case, the normalization rules guarantee that den is one.
                SASSERT(is_rational_one(den[0]));
                r = num[0];
            }
            else {
                scoped_mpbqi ri(bqim());
                bqim().add(interval(a), interval(b), ri);
                r = mk_rational_function_value_core(a->ext(), num_sz, num, den_sz, den);
                swap(r->interval(), ri);
                if (determine_sign(r)) {
                    SASSERT(!contains_zero(r->interval()));
                }
                else {
                    // The new value is 0
                    r = 0;
                }
            }
        }

        /**
           \brief Add a value of 'a' the form n/1 with b where rank(a) > rank(b)
        */
        void add_p_v(rational_function_value * a, value * b, value_ref & r) {
            SASSERT(is_rational_one(a->den()));
            SASSERT(compare_rank(a, b) > 0);
            polynomial const & an  = a->num();
            polynomial const & one = a->den();
            SASSERT(an.size() > 1);
            value_ref_buffer new_num(*this);
            add(an.size(), an.c_ptr(), b, new_num);
            SASSERT(new_num.size() == an.size());
            mk_add_value(a, b, new_num.size(), new_num.c_ptr(), one.size(), one.c_ptr(), r);
        }
        
        /**
           \brief Add a value 'a' of the form n/d with b where rank(a) > rank(b)
        */
        void add_rf_v(rational_function_value * a, value * b, value_ref & r) {
            value_ref_buffer b_ad(*this);
            value_ref_buffer num(*this);
            polynomial const & an = a->num();
            polynomial const & ad = a->den();
            if (is_rational_one(ad)) {
                add_p_v(a, b, r);
            }
            else {
                // b_ad <- b * ad
                mul(b, ad.size(), ad.c_ptr(), b_ad);
                // num <- a + b * ad
                add(an.size(), an.c_ptr(), b_ad.size(), b_ad.c_ptr(), num);
                if (num.empty())
                    r = 0;
                else {
                    value_ref_buffer new_num(*this);
                    value_ref_buffer new_den(*this);
                    normalize(num.size(), num.c_ptr(), ad.size(), ad.c_ptr(), new_num, new_den);
                    mk_add_value(a, b, new_num.size(), new_num.c_ptr(), new_den.size(), new_den.c_ptr(), r);
                }
            }
        }

        /**
           \brief Add values 'a' and 'b' of the form n/1 and rank(a) == rank(b)
        */
        void add_p_p(rational_function_value * a, rational_function_value * b, value_ref & r) {
            SASSERT(is_rational_one(a->den()));
            SASSERT(is_rational_one(b->den()));
            SASSERT(compare_rank(a, b) == 0);
            polynomial const & an  = a->num();
            polynomial const & one = a->den();
            polynomial const & bn  = b->num();
            value_ref_buffer new_num(*this);
            add(an.size(), an.c_ptr(), bn.size(), bn.c_ptr(), new_num);
            if (new_num.empty())
                r = 0;
            else 
                mk_add_value(a, b, new_num.size(), new_num.c_ptr(), one.size(), one.c_ptr(), r);
        }
        
        /**
           \brief Add values 'a' and 'b' of the form n/d and rank(a) == rank(b)
        */
        void add_rf_rf(rational_function_value * a, rational_function_value * b, value_ref & r) {
            SASSERT(compare_rank(a, b) == 0);
            polynomial const & an = a->num();
            polynomial const & ad = a->den();
            polynomial const & bn = b->num();
            polynomial const & bd = b->den();
            if (is_rational_one(ad) && is_rational_one(bd)) {
                add_p_p(a, b, r);
            }
            else {
                value_ref_buffer an_bd(*this);
                value_ref_buffer bn_ad(*this);
                mul(an.size(), an.c_ptr(), bd.size(), bd.c_ptr(), an_bd);
                mul(bn.size(), bn.c_ptr(), ad.size(), ad.c_ptr(), bn_ad);
                value_ref_buffer num(*this);
                add(an_bd.size(), an_bd.c_ptr(), bn_ad.size(), bn_ad.c_ptr(), num);
                if (num.empty()) {
                    r = 0;
                }
                else {
                    value_ref_buffer den(*this);
                    mul(ad.size(), ad.c_ptr(), bd.size(), bd.c_ptr(), den);
                    value_ref_buffer new_num(*this);
                    value_ref_buffer new_den(*this);
                    normalize(num.size(), num.c_ptr(), den.size(), den.c_ptr(), new_num, new_den);
                    mk_add_value(a, b, new_num.size(), new_num.c_ptr(), new_den.size(), new_den.c_ptr(), r);
                }
            }
        }
        
        void add(value * a, value * b, value_ref & r) {
            if (a == 0) {
                r = b;
            }
            else if (b == 0) {
                r = a;
            }
            else if (is_nz_rational(a) && is_nz_rational(b)) {
                scoped_mpq v(qm());
                qm().add(to_mpq(a), to_mpq(b), v);
                if (qm().is_zero(v))
                    r = 0;
                else 
                    r = mk_rational(v);
            }
            else {
                switch (compare_rank(a, b)) {
                case -1: add_rf_v(to_rational_function(b), a, r); break; 
                case 0:  add_rf_rf(to_rational_function(a), to_rational_function(b), r); break;
                case 1:  add_rf_v(to_rational_function(a), b, r); break;
                default: UNREACHABLE();
                }
            }
        }
        
        void sub(value * a, value * b, value_ref & r) {
            if (a == 0) {
                neg(b, r);
            }
            else if (b == 0) {
                r = a;
            }
            else if (is_nz_rational(a) && is_nz_rational(b)) {
                scoped_mpq v(qm());
                qm().sub(to_mpq(a), to_mpq(b), v);
                if (qm().is_zero(v))
                    r = 0;
                else 
                    r = mk_rational(v);
            }
            else {
                value_ref neg_b(*this);
                neg(b, neg_b);
                switch (compare_rank(a, neg_b)) {
                case -1: add_rf_v(to_rational_function(neg_b), a, r); break;
                case 0:  add_rf_rf(to_rational_function(a), to_rational_function(neg_b), r); break;
                case 1:  add_rf_v(to_rational_function(a), neg_b, r); break;
                default: UNREACHABLE();
                }
            }
        }

        void neg_rf(rational_function_value * a, value_ref & r) {
            polynomial const & an = a->num();
            polynomial const & ad = a->den();
            value_ref_buffer new_num(*this);
            neg(an.size(), an.c_ptr(), new_num);
            scoped_mpbqi ri(bqim());
            bqim().neg(interval(a), ri);
            r = mk_rational_function_value_core(a->ext(), new_num.size(), new_num.c_ptr(), ad.size(), ad.c_ptr());
            swap(r->interval(), ri);
            SASSERT(!contains_zero(r->interval()));
        }

        void neg(value * a, value_ref & r) {
            if (a == 0) {
                r = 0;
            }
            else if (is_nz_rational(a)) {
                scoped_mpq v(qm());
                qm().set(v, to_mpq(a));
                qm().neg(v);
                r = mk_rational(v);
            }
            else {
                neg_rf(to_rational_function(a), r);
            }
        }

        /**
           \brief Create a new value using the a->ext(), and the given numerator and denominator.
           Use interval(a) * interval(b) as an initial approximation for the interval of the result, and invoke determine_sign()
        */
        void mk_mul_value(rational_function_value * a, value * b, unsigned num_sz, value * const * num, unsigned den_sz, value * const * den, value_ref & r) {
            SASSERT(num_sz > 0 && den_sz > 0);
            if (num_sz == 1 && den_sz == 1) {
                // In this case, the normalization rules guarantee that den is one.
                SASSERT(is_rational_one(den[0]));
                r = num[0];
            }
            else {
                scoped_mpbqi ri(bqim());
                bqim().mul(interval(a), interval(b), ri);
                r = mk_rational_function_value_core(a->ext(), num_sz, num, den_sz, den);
                swap(ri, r->interval());
                if (determine_sign(r)) {
                    SASSERT(!contains_zero(r->interval()));
                }
                else {
                    // The new value is 0
                    r = 0;
                }
            }
        }

        /**
           \brief Multiply a value of 'a' the form n/1 with b where rank(a) > rank(b)
        */
        void mul_p_v(rational_function_value * a, value * b, value_ref & r) {
            SASSERT(is_rational_one(a->den()));
            SASSERT(b != 0);
            SASSERT(compare_rank(a, b) > 0);
            polynomial const & an  = a->num();
            polynomial const & one = a->den();
            SASSERT(an.size() > 1);
            value_ref_buffer new_num(*this);
            mul(b, an.size(), an.c_ptr(), new_num);
            SASSERT(new_num.size() == an.size());
            mk_mul_value(a, b, new_num.size(), new_num.c_ptr(), one.size(), one.c_ptr(), r);
        }

        /**
           \brief Multiply a value 'a' of the form n/d with b where rank(a) > rank(b)
        */
        void mul_rf_v(rational_function_value * a, value * b, value_ref & r) {
            polynomial const & an = a->num();
            polynomial const & ad = a->den();
            if (is_rational_one(ad)) {
                mul_p_v(a, b, r);
            }
            else {
                value_ref_buffer num(*this);
                // num <- b * an
                mul(b, an.size(), an.c_ptr(), num);
                SASSERT(num.size() == an.size());
                value_ref_buffer new_num(*this);
                value_ref_buffer new_den(*this);
                normalize(num.size(), num.c_ptr(), ad.size(), ad.c_ptr(), new_num, new_den);
                mk_mul_value(a, b, new_num.size(), new_num.c_ptr(), new_den.size(), new_den.c_ptr(), r);
            }
        }

        /**
           \brief Multiply values 'a' and 'b' of the form n/1 and rank(a) == rank(b)
        */
        void mul_p_p(rational_function_value * a, rational_function_value * b, value_ref & r) {
            SASSERT(is_rational_one(a->den()));
            SASSERT(is_rational_one(b->den()));
            SASSERT(compare_rank(a, b) == 0);
            polynomial const & an  = a->num();
            polynomial const & one = a->den();
            polynomial const & bn  = b->num();
            value_ref_buffer new_num(*this);
            mul(an.size(), an.c_ptr(), bn.size(), bn.c_ptr(), new_num);
            SASSERT(!new_num.empty());
            mk_mul_value(a, b, new_num.size(), new_num.c_ptr(), one.size(), one.c_ptr(), r);
        }

        /**
           \brief Multiply values 'a' and 'b' of the form n/d and rank(a) == rank(b)
        */
        void mul_rf_rf(rational_function_value * a, rational_function_value * b, value_ref & r) {
            SASSERT(compare_rank(a, b) == 0);
            polynomial const & an = a->num();
            polynomial const & ad = a->den();
            polynomial const & bn = b->num();
            polynomial const & bd = b->den();
            if (is_rational_one(ad) && is_rational_one(bd)) {
                mul_p_p(a, b, r);
            }
            else {
                value_ref_buffer num(*this);
                value_ref_buffer den(*this);
                mul(an.size(), an.c_ptr(), bn.size(), bn.c_ptr(), num);
                mul(ad.size(), ad.c_ptr(), bd.size(), bd.c_ptr(), den);
                SASSERT(!num.empty()); SASSERT(!den.empty());
                value_ref_buffer new_num(*this);
                value_ref_buffer new_den(*this);
                normalize(num.size(), num.c_ptr(), den.size(), den.c_ptr(), new_num, new_den);
                mk_mul_value(a, b, new_num.size(), new_num.c_ptr(), new_den.size(), new_den.c_ptr(), r);
            }
        }

        void mul(value * a, value * b, value_ref & r) {
            if (a == 0 || b == 0) {
                r = 0;
            }
            else if (is_rational_one(a)) {
                r = b;
            }
            else if (is_rational_one(b)) {
                r = a;
            }
            else if (is_rational_minus_one(a)) {
                neg(b, r);
            }
            else if (is_rational_minus_one(b)) {
                neg(a, r);
            }
            else if (is_nz_rational(a) && is_nz_rational(b)) {
                scoped_mpq v(qm());
                qm().mul(to_mpq(a), to_mpq(b), v);
                r = mk_rational(v);
            }
            else {
                switch (compare_rank(a, b)) {
                case -1: mul_rf_v(to_rational_function(b), a, r); break; 
                case 0:  mul_rf_rf(to_rational_function(a), to_rational_function(b), r); break;
                case 1:  mul_rf_v(to_rational_function(a), b, r); break;
                default: UNREACHABLE();
                }
            }
        }

        void div(value * a, value * b, value_ref & r) {
            if (a == 0) {
                r = 0;
            }
            else if (b == 0) {
                throw exception("division by zero");
            }
            else if (is_rational_one(b)) {
                r = a;
            }
            else if (is_rational_one(a)) {
                inv(b, r);
            }
            else if (is_rational_minus_one(b)) {
                neg(a, r);
            }
            else if (is_nz_rational(a) && is_nz_rational(b)) {
                scoped_mpq v(qm());
                qm().div(to_mpq(a), to_mpq(b), v);
                r = mk_rational(v);
            }
            else {
                value_ref inv_b(*this);
                inv(b, inv_b);
                switch (compare_rank(a, inv_b)) {
                case -1: mul_rf_v(to_rational_function(inv_b), a, r);  break;
                case 0:  mul_rf_rf(to_rational_function(a), to_rational_function(inv_b), r); break;
                case 1:  mul_rf_v(to_rational_function(a), inv_b, r); break;
                default: UNREACHABLE();
                }
            }
        }

        void inv_rf(rational_function_value * a, value_ref & r) {
            polynomial const & an = a->num();
            polynomial const & ad = a->den();
            scoped_mpbqi ri(bqim());
            bqim().inv(interval(a), ri);
            r = mk_rational_function_value_core(a->ext(), ad.size(), ad.c_ptr(), an.size(), an.c_ptr());
            swap(r->interval(), ri);
            SASSERT(!contains_zero(r->interval()));
        }

        void inv(value * a, value_ref & r) {
            if (a == 0) {
                throw exception("division by zero");
            }
            if (is_nz_rational(a)) {
                scoped_mpq v(qm());
                qm().inv(to_mpq(a), v);
                r = mk_rational(v);
            }
            else {
                inv_rf(to_rational_function(a), r);
            }
        }

        void set(numeral & n, value * v) {
            inc_ref(v);
            dec_ref(n.m_value);
            n.m_value = v;
        }

        void set(numeral & n, value_ref const & v) {
            set(n, v.get());
        }

        void neg(numeral & a) {
            value_ref r(*this);
            neg(a.m_value, r);
            set(a, r);
        }

        void neg(numeral const & a, numeral & b) {
            value_ref r(*this);
            neg(a.m_value, r);
            set(b, r);
        }

        void inv(numeral & a) {
            value_ref r(*this);
            inv(a.m_value, r);
            set(a, r);
        }

        void inv(numeral const & a, numeral & b) {
            value_ref r(*this);
            inv(a.m_value, r);
            set(b, r);
        }

        void add(numeral const & a, numeral const & b, numeral & c) {
            value_ref r(*this);
            add(a.m_value, b.m_value, r);
            set(c, r);
        }

        void sub(numeral const & a, numeral const & b, numeral & c) {
            value_ref r(*this);
            sub(a.m_value, b.m_value, r);
            set(c, r);
        }

        void mul(numeral const & a, numeral const & b, numeral & c) {
            value_ref r(*this);
            mul(a.m_value, b.m_value, r);
            set(c, r);
        }
        
        void div(numeral const & a, numeral const & b, numeral & c) {
            value_ref r(*this);
            div(a.m_value, b.m_value, r);
            set(c, r);
        }

        int compare(value * a, value * b) {
            if (a == 0)
                return -sign(b);
            else if (b == 0)
                return sign(a);
            else if (is_nz_rational(a) && is_nz_rational(b))
                return qm().lt(to_mpq(a), to_mpq(b)) ? -1 : 1;
            else {
                // TODO: try to refine interval before switching to sub+sign approach
                if (bqim().before(interval(a), interval(b)))
                    return -1;
                else if (bqim().before(interval(b), interval(a)))
                    return 1;
                else {
                    value_ref diff(*this);
                    sub(a, b, diff);
                    return sign(diff);
                }
            }
        }

        int compare(numeral const & a, numeral const & b) {
            return compare(a.m_value, b.m_value);
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

        bool use_parenthesis(value * v) const {
            if (is_zero(v) || is_nz_rational(v)) 
                return false;
            rational_function_value * rf = to_rational_function(v);
            return rf->num().size() > 1 || !is_rational_one(rf->den());
        }

        template<typename DisplayVar>
        void display_polynomial(std::ostream & out, unsigned sz, value * const * p, DisplayVar const & display_var, bool compact) const {
            if (sz == 0) {
                out << "0";
                return;
            }
            unsigned i = sz;
            bool first = true;
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
                        if (use_parenthesis(p[i])) {
                            out << "(";
                            display(out, p[i], compact);
                            out << ")*";
                        }
                        else {
                            display(out, p[i], compact);
                            out << "*";
                        }
                    }
                    display_var(out, compact);
                    if (i > 1)
                        out << "^" << i;
                }
            }
        }

        template<typename DisplayVar>
        void display_polynomial(std::ostream & out, polynomial const & p, DisplayVar const & display_var, bool compact) const {
            display_polynomial(out, p.size(), p.c_ptr(), display_var, compact);
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
        
        void display_sign_conditions(std::ostream & out, sign_condition * sc) const {
            bool first = true;
            out << "{";
            while (sc) {
                if (first)
                    first = false;
                else
                    out << ", ";
                out << "q(" << sc->qidx() << ")";
                display_poly_sign(out, sc->sign());
                sc = sc->prev();
            }
            out << "}";
        }

        void display_sign_conditions(std::ostream & out, sign_condition * sc, array<polynomial> const & qs, bool compact) const {
            bool first = true;
            out << "{";
            while (sc) {
                if (first)
                    first = false;
                else
                    out << ", ";
                display_polynomial(out, qs[sc->qidx()], display_free_var_proc(), compact);
                display_poly_sign(out, sc->sign());
                sc = sc->prev();
            }
            out << "}";
        }

        void display_algebraic_def(std::ostream & out, algebraic * a, bool compact) const {
            out << "root(";
            display_polynomial(out, a->p(), display_free_var_proc(), compact);
            out << ", ";
            bqim().display(out, a->interval());
            out << ", ";
            if (a->sdt() != 0) 
                display_sign_conditions(out, a->sdt()->sc(a->sdt_idx()), a->sdt()->qs(), compact);
            else
                out << "{}";
            out << ")";
        }

        void display_poly(std::ostream & out, unsigned n, value * const * p) const {
            display_polynomial(out, n, p, display_free_var_proc(), false);
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
            if (refine_interval(a.m_value, precision*4)) {
                // hack
                if (bqm().is_int(i.lower())) 
                    bqm().display_decimal(out, i.upper(), precision);
                else
                    bqm().display_decimal(out, i.lower(), precision);
            }
            else {
                if (sign(a.m_value) > 0)
                    out << "?";
                else
                    out << "-?";
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

    // Helper object for restoring the value intervals.
    class save_interval_ctx {
        manager::imp * m;
    public:
        save_interval_ctx(manager const * _this):m(_this->m_imp) { SASSERT (m); }
        ~save_interval_ctx() { m->restore_saved_intervals(); }
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

    void manager::mk_pi(numeral & r) {
        m_imp->mk_pi(r);
    }

    void manager::mk_e(numeral & r) {
        m_imp->mk_e(r);
    }

    void manager::isolate_roots(unsigned n, numeral const * as, numeral_vector & roots) {
        save_interval_ctx ctx(this);
        m_imp->isolate_roots(n, as, roots);
    }

    void manager::reset(numeral & a) {
        m_imp->reset(a);
    }

    int manager::sign(numeral const & a) {
        save_interval_ctx ctx(this);
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
        save_interval_ctx ctx(this);
        m_imp->root(a, k, b);
    }
      
    void manager::power(numeral const & a, unsigned k, numeral & b) {
        save_interval_ctx ctx(this);
        m_imp->power(a, k, b);
    }

    void manager::add(numeral const & a, numeral const & b, numeral & c) {
        save_interval_ctx ctx(this);
        m_imp->add(a, b, c);
    }

    void manager::add(numeral const & a, mpz const & b, numeral & c) {
        scoped_numeral _b(*this);
        set(_b, b);
        add(a, _b, c);
    }

    void manager::sub(numeral const & a, numeral const & b, numeral & c) {
        save_interval_ctx ctx(this);
        m_imp->sub(a, b, c);
    }

    void manager::mul(numeral const & a, numeral const & b, numeral & c) {
        save_interval_ctx ctx(this);
        m_imp->mul(a, b, c);
    }

    void manager::neg(numeral & a) {
        save_interval_ctx ctx(this);
        m_imp->neg(a);
    }

    void manager::neg(numeral const & a, numeral & b) {
        save_interval_ctx ctx(this);
        m_imp->neg(a, b);
    }

    void manager::inv(numeral & a) {
        save_interval_ctx ctx(this);
        m_imp->inv(a);
    }

    void manager::inv(numeral const & a, numeral & b) {
        save_interval_ctx ctx(this);
        m_imp->inv(a, b);
    }

    void manager::div(numeral const & a, numeral const & b, numeral & c) {
        save_interval_ctx ctx(this);
        m_imp->div(a, b, c);
    }

    int manager::compare(numeral const & a, numeral const & b) {
        save_interval_ctx ctx(this);
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
        save_interval_ctx ctx(this);
        m_imp->select(prev, next, result);
    }
        
    void manager::display(std::ostream & out, numeral const & a) const {
        save_interval_ctx ctx(this);
        m_imp->display(out, a);
    }

    void manager::display_decimal(std::ostream & out, numeral const & a, unsigned precision) const {
        save_interval_ctx ctx(this);
        m_imp->display_decimal(out, a, precision);
    }

    void manager::display_interval(std::ostream & out, numeral const & a) const {
        save_interval_ctx ctx(this);
        m_imp->display_interval(out, a);
    }

};

void pp(realclosure::manager::imp * imp, realclosure::polynomial const & p, realclosure::extension * ext) {
    imp->display_polynomial_expr(std::cout, p, ext, false);
    std::cout << std::endl;
}

void pp(realclosure::manager::imp * imp, realclosure::value * v) {
    imp->display(std::cout, v, false);
    std::cout << std::endl;
}

void pp(realclosure::manager::imp * imp, unsigned sz, realclosure::value * const * p) {
    for (unsigned i = 0; i < sz; i++)
        pp(imp, p[i]);
}

void pp(realclosure::manager::imp * imp, realclosure::manager::imp::value_ref_buffer const & p) {
    for (unsigned i = 0; i < p.size(); i++)
        pp(imp, p[i]);
}

void pp(realclosure::manager::imp * imp, realclosure::mpbqi const & i) {
    imp->bqim().display(std::cout, i);
    std::cout << std::endl;
}

void pp(realclosure::manager::imp * imp, realclosure::manager::imp::scoped_mpqi const & i) {
    imp->qim().display(std::cout, i);
    std::cout << std::endl;
}

void pp(realclosure::manager::imp * imp, mpbq const & n) {
    imp->bqm().display(std::cout, n);
    std::cout << std::endl;
}

void pp(realclosure::manager::imp * imp, mpq const & n) {
    imp->qm().display(std::cout, n);
    std::cout << std::endl;
}
