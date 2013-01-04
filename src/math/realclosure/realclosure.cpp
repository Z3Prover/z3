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

namespace realclosure {
    
    // ---------------------------------
    //
    // Binary rational intervals
    //
    // ---------------------------------

    class mpbq_config {
        mpbq_manager &       m_manager;
    public:
        typedef mpbq_manager numeral_manager;
        typedef mpbq         numeral;

        struct interval {
            numeral   m_lower;
            numeral   m_upper;
            unsigned  m_lower_inf:1;
            unsigned  m_upper_inf:1;
        };

        void round_to_minus_inf() {}
        void round_to_plus_inf() {}
        void set_rounding(bool to_plus_inf) {}
        
        // Getters
        numeral const & lower(interval const & a) const { return a.m_lower; }
        numeral const & upper(interval const & a) const { return a.m_upper; }
        numeral & lower(interval & a) { return a.m_lower; }
        numeral & upper(interval & a) { return a.m_upper; }
        bool lower_is_open(interval const & a) const { return true; }
        bool upper_is_open(interval const & a) const { return true; }
        bool lower_is_inf(interval const & a) const { return a.m_lower_inf; }
        bool upper_is_inf(interval const & a) const { return a.m_upper_inf; }
        
        // Setters
        void set_lower(interval & a, numeral const & n) { m_manager.set(a.m_lower, n); }
        void set_upper(interval & a, numeral const & n) { m_manager.set(a.m_upper, n); }
        void set_lower_is_open(interval & a, bool v) { SASSERT(v); }
        void set_upper_is_open(interval & a, bool v) { SASSERT(v); }
        void set_lower_is_inf(interval & a, bool v) { a.m_lower_inf = v; }
        void set_upper_is_inf(interval & a, bool v) { a.m_upper_inf = v; }
        
        // Reference to numeral manager
        numeral_manager & m() const { return m_manager; }
        
        mpbq_config(numeral_manager & m):m_manager(m) {}
    };
  
    typedef interval_manager<mpbq_config> mpbqi_manager;
    typedef mpbqi_manager::interval       mpbqi;

    // ---------------------------------
    //
    // Values: rational and composite
    //
    // ---------------------------------

    struct value {
        unsigned m_ref_count;
        bool     m_rational;
        value():m_ref_count(0), m_rational(false) {}
        bool is_rational() const { return m_rational; }
    };

    struct rational_value : public value {
        mpq      m_value;
        mpbqi    m_interval; // approximation as a binary rational
    };

    typedef ptr_array<value> polynomial;
    
    /**
       \brief Reference to a field extension element.
       The element can be a transcendental real value, an infinitesimal, or an algebraic extension.
    */
    struct extension_ref {
        enum kind {
            TRANSCENDENTAL = 0,
            INFINITESIMAL  = 1,
            ALGEBRAIC      = 2
        };
        unsigned m_kind:2;
        unsigned m_idx:30;
        unsigned idx() const { return m_idx; }
        kind knd() const { return static_cast<kind>(m_kind); }
        bool is_algebraic() const { return knd() == ALGEBRAIC; }
        bool is_infinitesimal() const { return knd() == INFINITESIMAL; }
        bool is_transcendental() const { return knd() == TRANSCENDENTAL; }
    };

    bool operator==(extension_ref const & r1, extension_ref const & r2) { 
        return r1.knd() == r2.knd() && r1.idx() == r2.idx();
    }
    
    bool operator<(extension_ref const & r1, extension_ref const & r2) { 
        return r1.knd() < r2.knd() || (r1.knd() == r2.knd() && r1.idx() < r2.idx()); 
    }

    bool operator<=(extension_ref const & r1, extension_ref const & r2) { 
        return r1.knd() < r2.knd() || (r1.knd() == r2.knd() && r1.idx() <= r2.idx()); 
    }

    typedef svector<extension_ref> extension_ref_vector;

    struct polynomial_expr {
        // The values occurring in this polynomial m_p may only contain extensions that are smaller than m_ext_ref.
        // The polynomial m_p must not be the constant polynomial on m_ext_ref. That is,
        // it contains a nonzero coefficient at position k > 0. It is not a constant polynomial on m_ext_ref.
        polynomial     m_p; 
        extension_ref  m_ext_ref;
        bool           m_real;
        mpbqi          m_interval; // approximation as a binary rational
        
        extension_ref const & ext_ref() const { return m_ext_ref; }
        bool is_real() const { return m_real; }
        polynomial const & p() const { return m_p; }
    };

    struct rational_function_value : public value {
        // We assume that a null polynomial_expr denotes 1.
        // m_numerator OR m_denominator must be different from NULL
        polynomial_expr * m_numerator;   
        polynomial_expr * m_denominator; 
        
        polynomial_expr * num() const { return m_numerator; }
        polynomial_expr * den() const { return m_denominator; }

        extension_ref const & ext_ref() const {
            if (den() == 0)
                return num()->ext_ref();
            else if (num() == 0 || num()->ext_ref() < den()->ext_ref())
                return den()->ext_ref();
            else
                return num()->ext_ref();
        }

        bool is_real() const { 
            if (den() == 0)
                return num()->is_real();
            else if (num() == 0)
                return den()->is_real();
            else
                return num()->is_real() && den()->is_real();
        }
    };

    typedef ptr_vector<value> value_vector;

    // ---------------------------------
    //
    // Root object definition
    //
    // ---------------------------------
    
    typedef int sign;

    typedef std::pair<polynomial, int> p2s;

    typedef sarray<p2s> signs;

    struct extension {
        unsigned      m_ref_count;
        extension():m_ref_count(0) {}
    };

    struct algebraic : public extension {
        polynomial   m_p;
        mpbqi        m_interval;
        signs        m_signs;
        bool         m_real;

        polynomial const & p() const { return m_p; }
        mpbqi const & interval() const { return m_interval; }
        signs const & s() const { return m_signs; }
    };

    struct transcendental : public extension {
        symbol        m_name;
        mk_interval & m_proc;
        transcendental(symbol const & n, mk_interval & p):m_name(n), m_proc(p) {}
        void display(std::ostream & out) const {
            out << m_name;
        }
    };
    
    struct infinitesimal : public extension {
        symbol        m_name;
        infinitesimal(symbol const & n):m_name(n) {}
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
        mpbq_manager                   m_bqm;
        mpqi_manager                   m_qim;
        mpbqi_manager                  m_bqim;
        value_vector                   m_to_delete;
        ptr_vector<extension>          m_extensions[3];
        value *                        m_one;
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
            m_cancel = false;
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

        void cleanup(extension_ref::kind k) {
            ptr_vector<extension> & exts = m_extensions[k];
            // keep removing unused slots
            while (!exts.empty() && exts.back() == 0) {
                exts.pop_back();
            }
        }

        unsigned next_transcendental_idx() {
            cleanup(extension_ref::TRANSCENDENTAL);
            return m_extensions[extension_ref::TRANSCENDENTAL].size();
        }

        unsigned next_infinitesimal_idx() {
            cleanup(extension_ref::INFINITESIMAL);
            return m_extensions[extension_ref::INFINITESIMAL].size();
        }
        
        void set_cancel(bool f) {
            m_cancel = f;
        }
        
        void updt_params(params_ref const & p) {
            // TODO
        }

        void finalize_polynomial(polynomial & p) {
            unsigned sz = p.size();
            for (unsigned i = 0; i < sz; i++) {
                dec_ref_core(p[i]);
            }
            p.finalize(allocator());
        }

        void del_polynomial_expr(polynomial_expr * p) {
            finalize_polynomial(p->m_p);
            bqim().del(p->m_interval);
            dec_ref_ext(p->m_ext_ref);
            allocator().deallocate(sizeof(polynomial_expr), p);
        }

        void del_rational(rational_value * v) {
            bqim().del(v->m_interval);
            qm().del(v->m_value);
            allocator().deallocate(sizeof(rational_value), v);
        }

        void del_rational_function(rational_function_value * v) {
            if (v->num())
                del_polynomial_expr(v->num());
            if (v->den())
                del_polynomial_expr(v->den());
            allocator().deallocate(sizeof(rational_function_value), v);
        }

        void flush_to_delete() {
            while (!m_to_delete.empty()) {
                value * v = m_to_delete.back();
                m_to_delete.pop_back();
                if (v->is_rational())
                    del_rational(static_cast<rational_value*>(v));
                else
                    del_rational_function(static_cast<rational_function_value*>(v));
            }
        }

        void del_algebraic(algebraic * a) {
            finalize_polynomial(a->m_p);
            bqim().del(a->m_interval);
            unsigned sz = a->m_signs.size();
            for (unsigned i = 0; i < sz; i++) {
                finalize_polynomial(a->m_signs[i].first);
            }
            allocator().deallocate(sizeof(algebraic), a);
        }

        void del_transcendental(transcendental * t) {
            allocator().deallocate(sizeof(transcendental), t);
        }
        
        void del_infinitesimal(infinitesimal * i) {
            allocator().deallocate(sizeof(infinitesimal), i);
        }

        void inc_ref_ext(extension_ref x) {
            SASSERT(m_extensions[x.knd()][x.idx()] != 0);
            m_extensions[x.knd()][x.idx()]->m_ref_count++;
        }

        void dec_ref_ext(extension_ref x) {
            SASSERT(m_extensions[x.knd()][x.idx()] != 0);
            extension * ext = m_extensions[x.knd()][x.idx()];
            SASSERT(ext->m_ref_count > 0);
            ext->m_ref_count--;
            if (ext->m_ref_count == 0) {
                m_extensions[x.knd()][x.idx()] = 0;
                switch (x.knd()) {
                case extension_ref::TRANSCENDENTAL: del_transcendental(static_cast<transcendental*>(ext)); break;
                case extension_ref::INFINITESIMAL:  del_infinitesimal(static_cast<infinitesimal*>(ext)); break;
                case extension_ref::ALGEBRAIC:      del_algebraic(static_cast<algebraic*>(ext)); break;
                }
            }
        }

        void inc_ref(value * v) {
            if (v)
                v->m_ref_count++;
        }

        void dec_ref_core(value * v) {
            if (v) {
                SASSERT(v->m_ref_count > 0);
                v->m_ref_count--;
                if (v->m_ref_count == 0)
                    m_to_delete.push_back(v);
            }
        }

        void dec_ref(value * v) {
            dec_ref_core(v);
            flush_to_delete();
        }

        void del(numeral & a) {
            dec_ref(a.m_value);
            a.m_value = 0;
        }

        static bool is_zero(value * v) {
            return v == 0;
        }

        static bool is_nz_rational(value * v) { 
            SASSERT(v != 0);
            return v->is_rational(); 
        }

        bool is_one(value * v) {
            return !is_zero(v) && is_nz_rational(v) && qm().is_one(to_mpq(v));
        }

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
            else if (to_rational_function(a)->ext_ref() == to_rational_function(b)->ext_ref())
                return 0;
            else 
                return to_rational_function(a)->ext_ref() < to_rational_function(b)->ext_ref() ? -1 : 1;
        }

        transcendental * to_transcendental(extension_ref const & r) const {
            SASSERT(r.is_transcendental());
            return static_cast<transcendental*>(m_extensions[r.knd()][r.idx()]);
        }

        infinitesimal * to_infinitesimal(extension_ref const & r) const {
            SASSERT(r.is_infinitesimal());
            return static_cast<infinitesimal*>(m_extensions[r.knd()][r.idx()]);
        }

        algebraic * to_algebraic(extension_ref const & r) const {
            SASSERT(r.is_algebraic());
            return static_cast<algebraic*>(m_extensions[r.knd()][r.idx()]);
        }

        void mk_infinitesimal(symbol const & n, numeral & r) {
            // TODO
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

        int sign(polynomial_expr * p) {
            if (p == 0) {
                // Remark: The null polynomial expression denotes 1
                return 1;
            }
            else {
                SASSERT(!bqim().contains_zero(p->m_interval));
                return bqim().is_P(p->m_interval) ? 1 : -1;
            }
        }
        
        int sign(numeral const & a) {
            if (is_zero(a))
                return 0;
            else if (is_nz_rational(a)) {
                return qm().is_pos(to_mpq(a)) ? 1 : -1;
            }
            else {
                rational_function_value * v = to_rational_function(a);
                return sign(v->num()) * sign(v->den());
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
        
        bool is_real(numeral const & a) const {
            if (is_zero(a) || is_nz_rational(a)) 
                return true;
            else 
                return to_rational_function(a)->is_real();
        }

        rational_value * mk_rational() {
            return new (allocator()) rational_value();
        }

        rational_value * mk_rational(mpq & v) {
            rational_value * r = mk_rational();
            ::swap(r->m_value, v);
            return r;
        }

        void set(numeral & a, int n) {
            if (n == 0) {
                reset(a);
                return;
            }
            
            if (!is_unique_nz_rational(a)) {
                del(a);
                a.m_value = mk_rational();
            }
            SASSERT(is_unique_nz_rational(a));
            qm().set(to_mpq(a), n);
        }

        void set(numeral & a, mpz const & n) {
            if (qm().is_zero(n)) {
                reset(a);
                return;
            }

            if (!is_unique_nz_rational(a)) {
                del(a);
                a.m_value = mk_rational();
            }
            SASSERT(is_unique_nz_rational(a));
            qm().set(to_mpq(a), n);
        }
        
        void set(numeral & a, mpq const & n) {
            if (qm().is_zero(n)) {
                reset(a);
                return;
            }

            if (!is_unique_nz_rational(a)) {
                del(a);
                a.m_value = mk_rational();
            }
            SASSERT(is_unique_nz_rational(a));
            qm().set(to_mpq(a), n);
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
            if (is_one(a))
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
            if (sz > 0 && !is_one(p[sz-1])) {
                SASSERT(p[sz-1] != 0);
                for (unsigned i = 0; i < sz - 1; i++) {
                    p.set(i, div(p[i], p[sz-1]));
                }
                p.set(0, one());
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
                    std::swap(v->m_numerator, v->m_denominator);
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
            imp const &            m;
            char_vector            m_visited; // Set of visited algebraic extensions.
            svector<extension_ref> m_found;   // vector/list of visited algebraic extensions.

            collect_algebraic_refs(imp const & _m):m(_m) {}

            void mark(extension_ref const & r) {
                if (r.is_algebraic()) {
                    m_visited.reserve(r.idx() + 1, false);
                    if (!m_visited[r.idx()]) {
                        m_visited[r.idx()] = true;
                        m_found.push_back(r);
                        algebraic * a = m.to_algebraic(r);
                        mark(a->p());
                    }
                }
            }

            void mark(polynomial_expr * p) {
                if (p == 0)
                    return;
                mark(p->ext_ref());
                mark(p->p());
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
                if (first)
                    first = false;
                else
                    out << " + ";
                if (i == 0)
                    display(out, p[i], compact);
                else {
                    out << "(";
                    display(out, p[i], compact);
                    out << ")*";
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

        struct display_ext_ref_proc {
            imp const &           m;
            extension_ref const & m_ref;    
            display_ext_ref_proc(imp const & _m, extension_ref const & r):m(_m), m_ref(r) {}
            void operator()(std::ostream & out, bool compact) const {
                m.display_ext_ref(out, m_ref, compact);
            }
        };

        void display_polynomial_expr(std::ostream & out, polynomial_expr const & p, bool compact) const {
            display_polynomial(out, p.p(), display_ext_ref_proc(*this, p.ext_ref()), compact);
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

        void display_ext_ref(std::ostream & out, extension_ref const & r, bool compact) const {
            switch (r.knd()) {
            case extension_ref::TRANSCENDENTAL: to_transcendental(r)->display(out); break;
            case extension_ref::INFINITESIMAL:  to_infinitesimal(r)->display(out); break;
            case extension_ref::ALGEBRAIC: 
                if (compact)
                    out << "r!" << r.idx();
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
                if (rf->den() == 0) {
                    display_polynomial_expr(out, *rf->num(), compact);
                }
                else if (rf->num() == 0) {
                    out << "1/(";
                    display_polynomial_expr(out, *rf->den(), compact);
                    out << ")";
                }
                else {
                    out << "(";
                    display_polynomial_expr(out, *rf->num(), compact);
                    out << ")/(";
                    display_polynomial_expr(out, *rf->den(), compact);
                    out << ")";
                }
            }
        }

        void display_compact(std::ostream & out, numeral const & a) const {
            collect_algebraic_refs c(*this);
            c.mark(a.m_value);
            if (c.m_found.empty()) {
                display(out, a.m_value, true);
            }
            else {
                std::sort(c.m_found.begin(), c.m_found.end());
                out << "[";
                display(out, a.m_value, true);
                for (unsigned i = 0; i < c.m_found.size(); i++) {
                    extension_ref const & r = c.m_found[i];
                    out << ", r!" << r.idx() << " = ";
                    display_algebraic_def(out, to_algebraic(r), true);
                }
                out << "]";
            }
        }
        
        void display(std::ostream & out, numeral const & a) const {
            display(out, a.m_value, false);
        }
        
        void display_decimal(std::ostream & out, numeral const & a, unsigned precision) const {
            if (!is_real(a))
                throw exception("number cannot be printed in decimal notation because it is not a real");
            if (is_zero(a)) {
                out << "0";
            }
            else if (is_nz_rational(a)) {
                qm().display_decimal(out, to_mpq(a), precision);
            }
            else {
                // TODO
            }
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

    void manager::mk_infinitesimal(char const * p, numeral & r) {
        m_imp->mk_infinitesimal(r);
    }

    void manager::mk_infinitesimal(numeral & r) {
        m_imp->mk_infinitesimal(r);
    }
        
    void manager::mk_transcendental(char const * p, mk_interval & proc, numeral & r) {
        m_imp->mk_transcendental(p, proc, r);
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

};
