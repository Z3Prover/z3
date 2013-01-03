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
        mpbqi    m_interval; // approximation as a binary rational
    };

    struct rational_value : public value {
        mpq      m_value;
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
    };
    
    bool operator==(extension_ref const & r1, extension_ref const & r2) { 
        return r1.m_kind == r2.m_kind && r1.m_idx == r2.m_idx;
    }
    
    bool operator<(extension_ref const & r1, extension_ref const & r2) { 
        return r1.m_kind < r2.m_kind || (r1.m_kind == r2.m_kind && r1.m_idx == r2.m_idx); 
    }

    struct composite_value : public value {
        polynomial    m_numerator;
        polynomial    m_denominator;
        extension_ref m_ext_ref;
        bool          m_real;
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
        char const *  m_prefix;
        extension(char const * p):m_ref_count(0), m_prefix(p) {}
    };

    struct algebraic : public extension {
        polynomial   m_p;
        mpbqi        m_interval;
        signs        m_signs;
        bool         m_real;
    };

    struct transcendental : public extension {
        mk_interval & m_proc;
        transcendental(char const * prefix, mk_interval & p):extension(prefix), m_proc(p) {}
    };
    
    typedef extension infinitesimal;

    struct manager::imp {
        small_object_allocator *       m_allocator;
        bool                           m_own_allocator;
        unsynch_mpq_manager &          m_qm;
        mpbq_manager                   m_bqm;
        mpqi_manager                   m_qim;
        mpbqi_manager                  m_bqim;
        value_vector                   m_to_delete;
        ptr_vector<extension>          m_extensions[3];
        volatile bool                  m_cancel;

        imp(unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a):
            m_allocator(a == 0 ? alloc(small_object_allocator, "realclosure") : a),
            m_own_allocator(a == 0),
            m_qm(qm),
            m_bqm(m_qm),
            m_qim(m_qm),
            m_bqim(m_bqm) {

            m_cancel = false;
        }

        ~imp() {
            if (m_own_allocator)
                dealloc(m_allocator);
        }

        unsynch_mpq_manager & qm() { return m_qm; }
        mpbq_manager & bqm() { return m_bqm; }
        mpqi_manager & qim() { return m_qim; }
        mpbqi_manager & bqim() { return m_bqim; }
        small_object_allocator & allocator() { return *m_allocator; }

        void cleanup(extension_ref::kind k) {
            ptr_vector<extension> & exts = m_extensions[k];
            // keep removing unused slots
            while (!exts.empty() && exts.back() == 0) {
                exts.pop_back();
            }
        }

        void set_cancel(bool f) {
            m_cancel = f;
        }

        void updt_params(params_ref const & p) {
            // TODO
        }

        void del_polynomial(polynomial & p) {
            unsigned sz = p.size();
            for (unsigned i = 0; i < sz; i++) {
                dec_ref_core(p[i]);
            }
            p.finalize(allocator());
        }

        void del_rational(rational_value * v) {
            qm().del(v->m_value);
            allocator().deallocate(sizeof(rational_value), v);
        }
        
        void del_composite(composite_value * v) {
            del_polynomial(v->m_numerator);
            del_polynomial(v->m_denominator);
            dec_ref_ext(v->m_ext_ref);
            allocator().deallocate(sizeof(composite_value), v);
        }

        void flush_to_delete() {
            while (!m_to_delete.empty()) {
                value * v = m_to_delete.back();
                m_to_delete.pop_back();
                if (v->m_rational)
                    del_rational(static_cast<rational_value*>(v));
                else
                    del_composite(static_cast<composite_value*>(v));
            }
        }

        void del_algebraic(algebraic * a) {
            del_polynomial(a->m_p);
            bqim().del(a->m_interval);
            unsigned sz = a->m_signs.size();
            for (unsigned i = 0; i < sz; i++) {
                del_polynomial(a->m_signs[i].first);
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
            SASSERT(m_extensions[x.m_kind][x.m_idx] != 0);
            m_extensions[x.m_kind][x.m_idx]->m_ref_count++;
        }

        void dec_ref_ext(extension_ref x) {
            SASSERT(m_extensions[x.m_kind][x.m_idx] != 0);
            extension * ext = m_extensions[x.m_kind][x.m_idx];
            SASSERT(ext->m_ref_count > 0);
            ext->m_ref_count--;
            if (ext->m_ref_count == 0) {
                m_extensions[x.m_kind][x.m_idx] = 0;
                switch (x.m_kind) {
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

        void mk_infinitesimal(char const * p, numeral & r) {
            // TODO
        }
        
        void mk_transcendental(char const * p, mk_interval & proc, numeral & r) {
            // TODO
        }

        void isolate_roots(char const * p, unsigned n, numeral const * as, numeral_vector & roots) {
            // TODO
        }

        void reset(numeral & a) {
            // TODO
        }

        int sign(numeral const & a) {
            // TODO
            return 0;
        }

        bool is_int(numeral const & a) {
            // TODO
            return false;
        }
        
        bool is_real(numeral const & a) {
            // TODO
            return false;
        }
        
        void set(numeral & a, int n) {
            // TODO
        }

        void set(numeral & a, mpz const & n) {
            // TODO
        }
        
        void set(numeral & a, mpq const & n) {
            // TODO
        }
        
        void set(numeral & a, numeral const & n) {
            // TODO
        }

        void root(numeral const & a, unsigned k, numeral & b) {
            // TODO
        }
      
        void power(numeral const & a, unsigned k, numeral & b) {
            // TODO
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
            // TODO
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
        
        void display(std::ostream & out, numeral const & a) const {
            // TODO
        }
        
        void display_decimal(std::ostream & out, numeral const & a, unsigned precision) const {
            // TODO
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
        m_imp->mk_infinitesimal(p, r);
    }
        
    void manager::mk_transcendental(char const * p, mk_interval & proc, numeral & r) {
        m_imp->mk_transcendental(p, proc, r);
    }

    void manager::isolate_roots(char const * p, unsigned n, numeral const * as, numeral_vector & roots) {
        m_imp->isolate_roots(p, n, as, roots);
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
