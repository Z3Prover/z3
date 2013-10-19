/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving.cpp

Abstract:

    Subpaving for non-linear arithmetic.
    This is a wrapper for the different implementations
    of the subpaving module.
    This wrapper is the main interface between Z3 other modules and subpaving.
    Thus, it assumes that polynomials have precise integer coefficients, and
    bounds are rationals. If a particular implementation uses floats, then
    internally the bounds are approximated.
    
Author:

    Leonardo de Moura (leonardo) 2012-08-07.

Revision History:

--*/
#include"subpaving.h"
#include"subpaving_types.h"
#include"subpaving_mpq.h"
#include"subpaving_mpf.h"
#include"subpaving_hwf.h"
#include"subpaving_mpff.h"
#include"subpaving_mpfx.h"

namespace subpaving {

    template<typename CTX>
    class context_wrapper : public context {
    protected:
        CTX m_ctx;
    public:
        context_wrapper(typename CTX::numeral_manager & m, params_ref const & p, small_object_allocator * a):m_ctx(m, p, a) {}
        virtual ~context_wrapper() {}
        virtual unsigned num_vars() const { return m_ctx.num_vars(); }
        virtual var mk_var(bool is_int) { return m_ctx.mk_var(is_int); }
        virtual bool is_int(var x) const { return m_ctx.is_int(x); }
        virtual var mk_monomial(unsigned sz, power const * pws) { return m_ctx.mk_monomial(sz, pws); }
        virtual void inc_ref(ineq * a) { m_ctx.inc_ref(reinterpret_cast<typename CTX::ineq*>(a)); }
        virtual void dec_ref(ineq * a) { m_ctx.dec_ref(reinterpret_cast<typename CTX::ineq*>(a)); }
        virtual void add_clause(unsigned sz, ineq * const * atoms) { m_ctx.add_clause(sz, reinterpret_cast<typename CTX::ineq * const *>(atoms)); }
        virtual void display_constraints(std::ostream & out, bool use_star) const { m_ctx.display_constraints(out, use_star); }
        virtual void set_cancel(bool f) { m_ctx.set_cancel(f); }
        virtual void set_display_proc(display_var_proc * p) { m_ctx.set_display_proc(p); }
        virtual void reset_statistics() { m_ctx.reset_statistics(); }
        virtual void collect_statistics(statistics & st) const { m_ctx.collect_statistics(st); }
        virtual void collect_param_descrs(param_descrs & r) { m_ctx.collect_param_descrs(r); }
        virtual void updt_params(params_ref const & p) { m_ctx.updt_params(p); }
        virtual void operator()() { m_ctx(); }
        virtual void display_bounds(std::ostream & out) const { m_ctx.display_bounds(out); }
    };

    class context_mpq_wrapper : public context_wrapper<context_mpq> {
        scoped_mpq        m_c;
        scoped_mpq_vector m_as;
    public:
        context_mpq_wrapper(unsynch_mpq_manager & m, params_ref const & p, small_object_allocator * a):
            context_wrapper<context_mpq>(m, p, a), 
            m_c(m), 
            m_as(m) 
        {}

        virtual ~context_mpq_wrapper() {}

        virtual unsynch_mpq_manager & qm() const { return m_ctx.nm(); }

        virtual var mk_sum(mpz const & c, unsigned sz, mpz const * as, var const * xs) {
            m_as.reserve(sz);
            for (unsigned i = 0; i < sz; i++) {
                m_ctx.nm().set(m_as[i], as[i]);
            }
            m_ctx.nm().set(m_c, c);
            return m_ctx.mk_sum(m_c, sz, m_as.c_ptr(), xs);
        }
        virtual ineq * mk_ineq(var x, mpq const & k, bool lower, bool open) { 
            return reinterpret_cast<ineq*>(m_ctx.mk_ineq(x, k, lower, open)); 
        }
    };

    class context_mpf_wrapper : public context_wrapper<context_mpf> {
        unsynch_mpq_manager &         m_qm;
        scoped_mpf                    m_c;
        scoped_mpf_vector             m_as;
        scoped_mpq                    m_q1, m_q2;
        
        // Convert the mpz (integer) into a mpf, and throws an exception if the conversion is not precise.
        void int2mpf(mpz const & a, mpf & o) {
            m_qm.set(m_q1, a);
            m_ctx.nm().set(o, m_q1);
            m_ctx.nm().m().to_rational(o, m_q2);
            if (!m_qm.eq(m_q1, m_q2))
                throw subpaving::exception();
        }
        
    public:
        context_mpf_wrapper(f2n<mpf_manager> & fm, params_ref const & p, small_object_allocator * a):
            context_wrapper<context_mpf>(fm, p, a),
            m_qm(fm.m().mpq_manager()),
            m_c(fm.m()),
            m_as(fm.m()),
            m_q1(m_qm),
            m_q2(m_qm) {
        }

        virtual ~context_mpf_wrapper() {}

        virtual unsynch_mpq_manager & qm() const { return m_qm; }

        virtual var mk_sum(mpz const & c, unsigned sz, mpz const * as, var const * xs) {
            try {
                m_as.reserve(sz);
                for (unsigned i = 0; i < sz; i++) {
                    int2mpf(as[i], m_as[i]);
                }
                int2mpf(c, m_c);
                return m_ctx.mk_sum(m_c, sz, m_as.c_ptr(), xs);
            }
            catch (f2n<mpf_manager>::exception) {
                throw subpaving::exception();
            }
        }
        virtual ineq * mk_ineq(var x, mpq const & k, bool lower, bool open) { 
            try {
                f2n<mpf_manager> & m = m_ctx.nm();
                if (lower)
                    m.round_to_minus_inf();
                else
                    m.round_to_plus_inf();
                m.set(m_c, k);
                return reinterpret_cast<ineq*>(m_ctx.mk_ineq(x, m_c, lower, open));
            }
            catch (f2n<mpf_manager>::exception) {
                throw subpaving::exception();
            }
        }
    };

    class context_hwf_wrapper : public context_wrapper<context_hwf> {
        unsynch_mpq_manager &         m_qm;
        hwf                           m_c;
        svector<hwf>                  m_as;
        
        // Convert the mpz (integer) into a hwf, and throws an exception if the conversion is not precise.
        void int2hwf(mpz const & a, hwf & o) {
            if (!m_qm.is_int64(a))
                throw subpaving::exception();
            int64 val   = m_qm.get_int64(a);
            double dval = static_cast<double>(val);
            m_ctx.nm().set(o, dval);
            double _dval = m_ctx.nm().m().to_double(o);
            // TODO check the following test
            if (static_cast<int64>(_dval) != val)
                throw subpaving::exception();
        }
        
    public:
        context_hwf_wrapper(f2n<hwf_manager> & fm, unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a):
            context_wrapper<context_hwf>(fm, p, a),
            m_qm(qm) {
        }

        virtual ~context_hwf_wrapper() {}

        virtual unsynch_mpq_manager & qm() const { return m_qm; }

        virtual var mk_sum(mpz const & c, unsigned sz, mpz const * as, var const * xs) {
            try {
                m_as.reserve(sz);
                for (unsigned i = 0; i < sz; i++) {
                    int2hwf(as[i], m_as[i]);
                }
                int2hwf(c, m_c);
                return m_ctx.mk_sum(m_c, sz, m_as.c_ptr(), xs);
            }
            catch (f2n<mpf_manager>::exception) {
                throw subpaving::exception();
            }
        }
        virtual ineq * mk_ineq(var x, mpq const & k, bool lower, bool open) { 
            try {
                f2n<hwf_manager> & m = m_ctx.nm();
                if (lower)
                    m.round_to_minus_inf();
                else
                    m.round_to_plus_inf();
                m.set(m_c, k);
                return reinterpret_cast<ineq*>(m_ctx.mk_ineq(x, m_c, lower, open));
            }
            catch (f2n<mpf_manager>::exception) {
                throw subpaving::exception();
            }
        }
    };

    template<typename context_fpoint>
    class context_fpoint_wrapper : public context_wrapper<context_fpoint> {
        unsynch_mpq_manager &  m_qm;
        _scoped_numeral<typename context_fpoint::numeral_manager>        m_c;
        _scoped_numeral_vector<typename context_fpoint::numeral_manager> m_as;
        scoped_mpz             m_z1, m_z2;

        void int2fpoint(mpz const & a, typename context_fpoint::numeral & o) {
            m_qm.set(m_z1, a);
            this->m_ctx.nm().set(o, m_qm, m_z1);
            this->m_ctx.nm().to_mpz(o, m_qm, m_z2);
            if (!m_qm.eq(m_z1, m_z2))
                throw subpaving::exception();
        }
        
    public:
        context_fpoint_wrapper(typename context_fpoint::numeral_manager & m, unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a):
            context_wrapper<context_fpoint>(m, p, a),
            m_qm(qm), 
            m_c(m),
            m_as(m),
            m_z1(m_qm),
            m_z2(m_qm) {
        }

        virtual ~context_fpoint_wrapper() {}

        virtual unsynch_mpq_manager & qm() const { return m_qm; }

        virtual var mk_sum(mpz const & c, unsigned sz, mpz const * as, var const * xs) {
            try {
                m_as.reserve(sz);
                for (unsigned i = 0; i < sz; i++) {
                    int2fpoint(as[i], m_as[i]);
                }
                int2fpoint(c, m_c);
                return this->m_ctx.mk_sum(m_c, sz, m_as.c_ptr(), xs);
            }
            catch (typename context_fpoint::numeral_manager::exception) {
                throw subpaving::exception();
            }
        }
        
        virtual ineq * mk_ineq(var x, mpq const & k, bool lower, bool open) { 
            try {
                typename context_fpoint::numeral_manager & m = this->m_ctx.nm();
                if (lower)
                    m.round_to_minus_inf();
                else
                    m.round_to_plus_inf();
                m.set(m_c, m_qm, k);
                return reinterpret_cast<ineq*>(this->m_ctx.mk_ineq(x, m_c, lower, open));
            }
            catch (typename context_fpoint::numeral_manager::exception) {
                throw subpaving::exception();
            }
        }
    };

    typedef context_fpoint_wrapper<context_mpff> context_mpff_wrapper;
    typedef context_fpoint_wrapper<context_mpfx> context_mpfx_wrapper;

    context * mk_mpq_context(unsynch_mpq_manager & m, params_ref const & p, small_object_allocator * a) {
        return alloc(context_mpq_wrapper, m, p, a);
    }

    context * mk_mpf_context(f2n<mpf_manager> & m, params_ref const & p, small_object_allocator * a) {
        return alloc(context_mpf_wrapper, m, p, a);
    }

    context * mk_hwf_context(f2n<hwf_manager> & m, unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a) {
        return alloc(context_hwf_wrapper, m, qm, p, a);
    }

    context * mk_mpff_context(mpff_manager & m, unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a) {
        return alloc(context_mpff_wrapper, m, qm, p, a);
    }

    context * mk_mpfx_context(mpfx_manager & m, unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a) {
        return alloc(context_mpfx_wrapper, m, qm, p, a);
    }

};
