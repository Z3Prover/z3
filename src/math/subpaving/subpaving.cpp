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
#include "math/subpaving/subpaving.h"
#include "math/subpaving/subpaving_types.h"
#include "math/subpaving/subpaving_mpq.h"
#include "math/subpaving/subpaving_mpf.h"
#include "math/subpaving/subpaving_hwf.h"
#include "math/subpaving/subpaving_mpff.h"
#include "math/subpaving/subpaving_mpfx.h"

namespace subpaving {

    template<typename CTX>
    class context_wrapper : public context {
    protected:
        CTX m_ctx;
    public:
        context_wrapper(reslimit& lim, typename CTX::numeral_manager & m, params_ref const & p, small_object_allocator * a):m_ctx(lim, m, p, a) {}
        ~context_wrapper() override {}
        unsigned num_vars() const override { return m_ctx.num_vars(); }
        var mk_var(bool is_int) override { return m_ctx.mk_var(is_int); }
        bool is_int(var x) const override { return m_ctx.is_int(x); }
        var mk_monomial(unsigned sz, power const * pws) override { return m_ctx.mk_monomial(sz, pws); }
        void inc_ref(ineq * a) override { m_ctx.inc_ref(reinterpret_cast<typename CTX::ineq*>(a)); }
        void dec_ref(ineq * a) override { m_ctx.dec_ref(reinterpret_cast<typename CTX::ineq*>(a)); }
        void add_clause(unsigned sz, ineq * const * atoms) override { m_ctx.add_clause(sz, reinterpret_cast<typename CTX::ineq * const *>(atoms)); }
        void display_constraints(std::ostream & out, bool use_star) const override { m_ctx.display_constraints(out, use_star); }
        void set_display_proc(display_var_proc * p) override { m_ctx.set_display_proc(p); }
        void reset_statistics() override { m_ctx.reset_statistics(); }
        void collect_statistics(statistics & st) const override { m_ctx.collect_statistics(st); }
        void collect_param_descrs(param_descrs & r) override { m_ctx.collect_param_descrs(r); }
        void updt_params(params_ref const & p) override { m_ctx.updt_params(p); }
        void operator()() override { m_ctx(); }
        void display_bounds(std::ostream & out) const override { m_ctx.display_bounds(out); }
    };

    class context_mpq_wrapper : public context_wrapper<context_mpq> {
        scoped_mpq        m_c;
        scoped_mpq_vector m_as;
    public:
        context_mpq_wrapper(reslimit& lim, unsynch_mpq_manager & m, params_ref const & p, small_object_allocator * a):
            context_wrapper<context_mpq>(lim, m, p, a), 
            m_c(m), 
            m_as(m) 
        {}

        ~context_mpq_wrapper() override {}

        unsynch_mpq_manager & qm() const override { return m_ctx.nm(); }

        var mk_sum(mpz const & c, unsigned sz, mpz const * as, var const * xs) override {
            m_as.reserve(sz);
            for (unsigned i = 0; i < sz; i++) {
                m_ctx.nm().set(m_as[i], as[i]);
            }
            m_ctx.nm().set(m_c, c);
            return m_ctx.mk_sum(m_c, sz, m_as.c_ptr(), xs);
        }
        ineq * mk_ineq(var x, mpq const & k, bool lower, bool open) override {
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
        context_mpf_wrapper(reslimit& lim, f2n<mpf_manager> & fm, params_ref const & p, small_object_allocator * a):
            context_wrapper<context_mpf>(lim, fm, p, a),
            m_qm(fm.m().mpq_manager()),
            m_c(fm.m()),
            m_as(fm.m()),
            m_q1(m_qm),
            m_q2(m_qm) {
        }

        ~context_mpf_wrapper() override {}

        unsynch_mpq_manager & qm() const override { return m_qm; }

        var mk_sum(mpz const & c, unsigned sz, mpz const * as, var const * xs) override {
            try {
                m_as.reserve(sz);
                for (unsigned i = 0; i < sz; i++) {
                    int2mpf(as[i], m_as[i]);
                }
                int2mpf(c, m_c);
                return m_ctx.mk_sum(m_c, sz, m_as.c_ptr(), xs);
            }
            catch (const f2n<mpf_manager>::exception &) {
                throw subpaving::exception();
            }
        }
        ineq * mk_ineq(var x, mpq const & k, bool lower, bool open) override {
            try {
                f2n<mpf_manager> & m = m_ctx.nm();
                if (lower)
                    m.round_to_minus_inf();
                else
                    m.round_to_plus_inf();
                m.set(m_c, k);
                return reinterpret_cast<ineq*>(m_ctx.mk_ineq(x, m_c, lower, open));
            }
            catch (const f2n<mpf_manager>::exception &) {
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
            int64_t val   = m_qm.get_int64(a);
            double dval = static_cast<double>(val);
            m_ctx.nm().set(o, dval);
            double _dval = m_ctx.nm().m().to_double(o);
            // TODO check the following test
            if (static_cast<int64_t>(_dval) != val)
                throw subpaving::exception();
        }
        
    public:
        context_hwf_wrapper(reslimit& lim,f2n<hwf_manager> & fm, unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a):
            context_wrapper<context_hwf>(lim, fm, p, a),
            m_qm(qm) {
        }

        ~context_hwf_wrapper() override {}

        unsynch_mpq_manager & qm() const override { return m_qm; }

        var mk_sum(mpz const & c, unsigned sz, mpz const * as, var const * xs) override {
            try {
                m_as.reserve(sz);
                for (unsigned i = 0; i < sz; i++) {
                    int2hwf(as[i], m_as[i]);
                }
                int2hwf(c, m_c);
                return m_ctx.mk_sum(m_c, sz, m_as.c_ptr(), xs);
            }
            catch (const f2n<mpf_manager>::exception &) {
                throw subpaving::exception();
            }
        }
        ineq * mk_ineq(var x, mpq const & k, bool lower, bool open) override {
            try {
                f2n<hwf_manager> & m = m_ctx.nm();
                if (lower)
                    m.round_to_minus_inf();
                else
                    m.round_to_plus_inf();
                m.set(m_c, k);
                return reinterpret_cast<ineq*>(m_ctx.mk_ineq(x, m_c, lower, open));
            }
            catch (const f2n<mpf_manager>::exception &) {
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
        context_fpoint_wrapper(reslimit& lim, typename context_fpoint::numeral_manager & m, unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a):
            context_wrapper<context_fpoint>(lim, m, p, a),
            m_qm(qm), 
            m_c(m),
            m_as(m),
            m_z1(m_qm),
            m_z2(m_qm) {
        }

        ~context_fpoint_wrapper() override {}

        unsynch_mpq_manager & qm() const override { return m_qm; }

        var mk_sum(mpz const & c, unsigned sz, mpz const * as, var const * xs) override {
            try {
                m_as.reserve(sz);
                for (unsigned i = 0; i < sz; i++) {
                    int2fpoint(as[i], m_as[i]);
                }
                int2fpoint(c, m_c);
                return this->m_ctx.mk_sum(m_c, sz, m_as.c_ptr(), xs);
            }
            catch (const typename context_fpoint::numeral_manager::exception &) {
                throw subpaving::exception();
            }
        }
        
        ineq * mk_ineq(var x, mpq const & k, bool lower, bool open) override {
            try {
                typename context_fpoint::numeral_manager & m = this->m_ctx.nm();
                if (lower)
                    m.round_to_minus_inf();
                else
                    m.round_to_plus_inf();
                m.set(m_c, m_qm, k);
                return reinterpret_cast<ineq*>(this->m_ctx.mk_ineq(x, m_c, lower, open));
            }
            catch (const typename context_fpoint::numeral_manager::exception &) {
                throw subpaving::exception();
            }
        }
    };

    typedef context_fpoint_wrapper<context_mpff> context_mpff_wrapper;
    typedef context_fpoint_wrapper<context_mpfx> context_mpfx_wrapper;

    context * mk_mpq_context(reslimit& lim, unsynch_mpq_manager & m, params_ref const & p, small_object_allocator * a) {
        return alloc(context_mpq_wrapper, lim, m, p, a);
    }

    context * mk_mpf_context(reslimit& lim, f2n<mpf_manager> & m, params_ref const & p, small_object_allocator * a) {
        return alloc(context_mpf_wrapper, lim, m, p, a);
    }

    context * mk_hwf_context(reslimit& lim, f2n<hwf_manager> & m, unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a) {
        return alloc(context_hwf_wrapper, lim, m, qm, p, a);
    }

    context * mk_mpff_context(reslimit& lim, mpff_manager & m, unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a) {
        return alloc(context_mpff_wrapper, lim, m, qm, p, a);
    }

    context * mk_mpfx_context(reslimit& lim, mpfx_manager & m, unsynch_mpq_manager & qm, params_ref const & p, small_object_allocator * a) {
        return alloc(context_mpfx_wrapper, lim, m, qm, p, a);
    }

};
