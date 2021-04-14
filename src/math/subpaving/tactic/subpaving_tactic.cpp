/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    subpaving_tactic.cpp

Abstract:

    "Fake" tactic used to test subpaving module.

Author:

    Leonardo de Moura (leonardo) 2012-08-07.

Revision History:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "math/subpaving/tactic/expr2subpaving.h"
#include "ast/expr2var.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_smt2_pp.h"
#include "util/hwf.h"
#include "util/mpff.h"
#include "util/mpfx.h"
#include "util/f2n.h"

class subpaving_tactic : public tactic {

    struct display_var_proc : public subpaving::display_var_proc {
        expr_ref_vector m_inv;
        
        display_var_proc(expr2var & e2v):m_inv(e2v.m()) {
            e2v.mk_inv(m_inv);
        }

        virtual ~display_var_proc() {}
        
        ast_manager & m() const { return m_inv.get_manager(); }
        
        void operator()(std::ostream & out, subpaving::var x) const override {
            expr * t = m_inv.get(x, nullptr);
            if (t != nullptr)
                out << mk_ismt2_pp(t, m());
            else
                out << "k!" << x;
        }
    };

    struct imp {
        enum engine_kind { MPQ, MPF, HWF, MPFF, MPFX, NONE };

        ast_manager &                   m_manager;
        unsynch_mpq_manager             m_qm;
        mpf_manager                     m_fm_core;
        f2n<mpf_manager>                m_fm;
        hwf_manager                     m_hm_core;
        f2n<hwf_manager>                m_hm;
        mpff_manager                    m_ffm;
        mpfx_manager                    m_fxm;
        arith_util                      m_autil;
        engine_kind                     m_kind;
        scoped_ptr<subpaving::context>  m_ctx;
        scoped_ptr<display_var_proc>    m_proc;
        expr2var                        m_e2v;
        scoped_ptr<expr2subpaving>      m_e2s;
        bool                            m_display;
        
        imp(ast_manager & m, params_ref const & p):
            m_manager(m),
            m_fm(m_fm_core),
            m_hm(m_hm_core),
            m_autil(m),
            m_kind(NONE),
            m_e2v(m) {
            updt_params(p);
        }
        
        ast_manager & m() const { return m_manager; }
        
        void collect_param_descrs(param_descrs & r) {        
            m_ctx->collect_param_descrs(r);
            // #ifndef _EXTERNAL_RELEASE
            r.insert("numeral", CPK_SYMBOL, "(default: mpq) options: mpq, mpf, hwf, mpff, mpfx.");
            r.insert("print_nodes", CPK_BOOL, "(default: false) display subpaving tree leaves.");
            // #endif
        }
        
        void updt_params(params_ref const & p) {
            m_display = p.get_bool("print_nodes", false);
            symbol engine = p.get_sym("numeral", symbol("mpq"));
            engine_kind new_kind;
            if (engine == "mpq")
                new_kind = MPQ;
            else if (engine == "mpf")
                new_kind = MPF;
            else if (engine == "mpff")
                new_kind = MPFF;
            else if (engine == "mpfx")
                new_kind = MPFX;
            else 
                new_kind = HWF;
            if (m_kind != new_kind) {
                m_kind = new_kind;
                switch (m_kind) {
                case MPQ:  m_ctx = subpaving::mk_mpq_context(m().limit(), m_qm); break;
                case MPF:  m_ctx = subpaving::mk_mpf_context(m().limit(), m_fm); break;
                case HWF:  m_ctx = subpaving::mk_hwf_context(m().limit(), m_hm, m_qm); break;
                case MPFF: m_ctx = subpaving::mk_mpff_context(m().limit(), m_ffm, m_qm); break;
                case MPFX: m_ctx = subpaving::mk_mpfx_context(m().limit(), m_fxm, m_qm); break;
                default: UNREACHABLE(); break;
                }
                m_e2s = alloc(expr2subpaving, m_manager, *m_ctx, &m_e2v);
            }
            m_ctx->updt_params(p);
        }

        void collect_statistics(statistics & st) const {
            m_ctx->collect_statistics(st);
        }

        void reset_statistics() {
            m_ctx->reset_statistics();
        }

        subpaving::ineq * mk_ineq(expr * a) {
            bool neg = false;
            while (m().is_not(a, a))
                neg = !neg;
            bool lower;
            bool open  = false;
            if (m_autil.is_le(a)) {
                lower = false;
            }
            else if (m_autil.is_ge(a)) {
                lower = true;
            }
            else {
                throw tactic_exception("unsupported atom");
            }
            if (neg) {
                lower = !lower;
                open  = !open;
            }
            rational _k;
            if (!m_autil.is_numeral(to_app(a)->get_arg(1), _k))
                throw tactic_exception("use simplify tactic with option :arith-lhs true");
            scoped_mpq k(m_qm);
            k = _k.to_mpq();
            scoped_mpz n(m_qm), d(m_qm);
            subpaving::var x = m_e2s->internalize_term(to_app(a)->get_arg(0), n, d);
            m_qm.mul(d, k, k);
            m_qm.div(k, n, k);
            if (is_neg(n))
                lower = !lower;
            TRACE("subpaving_tactic", tout << x << " " << k << " " << lower << " " << open << "\n";);
            return m_ctx->mk_ineq(x, k, lower, open);
        }

        void process_clause(expr * c) {
            expr * const * args = nullptr;
            unsigned sz;
            if (m().is_or(c)) {
                args = to_app(c)->get_args();
                sz   = to_app(c)->get_num_args();
            }
            else {
                args = &c;
                sz   = 1;
            }
            ref_buffer<subpaving::ineq, subpaving::context> ineq_buffer(*m_ctx);
            for (unsigned i = 0; i < sz; i++) {
                ineq_buffer.push_back(mk_ineq(args[i]));
            }
            m_ctx->add_clause(sz, ineq_buffer.data());
        }
        
        void internalize(goal const & g) {
            try {
                for (unsigned i = 0; i < g.size(); i++) {
                    process_clause(g.form(i));
                }
            }
            catch (const subpaving::exception &) {
                throw tactic_exception("failed to internalize goal into subpaving module");
            }
        }

        void process(goal const & g) {
            internalize(g);
            m_proc = alloc(display_var_proc, m_e2v);
            m_ctx->set_display_proc(m_proc.get());
            try {
                (*m_ctx)();
            }
            catch (const subpaving::exception &) {
                throw tactic_exception("failed building subpaving tree...");
            }
            if (m_display) {
                m_ctx->display_constraints(std::cout);
                std::cout << "bounds at leaves: \n";
                m_ctx->display_bounds(std::cout);
            }
        }
    };
    
    imp *       m_imp;
    params_ref  m_params;
    statistics  m_stats;
public:

    subpaving_tactic(ast_manager & m, params_ref const & p):
        m_imp(alloc(imp, m, p)),
        m_params(p) {
    }

    ~subpaving_tactic() override {
        dealloc(m_imp);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(subpaving_tactic, m, m_params);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        m_imp->collect_param_descrs(r);
    }

    void collect_statistics(statistics & st) const override {
        st.copy(m_stats);
    }

    void reset_statistics() override {
        m_stats.reset();
    }

    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        try {
            m_imp->process(*in);
            m_imp->collect_statistics(m_stats);
            result.reset();
            result.push_back(in.get());
        }
        catch (z3_exception & ex) {
            // convert all Z3 exceptions into tactic exceptions
            throw tactic_exception(ex.msg());
        }
    }
    
    void cleanup() override {
        ast_manager & m = m_imp->m();
        dealloc(m_imp);
        m_imp = alloc(imp, m, m_params);
    }

};


tactic * mk_subpaving_tactic_core(ast_manager & m, params_ref const & p) {
    return alloc(subpaving_tactic, m, p);
}

tactic * mk_subpaving_tactic(ast_manager & m, params_ref const & p) {
    params_ref simp_p  = p;
    simp_p.set_bool("arith_lhs", true);
    simp_p.set_bool("expand_power", true);
    simp_p.set_uint("max_power", UINT_MAX);
    simp_p.set_bool("som", true);
    simp_p.set_bool("eq2ineq", true);
    simp_p.set_bool("elim_and", true);
    simp_p.set_bool("blast_distinct", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("mul_to_power", true);

    return and_then(using_params(mk_simplify_tactic(m, p),
                                 simp_p),
                    using_params(mk_simplify_tactic(m, p),
                                 simp2_p),
                    mk_subpaving_tactic_core(m, p));
}


