/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    purify_arith_simplifier.h

Abstract:

    Simplifier for eliminating arithmetic operators: DIV, IDIV, MOD,
    TO_INT, and optionally (OP_IRRATIONAL_ALGEBRAIC_NUM).

    This simplifier uses the rewriter for also eliminating:
    OP_SUB, OP_UMINUS, OP_POWER (optionally), OP_REM, OP_IS_INT.

Author:

    Nikolaj Bjorner (nbjorner) 2024-01-01

--*/
#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/rewriter_def.h"
#include "math/polynomial/algebraic_numbers.h"
#include "ast/converters/generic_model_converter.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"

class purify_arith_simplifier : public dependent_expr_simplifier {
    arith_util         m_util;
    bool               m_elim_root_objs = true;
    bool               m_elim_inverses  = true;
    bool               m_complete       = true;

    arith_util & u() { return m_util; }

    struct bin_def {
        expr* x, *y, *d;
        bin_def(expr* x, expr* y, expr* d): x(x), y(y), d(d) {}
    };

    struct rw_cfg : public default_rewriter_cfg {
        purify_arith_simplifier &       m_owner;
        obj_hashtable<func_decl>        m_cannot_purify;
        obj_map<app, expr*>             m_app2fresh;
        obj_map<app, proof*>            m_app2pr;
        expr_ref_vector                 m_pinned;
        expr_ref_vector                 m_new_cnstrs;
        proof_ref_vector                m_new_cnstr_prs;
        svector<bin_def>                m_divs, m_idivs, m_mods;
        expr_ref                        m_ipower0, m_rpower0;
        expr_ref                        m_subst;
        proof_ref                       m_subst_pr;
        expr_ref_vector                 m_new_vars;
        ast_mark                        m_unsafe_exprs;
        bool                            m_unsafe_found = false;
        obj_map<app, std::pair<expr*, expr*> > m_sin_cos;

        rw_cfg(purify_arith_simplifier & o):
            m_owner(o),
            m_pinned(o.m),
            m_new_cnstrs(o.m),
            m_new_cnstr_prs(o.m),
            m_ipower0(o.m),
            m_rpower0(o.m),
            m_subst(o.m),
            m_subst_pr(o.m),
            m_new_vars(o.m) {
        }

        ast_manager & m() { return m_owner.m; }
        arith_util & u() { return m_owner.m_util; }
        bool produce_proofs() const { return false; }
        bool complete() const { return m_owner.m_complete; }
        bool elim_root_objs() const { return m_owner.m_elim_root_objs; }
        bool elim_inverses() const { return m_owner.m_elim_inverses; }

        void init_cannot_purify() {
            struct proc {
                rw_cfg& o;
                proc(rw_cfg& o):o(o) {}
                void operator()(app* a) {
                    for (expr* arg : *a) {
                        if (!is_ground(arg)) {
                            auto* f = a->get_decl();
                            o.m_cannot_purify.insert(f);
                            break;
                        }
                    }
                }
                void operator()(expr* ) {}
            };
            expr_fast_mark1 visited;
            proc p(*this);
            for (unsigned i = m_owner.qhead(); i < m_owner.qtail(); ++i) {
                expr* f = m_owner.m_fmls[i].fml();
                for_each_expr_core<proc, expr_fast_mark1, true, true>(p, visited, f);
            }
        }

        void find_unsafe() {
            if (m_unsafe_found) return;
            struct find_unsafe_proc {
                rw_cfg& m_owner;
                find_unsafe_proc(rw_cfg& o) : m_owner(o) {}
                void operator()(app* a) {
                    if (!m_owner.u().is_sin(a) && !m_owner.u().is_cos(a)) {
                        for (unsigned i = 0; i < a->get_num_args(); ++i)
                            m_owner.m_unsafe_exprs.mark(a->get_arg(i), true);
                    }
                }
                void operator()(quantifier *q) {}
                void operator()(var* v) {}
            };
            find_unsafe_proc proc(*this);
            expr_fast_mark1 visited;
            for (unsigned i = m_owner.qhead(); i < m_owner.qtail(); ++i) {
                expr* f = m_owner.m_fmls[i].fml();
                for_each_expr_core<find_unsafe_proc, expr_fast_mark1, true, true>(proc, visited, f);
            }
            m_unsafe_found = true;
        }

        bool convert_basis(expr* theta, expr*& x, expr*& y) {
            if (!is_uninterp_const(theta))
                return false;
            find_unsafe();
            if (m_unsafe_exprs.is_marked(theta))
                return false;
            std::pair<expr*, expr*> pair;
            if (!m_sin_cos.find(to_app(theta), pair)) {
                pair.first  = m().mk_fresh_const(nullptr, u().mk_real());
                pair.second = m().mk_fresh_const(nullptr, u().mk_real());
                m_sin_cos.insert(to_app(theta), pair);
                m_pinned.push_back(pair.first);
                m_pinned.push_back(pair.second);
                m_pinned.push_back(theta);
            }
            x = pair.first;
            y = pair.second;
            return true;
        }

        expr * mk_fresh_var(bool is_int) {
            expr * r = m().mk_fresh_const(nullptr, is_int ? u().mk_int() : u().mk_real());
            m_new_vars.push_back(r);
            return r;
        }

        expr * mk_fresh_real_var() { return mk_fresh_var(false); }
        expr * mk_fresh_int_var()  { return mk_fresh_var(true); }
        expr * mk_int_zero()  { return u().mk_numeral(rational(0), true); }
        expr * mk_real_zero() { return u().mk_numeral(rational(0), false); }
        expr * mk_real_one()  { return u().mk_numeral(rational(1), false); }

        bool already_processed(app * t, expr_ref & result, proof_ref & result_pr) {
            expr * r;
            if (m_app2fresh.find(t, r)) {
                result = r;
                result_pr = nullptr;
                return true;
            }
            return false;
        }

        void mk_def_proof(expr *, expr *, proof_ref & result_pr) {
            result_pr = nullptr;
        }

        void push_cnstr_pr(proof *) {}
        void push_cnstr_pr(proof *, proof *) {}

        void push_cnstr(expr * cnstr) {
            m_new_cnstrs.push_back(cnstr);
            TRACE("purify_arith", tout << mk_pp(cnstr, m()) << "\n";);
        }

        void cache_result(app * t, expr * r, proof * pr) {
            m_app2fresh.insert(t, r);
            m_pinned.push_back(t);
            m_pinned.push_back(r);
        }

        expr * OR(expr * a, expr * b) { return m().mk_or(a, b); }
        expr * AND(expr * a, expr * b) { return m().mk_and(a, b); }
        expr * EQ(expr * a, expr * b)  { return m().mk_eq(a, b); }
        expr * NOT(expr * a)           { return m().mk_not(a); }

        void process_div(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            app_ref t(m());
            t = m().mk_app(f, num, args);
            if (already_processed(t, result, result_pr))
                return;

            expr * k = mk_fresh_real_var();
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);

            expr * x = args[0];
            expr * y = args[1];
            push_cnstr(OR(EQ(y, mk_real_zero()), EQ(u().mk_mul(y, k), x)));
            rational r;
            if (complete()) {
                push_cnstr(OR(NOT(EQ(y, mk_real_zero())), EQ(k, u().mk_div(x, mk_real_zero()))));
            }
            m_divs.push_back(bin_def(x, y, k));
        }

        void process_idiv(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            app_ref div_app(m());
            div_app = m().mk_app(f, num, args);
            if (already_processed(div_app, result, result_pr))
                return;

            expr * k1 = mk_fresh_int_var();
            result = k1;
            mk_def_proof(k1, div_app, result_pr);
            cache_result(div_app, result, result_pr);

            expr * k2 = mk_fresh_int_var();
            app_ref mod_app(m());
            proof_ref mod_pr(m());
            expr * x = args[0];
            expr * y = args[1];
            mod_app = u().mk_mod(x, y);
            mk_def_proof(k2, mod_app, mod_pr);
            cache_result(mod_app, k2, mod_pr);

            m_mods.push_back(bin_def(x, y, k2));

            expr * zero = mk_int_zero();
            push_cnstr(OR(EQ(y, zero), EQ(x, u().mk_add(u().mk_mul(k1, y), k2))));
            push_cnstr(OR(EQ(y, zero), u().mk_le(zero, k2)));
            push_cnstr(OR(u().mk_le(y, zero), u().mk_lt(k2, y)));
            push_cnstr(OR(u().mk_ge(y, zero), u().mk_lt(k2, u().mk_mul(u().mk_numeral(rational(-1), true), y))));

            rational r;
            if (complete() && (!u().is_numeral(y, r) || r.is_zero())) {
                push_cnstr(OR(NOT(EQ(y, zero)), EQ(k1, u().mk_idiv(x, zero))));
                push_cnstr(OR(NOT(EQ(y, zero)), EQ(k2, u().mk_mod(x, zero))));
            }
            m_idivs.push_back(bin_def(x, y, k1));
        }

        void process_mod(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            app_ref t(m());
            t = m().mk_app(f, num, args);
            if (already_processed(t, result, result_pr))
                return;
            process_idiv(f, num, args, result, result_pr);
            VERIFY(already_processed(t, result, result_pr));
        }

        void process_to_int(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            app_ref t(m());
            t = m().mk_app(f, num, args);
            if (already_processed(t, result, result_pr))
                return;

            expr * k = mk_fresh_int_var();
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);

            expr * x = args[0];
            expr * diff = u().mk_add(x, u().mk_mul(u().mk_numeral(rational(-1), false), u().mk_to_real(k)));
            push_cnstr(u().mk_ge(diff, mk_real_zero()));
            push_cnstr(NOT(u().mk_ge(diff, u().mk_numeral(rational(1), false))));
        }

        br_status process_power(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            rational y;
            if (!u().is_numeral(args[1], y))
                return BR_FAILED;
            if (y.is_int() && !y.is_zero())
                return BR_FAILED;
            app_ref t(m());
            t = m().mk_app(f, num, args);
            if (already_processed(t, result, result_pr))
                return BR_DONE;

            expr * x = args[0];
            bool is_int = u().is_int(x);

            expr * k = mk_fresh_var(false);
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);

            expr_ref zero(u().mk_numeral(rational(0), is_int), m());
            expr_ref one(u().mk_numeral(rational(1), is_int), m());
            if (y.is_zero()) {
                expr* p0;
                if (is_int) {
                    if (!m_ipower0) m_ipower0 = mk_fresh_var(false);
                    p0 = m_ipower0;
                }
                else {
                    if (!m_rpower0) m_rpower0 = mk_fresh_var(false);
                    p0 = m_rpower0;
                }
                push_cnstr(OR(EQ(x, zero), EQ(k, one)));
                push_cnstr(OR(NOT(EQ(x, zero)), EQ(k, p0)));
            }
            else if (!is_int) {
                SASSERT(!y.is_int());
                SASSERT(numerator(y).is_one());
                rational n = denominator(y);
                if (!n.is_even()) {
                    push_cnstr(EQ(x, u().mk_power(k, u().mk_numeral(n, false))));
                }
                else {
                    SASSERT(n.is_even());
                    push_cnstr(OR(NOT(u().mk_ge(x, zero)),
                                  AND(EQ(x, u().mk_power(k, u().mk_numeral(n, false))),
                                      u().mk_ge(k, zero))));
                    push_cnstr(OR(u().mk_ge(x, zero),
                                  EQ(k, u().mk_neg_root(x, u().mk_numeral(n, false)))));
                }
            }
            else {
                SASSERT(is_int);
                SASSERT(!y.is_int());
                return BR_FAILED;
            }
            return BR_DONE;
        }

        void process_irrat(app * s, expr_ref & result, proof_ref & result_pr) {
            if (already_processed(s, result, result_pr))
                return;

            expr * k = mk_fresh_real_var();
            result = k;
            mk_def_proof(k, s, result_pr);
            cache_result(s, result, result_pr);

            anum_manager & am = u().am();
            anum const & a = u().to_irrational_algebraic_numeral(s);
            scoped_mpz_vector p(am.qm());
            am.get_polynomial(a, p);
            rational lower, upper;
            am.get_lower(a, lower);
            am.get_upper(a, upper);
            unsigned sz = p.size();
            SASSERT(sz > 2);
            ptr_buffer<expr> args;
            for (unsigned i = 0; i < sz; ++i) {
                if (am.qm().is_zero(p[i]))
                    continue;
                rational coeff = rational(p[i]);
                if (i == 0) {
                    args.push_back(u().mk_numeral(coeff, false));
                }
                else {
                    expr * me;
                    if (i == 1)
                        me = k;
                    else
                        me = u().mk_power(k, u().mk_numeral(rational(i), false));
                    args.push_back(u().mk_mul(u().mk_numeral(coeff, false), me));
                }
            }
            SASSERT(args.size() >= 2);
            push_cnstr(EQ(u().mk_add(args.size(), args.data()), mk_real_zero()));
            push_cnstr(u().mk_lt(u().mk_numeral(lower, false), k));
            push_cnstr(u().mk_lt(k, u().mk_numeral(upper, false)));
        }

        br_status process_sin_cos(bool first, func_decl *f, expr * theta, expr_ref & result, proof_ref & result_pr) {
            expr* x, *y;
            if (convert_basis(theta, x, y)) {
                result = first ? x : y;
                app_ref t(m().mk_app(f, theta), m());
                mk_def_proof(result, t, result_pr);
                cache_result(t, result, result_pr);
                push_cnstr(EQ(mk_real_one(), u().mk_add(u().mk_mul(x, x), u().mk_mul(y, y))));
                return BR_DONE;
            }
            else {
                expr_ref s(u().mk_sin(theta), m());
                expr_ref c(u().mk_cos(theta), m());
                expr_ref axm(EQ(mk_real_one(), u().mk_add(u().mk_mul(s, s), u().mk_mul(c, c))), m());
                push_cnstr(axm);
                return BR_FAILED;
            }
        }

        br_status process_sin(func_decl *f, expr * theta, expr_ref & result, proof_ref & result_pr) {
            return process_sin_cos(true, f, theta, result, result_pr);
        }

        br_status process_cos(func_decl *f, expr * theta, expr_ref & result, proof_ref & result_pr) {
            return process_sin_cos(false, f, theta, result, result_pr);
        }

        br_status process_asin(func_decl * f, expr * x, expr_ref & result, proof_ref & result_pr) {
            if (!elim_inverses())
                return BR_FAILED;
            app_ref t(m());
            t = m().mk_app(f, x);
            if (already_processed(t, result, result_pr))
                return BR_DONE;

            expr * k = mk_fresh_var(false);
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);

            expr * one   = u().mk_numeral(rational(1), false);
            expr * mone  = u().mk_numeral(rational(-1), false);
            expr * pi2   = u().mk_mul(u().mk_numeral(rational(1,2), false), u().mk_pi());
            expr * mpi2  = u().mk_mul(u().mk_numeral(rational(-1,2), false), u().mk_pi());
            push_cnstr(OR(OR(NOT(u().mk_ge(x, mone)), NOT(u().mk_le(x, one))),
                          AND(EQ(x, u().mk_sin(k)),
                              AND(u().mk_ge(k, mpi2), u().mk_le(k, pi2)))));
            if (complete()) {
                push_cnstr(OR(u().mk_ge(x, mone), EQ(k, u().mk_u_asin(x))));
                push_cnstr(OR(u().mk_le(x, one),  EQ(k, u().mk_u_asin(x))));
            }
            return BR_DONE;
        }

        br_status process_acos(func_decl * f, expr * x, expr_ref & result, proof_ref & result_pr) {
            if (!elim_inverses())
                return BR_FAILED;
            app_ref t(m());
            t = m().mk_app(f, x);
            if (already_processed(t, result, result_pr))
                return BR_DONE;

            expr * k = mk_fresh_var(false);
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);

            expr * one   = u().mk_numeral(rational(1), false);
            expr * mone  = u().mk_numeral(rational(-1), false);
            expr * pi    = u().mk_pi();
            expr * zero  = u().mk_numeral(rational(0), false);
            push_cnstr(OR(OR(NOT(u().mk_ge(x, mone)), NOT(u().mk_le(x, one))),
                          AND(EQ(x, u().mk_cos(k)),
                              AND(u().mk_ge(k, zero), u().mk_le(k, pi)))));
            if (complete()) {
                push_cnstr(OR(u().mk_ge(x, mone), EQ(k, u().mk_u_acos(x))));
                push_cnstr(OR(u().mk_le(x, one),  EQ(k, u().mk_u_acos(x))));
            }
            return BR_DONE;
        }

        br_status process_atan(func_decl * f, expr * x, expr_ref & result, proof_ref & result_pr) {
            if (!elim_inverses())
                return BR_FAILED;
            app_ref t(m());
            t = m().mk_app(f, x);
            if (already_processed(t, result, result_pr))
                return BR_DONE;

            expr * k = mk_fresh_var(false);
            result = k;
            mk_def_proof(k, t, result_pr);
            cache_result(t, result, result_pr);

            expr * pi2  = u().mk_mul(u().mk_numeral(rational(1,2), false),  u().mk_pi());
            expr * mpi2 = u().mk_mul(u().mk_numeral(rational(-1,2), false), u().mk_pi());
            push_cnstr(AND(EQ(x, u().mk_tan(k)),
                           AND(u().mk_gt(k, mpi2), u().mk_lt(k, pi2))));
            return BR_DONE;
        }

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            if (f->get_family_id() != u().get_family_id())
                return BR_FAILED;
            if (m_cannot_purify.contains(f))
                return BR_FAILED;
            switch (f->get_decl_kind()) {
            case OP_DIV:
                process_div(f, num, args, result, result_pr);
                return BR_DONE;
            case OP_IDIV:
                if (!m_cannot_purify.empty())
                    return BR_FAILED;
                process_idiv(f, num, args, result, result_pr);
                return BR_DONE;
            case OP_MOD:
                if (!m_cannot_purify.empty())
                    return BR_FAILED;
                process_mod(f, num, args, result, result_pr);
                return BR_DONE;
            case OP_TO_INT:
                process_to_int(f, num, args, result, result_pr);
                return BR_DONE;
            case OP_POWER:
                return process_power(f, num, args, result, result_pr);
            case OP_ASIN:
                return process_asin(f, args[0], result, result_pr);
            case OP_ACOS:
                return process_acos(f, args[0], result, result_pr);
            case OP_SIN:
                return process_sin(f, args[0], result, result_pr);
            case OP_COS:
                return process_cos(f, args[0], result, result_pr);
            case OP_ATAN:
                return process_atan(f, args[0], result, result_pr);
            default:
                return BR_FAILED;
            }
        }

        bool get_subst(expr * s, expr * & t, proof * & t_pr) {
            if (is_quantifier(s)) {
                process_quantifier(to_quantifier(s), m_subst, m_subst_pr);
                t    = m_subst.get();
                t_pr = m_subst_pr.get();
                return true;
            }
            else if (u().is_irrational_algebraic_numeral(s) && elim_root_objs()) {
                process_irrat(to_app(s), m_subst, m_subst_pr);
                t    = m_subst.get();
                t_pr = m_subst_pr.get();
                return true;
            }
            return false;
        }

        struct rw_rec : public rewriter_tpl<rw_cfg> {
            rw_cfg& m_cfg;
            rw_rec(rw_cfg& cfg):
                rewriter_tpl<rw_cfg>(cfg.m(), cfg.produce_proofs(), cfg),
                m_cfg(cfg) {
            }
        };

        void process_quantifier(quantifier * q, expr_ref & result, proof_ref & result_pr) {
            result_pr = nullptr;
            rw_rec r(*this);
            expr_ref new_body(m());
            proof_ref new_body_pr(m());
            r(q->get_expr(), new_body, new_body_pr);
            TRACE("purify_arith",
                  tout << "body: " << mk_ismt2_pp(q->get_expr(), m()) << "\nnew_body: " << new_body << "\n";);
            result = m().update_quantifier(q, new_body);
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(purify_arith_simplifier & o):
            rewriter_tpl<rw_cfg>(o.m, false, m_cfg),
            m_cfg(o) {
            m_cfg.init_cannot_purify();
        }
    };

public:
    purify_arith_simplifier(ast_manager & m, params_ref const & p, dependent_expr_state & s):
        dependent_expr_simplifier(m, s),
        m_util(m) {
        updt_params(p);
    }

    char const* name() const override { return "purify-arith"; }

    void updt_params(params_ref const & p) override {
        m_elim_root_objs = p.get_bool("elim_root_objects", true);
        m_elim_inverses  = p.get_bool("elim_inverses", true);
        m_complete       = p.get_bool("complete", true);
    }

    void collect_param_descrs(param_descrs & r) override {
        r.insert("complete", CPK_BOOL,
                 "add constraints to make sure that any interpretation of an underspecified arithmetic operators is a function. The result will include additional uninterpreted functions/constants: /0, div0, mod0, 0^0, neg-root", "true");
        r.insert("elim_root_objects", CPK_BOOL,
                 "eliminate root objects.", "true");
        r.insert("elim_inverses", CPK_BOOL,
                 "eliminate inverse trigonometric functions (asin, acos, atan).", "true");
    }

    void reduce() override {
        rw r(*this);

        expr_ref   new_curr(m);
        proof_ref  new_pr(m);

        // Rewrite each formula in the window.
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            r(d.fml(), new_curr, new_pr);
            if (new_curr != d.fml())
                m_fmls.update(idx, dependent_expr(m, new_curr, nullptr, d.dep()));
        }

        // Add new constraints collected during rewriting.
        for (expr* c : r.m_cfg.m_new_cnstrs)
            m_fmls.add(dependent_expr(m, c, nullptr, nullptr));

        auto const& divs  = r.m_cfg.m_divs;
        auto const& idivs = r.m_cfg.m_idivs;
        auto const& mods  = r.m_cfg.m_mods;

        // Add consistency constraints between multiple div / mod / idiv occurrences
        // that share the same arguments (but may have been introduced independently).
        for (unsigned i = 0; i < divs.size(); ++i) {
            auto const& p1 = divs[i];
            for (unsigned j = i + 1; j < divs.size(); ++j) {
                auto const& p2 = divs[j];
                m_fmls.add(dependent_expr(m,
                    m.mk_implies(m.mk_and(m.mk_eq(p1.x, p2.x), m.mk_eq(p1.y, p2.y)),
                                 m.mk_eq(p1.d, p2.d)), nullptr, nullptr));
            }
        }
        for (unsigned i = 0; i < mods.size(); ++i) {
            auto const& p1 = mods[i];
            for (unsigned j = i + 1; j < mods.size(); ++j) {
                auto const& p2 = mods[j];
                m_fmls.add(dependent_expr(m,
                    m.mk_implies(m.mk_and(m.mk_eq(p1.x, p2.x), m.mk_eq(p1.y, p2.y)),
                                 m.mk_eq(p1.d, p2.d)), nullptr, nullptr));
            }
        }
        for (unsigned i = 0; i < idivs.size(); ++i) {
            auto const& p1 = idivs[i];
            for (unsigned j = i + 1; j < idivs.size(); ++j) {
                auto const& p2 = idivs[j];
                m_fmls.add(dependent_expr(m,
                    m.mk_implies(m.mk_and(m.mk_eq(p1.x, p2.x), m.mk_eq(p1.y, p2.y)),
                                 m.mk_eq(p1.d, p2.d)), nullptr, nullptr));
            }
        }

        // Register fresh variables for model reconstruction (hide them so the model
        // reconstructor will assign them arbitrary values and model completion will
        // use the original expressions).
        obj_map<app, expr*> & f2v = r.m_cfg.m_app2fresh;
        for (auto const& kv : f2v) {
            app * v = to_app(kv.m_value);
            SASSERT(is_uninterp_const(v));
            m_fmls.model_trail().hide(v->get_decl());
        }

        // Provide explicit definitions for under-specified operations so that
        // models produced by the back-end can be lifted back to the original vocabulary.
        if (!divs.empty()) {
            expr_ref body(u().mk_real(0), m);
            expr_ref v0(m.mk_var(0, u().mk_real()), m);
            expr_ref v1(m.mk_var(1, u().mk_real()), m);
            for (auto const& p : divs)
                body = m.mk_ite(m.mk_and(m.mk_eq(v0, p.x), m.mk_eq(v1, p.y)), p.d, body);
            m_fmls.model_trail().push(u().mk_div0(), body, nullptr, {});
        }
        if (!mods.empty()) {
            expr_ref body(u().mk_int(0), m);
            expr_ref v0(m.mk_var(0, u().mk_int()), m);
            expr_ref v1(m.mk_var(1, u().mk_int()), m);
            for (auto const& p : mods)
                body = m.mk_ite(m.mk_and(m.mk_eq(v0, p.x), m.mk_eq(v1, p.y)), p.d, body);
            m_fmls.model_trail().push(u().mk_mod0(), body, nullptr, {});
            body = m.mk_ite(u().mk_ge(v1, u().mk_int(0)), body, u().mk_uminus(body));
            m_fmls.model_trail().push(u().mk_rem0(), body, nullptr, {});
        }
        if (!idivs.empty()) {
            expr_ref body(u().mk_int(0), m);
            expr_ref v0(m.mk_var(0, u().mk_int()), m);
            expr_ref v1(m.mk_var(1, u().mk_int()), m);
            for (auto const& p : idivs)
                body = m.mk_ite(m.mk_and(m.mk_eq(v0, p.x), m.mk_eq(v1, p.y)), p.d, body);
            m_fmls.model_trail().push(u().mk_idiv0(), body, nullptr, {});
        }
        if (r.m_cfg.m_ipower0) {
            m_fmls.model_trail().push(u().mk_ipower0(), r.m_cfg.m_ipower0, nullptr, {});
        }
        if (r.m_cfg.m_rpower0) {
            m_fmls.model_trail().push(u().mk_rpower0(), r.m_cfg.m_rpower0, nullptr, {});
        }
        if (!r.m_cfg.m_sin_cos.empty()) {
            expr_ref zero(u().mk_numeral(rational(0), false), m);
            for (auto const& kv : r.m_cfg.m_sin_cos) {
                expr* x_val = kv.m_value.first;
                expr* y_val = kv.m_value.second;
                // theta = atan2(x, y) or similar; use acos/pi reconstruction as in original tactic
                expr_ref def(m.mk_ite(u().mk_ge(x_val, zero),
                                      u().mk_acos(y_val),
                                      u().mk_add(u().mk_acos(u().mk_uminus(y_val)), u().mk_pi())), m);
                m_fmls.model_trail().push(kv.m_key->get_decl(), def, nullptr, {});
            }
        }
    }
};

/*
  ADD_SIMPLIFIER("purify-arith", "eliminate unnecessary operators: -, /, div, mod, rem, is-int, to-int, ^, root-objects.", "alloc(purify_arith_simplifier, m, p, s)")
*/
