/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    polynomial_cmds.cpp

Abstract:
    Commands for debugging polynomial module.

Author:

    Leonardo (leonardo) 2011-12-23

Notes:

--*/
#include<sstream>
#include"cmd_context.h"
#include"cmd_util.h"
#include"scoped_timer.h"
#include"scoped_ctrl_c.h"
#include"cancel_eh.h"
#include"ast_smt2_pp.h"
#include"expr2polynomial.h"
#include"parametric_cmd.h"
#include"mpq.h"
#include"algebraic_numbers.h"
#include"polynomial_var2value.h"
#include"expr2var.h"
#include"pp.h"
#include"pp_params.hpp"

static void to_poly(cmd_context & ctx, expr * t) {
    polynomial::numeral_manager nm;
    polynomial::manager pm(nm);
    default_expr2polynomial expr2poly(ctx.m(), pm);
    polynomial::polynomial_ref p(pm);
    polynomial::scoped_numeral d(nm);
    if (!expr2poly.to_polynomial(t, p, d)) {
        throw cmd_exception("expression is not a polynomial");
    }
    expr_ref r(ctx.m());
    expr2poly.to_expr(p, true, r);
    if (!nm.is_one(d))
        ctx.regular_stream() << "(* " << nm.to_string(d) << " ";
    ctx.display(ctx.regular_stream(), r);
    if (!nm.is_one(d))
        ctx.regular_stream() << ")";
    ctx.regular_stream() << std::endl;
}

static void factor(cmd_context & ctx, expr * t, polynomial::factor_params const & ps) {
    polynomial::numeral_manager nm;
    polynomial::manager pm(nm);
    default_expr2polynomial expr2poly(ctx.m(), pm);
    polynomial::polynomial_ref p(pm);
    polynomial::scoped_numeral d(nm);
    if (!expr2poly.to_polynomial(t, p, d)) {
        throw cmd_exception("expression is not a polynomial");
    }
    polynomial::factors fs(pm);
    factor(p, fs, ps);
    ctx.regular_stream() << "(factors";
    rational f0(fs.get_constant());
    f0 = f0 / rational(d);
    ctx.regular_stream() << std::endl << f0;
    unsigned num_factors = fs.distinct_factors();
    expr_ref f(ctx.m());
    for (unsigned i = 0; i < num_factors; i++) {
        ctx.regular_stream() << std::endl;
        if (fs.get_degree(i) > 1)
            ctx.regular_stream() << "(^ ";
        expr2poly.to_expr(fs[i], true, f);
        ctx.display(ctx.regular_stream(), f);
        if (fs.get_degree(i) > 1)
            ctx.regular_stream() << " " << fs.get_degree(i) << ")";
    }
    ctx.regular_stream() << ")" << std::endl;
}


class poly_isolate_roots_cmd : public cmd {
    struct context {
        arith_util                  m_util;
        unsynch_mpq_manager         m_qm;
        polynomial::manager         m_pm;
        algebraic_numbers::manager  m_am;
        polynomial_ref              m_p;
        default_expr2polynomial     m_expr2poly;
        polynomial::var             m_var;
        typedef polynomial::simple_var2value<algebraic_numbers::manager> x2v;
        x2v                         m_x2v;
        
        context(ast_manager & m):
            m_util(m),
            m_pm(m_qm),
            m_am(m_qm),
            m_p(m_pm),
            m_expr2poly(m, m_pm),
            m_var(polynomial::null_var),
            m_x2v(m_am) {
        }

        void set_next_arg(cmd_context & ctx, expr * arg) {
            if (m_p.get() == 0) {
                scoped_mpz d(m_qm);
                if (!m_expr2poly.to_polynomial(arg, m_p, d))
                    throw cmd_exception("expression is not a polynomial");
            }
            else if (m_var == polynomial::null_var) {
                if (!m_expr2poly.is_var(arg))
                    throw cmd_exception("invalid assignment, argument is not a variable in the given polynomial");
                m_var = m_expr2poly.get_mapping().to_var(arg);
            }
            else {
                rational k;
                scoped_anum v(m_am);
                if (m_util.is_numeral(arg, k)) {
                    m_am.set(v, k.to_mpq());
                }
                else if (m_util.is_irrational_algebraic_numeral(arg)) {
                    m_am.set(v, m_util.to_irrational_algebraic_numeral(arg));
                }
                else {
                    throw cmd_exception("invalid assignment, argument is not a value");
                }
                m_x2v.push_back(m_var, v);
                m_var = polynomial::null_var;
            }
        }

        void execute(cmd_context & ctx) {
            if (m_p.get() == 0)
                throw cmd_exception("polynomial expected");
            polynomial::var_vector xs;
            m_pm.vars(m_p, xs);
            unsigned num_assigned = 0;
            for (unsigned i = 0; i < xs.size(); i++) {
                if (m_x2v.contains(xs[i]))
                    num_assigned++;
            }
            if (num_assigned != xs.size() && num_assigned + 1 != xs.size())
                throw cmd_exception("given assignment is not sufficient to make the given polynomial univariate");
            scoped_anum_vector rs(m_am);
            m_am.isolate_roots(m_p, m_x2v, rs);
            ctx.regular_stream() << "(roots";
            pp_params params;
            bool pp_decimal = params.decimal();
            for (unsigned i = 0; i < rs.size(); i++) {
                ctx.regular_stream() << std::endl;
                if (!pp_decimal)
                    m_am.display_root_smt2(ctx.regular_stream(), rs[i]);
                else
                    m_am.display_decimal(ctx.regular_stream(), rs[i]);
            }
            ctx.regular_stream() << ")" << std::endl;
        }
    };

    scoped_ptr<context> m_ctx;
    
public:
    poly_isolate_roots_cmd(char const * name = "poly/isolate-roots"):cmd(name), m_ctx(0) {}

    virtual char const * get_usage() const { return "<term> (<term> <value>)*"; }

    virtual char const * get_descr(cmd_context & ctx) const { return "isolate the roots a multivariate polynomial modulo an assignment"; }
    
    virtual unsigned get_arity() const { return VAR_ARITY; }

    virtual void prepare(cmd_context & ctx) { 
        m_ctx = alloc(context, ctx.m());
    }

    virtual void finalize(cmd_context & ctx) {
        m_ctx = 0;
    }

    virtual void failure_cleanup(cmd_context & ctx) {
        m_ctx = 0;
    }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        return CPK_EXPR;
    }
    
    virtual void set_next_arg(cmd_context & ctx, expr * arg) {
        m_ctx->set_next_arg(ctx, arg);
    }

    virtual void execute(cmd_context & ctx) {
        m_ctx->execute(ctx);
        m_ctx = 0;
    }
};


UNARY_CMD(to_poly_cmd, "to-poly", "<term>", "convert expression into sum-of-monomials form", CPK_EXPR, expr *, to_poly(ctx, arg););

class poly_factor_cmd : public parametric_cmd {
    expr *                   m_target;
public:
    poly_factor_cmd(char const * name = "poly/factor"):parametric_cmd(name) {}

    virtual char const * get_usage() const { return "<term> (<keyword> <value>)*"; }

    virtual char const * get_main_descr() const { 
        return "factor a polynomial";
    }
    
    virtual void init_pdescrs(cmd_context & ctx, param_descrs & p) {
        polynomial::factor_params::get_param_descrs(p);
    }
    
    virtual void prepare(cmd_context & ctx) { 
        parametric_cmd::prepare(ctx);
        m_target   = 0; 
    }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        if (m_target == 0) return CPK_EXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }
    
    virtual void set_next_arg(cmd_context & ctx, expr * arg) {
        m_target = arg;
    }
    
    virtual void execute(cmd_context & ctx) {
        polynomial::factor_params ps;
        ps.updt_params(m_params);
        factor(ctx, m_target, ps);
    }
};

void install_polynomial_cmds(cmd_context & ctx) {
#ifndef _EXTERNAL_RELEASE
    ctx.insert(alloc(to_poly_cmd));
    ctx.insert(alloc(poly_factor_cmd));
    ctx.insert(alloc(poly_isolate_roots_cmd));
#endif
}
