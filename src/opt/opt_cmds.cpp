/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_cmds.cpp

Abstract:
    Commands for optimization benchmarks

Author:

    Anh-Dung Phan (t-anphan) 2013-10-14

Notes:

--*/
#include "opt_cmds.h"
#include "cmd_context.h"
#include "ast_pp.h"
#include "smt_solver.h"
#include "fu_malik.h"

class opt_context {
    ast_manager& m;
    expr_ref_vector m_formulas;
    vector<rational> m_weights;

public:
    opt_context(ast_manager& m):
        m(m),
        m_formulas(m)        
    {}

    void add_formula(expr* f, rational const& w) {
        m_formulas.push_back(f);
        m_weights.push_back(w);
    }
        
    expr_ref_vector const & formulas() const { return m_formulas; }
    vector<rational> const& weights() const { return m_weights; }
};

class assert_weighted_cmd : public cmd {
    opt_context* m_opt_ctx;
    unsigned   m_idx;
    expr_ref   m_formula;
    rational   m_weight;

public:
    assert_weighted_cmd(cmd_context& ctx, opt_context* opt_ctx):
        cmd("assert-weighted"),
        m_opt_ctx(opt_ctx),
        m_idx(0),
        m_formula(ctx.m()),
        m_weight(0)
    {}

    virtual ~assert_weighted_cmd() {
        dealloc(m_opt_ctx);
    }

    virtual void reset(cmd_context & ctx) { 
        m_idx = 0; 
        m_formula = 0;
    }

    virtual char const * get_usage() const { return "<formula> <rational-weight>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "assert soft constraint with weight"; }
    virtual unsigned get_arity() const { return 2; }

    // command invocation
    virtual void prepare(cmd_context & ctx) {}
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { if (m_idx == 0) return CPK_EXPR; return CPK_NUMERAL; }
    virtual void set_next_arg(cmd_context & ctx, rational const & val) { 
        SASSERT(m_idx == 1);
        if (!val.is_pos()) {
            throw cmd_exception("Invalid weight. Weights must be positive.");
        }
        m_weight = val;
        ++m_idx;
    }

    virtual void set_next_arg(cmd_context & ctx, expr * t) {
        SASSERT(m_idx == 0);
        if (!ctx.m().is_bool(t)) {
            throw cmd_exception("Invalid type for expression. Expected Boolean type.");
        }
        m_formula = t;
        ++m_idx;
    }

    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual void execute(cmd_context & ctx) {
        m_opt_ctx->add_formula(m_formula, m_weight);
        reset(ctx);
    }

    virtual void finalize(cmd_context & ctx) { 
        std::cout << "FINALIZE\n";
    }

};

// what amounts to check-sat, but uses the *single* objective function.
// alternative is to register multiple objective functions using
// minimize/maximize and then use check-sat or some variant of it 
// to do the feasibility check.
class min_maximize_cmd : public cmd {
    bool m_is_max;
    expr_ref m_term;
    opt_context* m_opt_ctx;

public:
    min_maximize_cmd(cmd_context& ctx, opt_context* opt_ctx, bool is_max):
        cmd(is_max?"maximize":"minimize"),
        m_is_max(is_max),
        m_term(ctx.m()),
        m_opt_ctx(opt_ctx)
    {}

    virtual void reset(cmd_context & ctx) { 
        m_term = 0;
    }

    virtual char const * get_usage() const { return "<term>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "check sat modulo objective function";}
    virtual unsigned get_arity() const { return 1; }

    virtual void prepare(cmd_context & ctx) {}
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_EXPR; }

    virtual void set_next_arg(cmd_context & ctx, expr * t) {
        m_term = t;
    }

    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual void execute(cmd_context & ctx) {
        ast_manager& m = m_term.get_manager();
        std::cout << "TODO: " << mk_pp(m_term, ctx.m()) << "\n";
        // Here is how to retrieve the soft constraints
        expr_ref_vector const& fmls = m_opt_ctx->formulas();
        vector<rational> const& ws  = m_opt_ctx->weights();

        // TODO: move most functionaltiy to separate module, because it is going to grow..
        ref<solver> s;
        symbol logic;
        params_ref p;
        p.set_bool("model", true);
        p.set_bool("unsat_core", true);        
        s = mk_smt_solver(m, p, logic);

        ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
        ptr_vector<expr>::const_iterator end = ctx.end_assertions();
        for (; it != end; ++it) {
            s->assert_expr(*it);
        }
        expr_ref_vector fmls_copy(fmls);
        if (is_maxsat_problem(ws)) {
            lbool is_sat = opt::fu_malik_maxsat(*s, fmls_copy);
            std::cout << "is-sat: " << is_sat << "\n";
            if (is_sat == l_true) {
                for (unsigned i = 0; i < fmls_copy.size(); ++i) {
                    std::cout << mk_pp(fmls_copy[i].get(), m) << "\n";
                }
            }
        }
        else {
            NOT_IMPLEMENTED_YET();
        }

        // handle optimization criterion.        
    }

private:

    bool is_maxsat_problem(vector<rational> const& ws) const {
        for (unsigned i = 0; i < ws.size(); ++i) {
            if (!ws[i].is_one()) {
                return false;
            }
        }
        return true;
    }

};

void install_opt_cmds(cmd_context & ctx) {
    opt_context* opt_ctx = alloc(opt_context, ctx.m());
    ctx.insert(alloc(assert_weighted_cmd, ctx, opt_ctx));
    ctx.insert(alloc(min_maximize_cmd, ctx, opt_ctx, true));
    ctx.insert(alloc(min_maximize_cmd, ctx, opt_ctx, false));
}
