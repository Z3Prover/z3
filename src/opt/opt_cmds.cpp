/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_cmds.cpp

Abstract:
    Commands for optimization benchmarks

Author:

    Anh-Dung Phan (t-anphan) 2013-10-14

Notes:

    TODO:
    - integrate with parameters. 
      Parameter infrastructure lets us control setttings, such as 
      timeouts and control which backend optimization approach to 
      use during experiments.

    - Display statistics properly on exit when configured to do so.
      Also add appropriate statistics tracking to opt::context

    - Deal with push/pop (later)

    - Revisit weighted constraints if we want to group them using identifiers.

--*/
#include "opt_cmds.h"
#include "cmd_context.h"
#include "ast_pp.h"
#include "opt_context.h"
#include "cancel_eh.h"
#include "scoped_ctrl_c.h"


class opt_context {
    cmd_context& ctx;
    scoped_ptr<opt::context> m_opt;
public:
    opt_context(cmd_context& ctx): ctx(ctx) {}
    opt::context& operator()() { 
        if (!m_opt) {
            m_opt = alloc(opt::context, ctx.m());
        }
        return *m_opt;
    }
};


class assert_weighted_cmd : public cmd {
    opt_context& m_opt_ctx;
    unsigned     m_idx;
    expr*        m_formula;
    rational     m_weight;

public:
    assert_weighted_cmd(cmd_context& ctx, opt_context& opt_ctx):
        cmd("assert-weighted"),
        m_opt_ctx(opt_ctx),
        m_idx(0),
        m_formula(0),
        m_weight(0)
    {}

    virtual ~assert_weighted_cmd() {
        dealloc(&m_opt_ctx);
    }

    virtual void reset(cmd_context & ctx) { 
        if (m_formula) {
            ctx.m().dec_ref(m_formula);
        }
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
        ctx.m().inc_ref(t);
        ++m_idx;
    }

    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual void execute(cmd_context & ctx) {
        m_opt_ctx().add_soft_constraint(m_formula, m_weight);
        reset(ctx);
    }

    virtual void finalize(cmd_context & ctx) { 
    }

};

class min_maximize_cmd : public cmd {
    bool         m_is_max;
    opt_context& m_opt_ctx;

public:
    min_maximize_cmd(cmd_context& ctx, opt_context& opt_ctx, bool is_max):
        cmd(is_max?"maximize":"minimize"),
        m_is_max(is_max),
        m_opt_ctx(opt_ctx)
    {}

    virtual void reset(cmd_context & ctx) { }

    virtual char const * get_usage() const { return "<term>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "check sat modulo objective function";}
    virtual unsigned get_arity() const { return 1; }

    virtual void prepare(cmd_context & ctx) {}
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_EXPR; }

    virtual void set_next_arg(cmd_context & ctx, expr * t) {
        m_opt_ctx().add_objective(t, m_is_max);
    }

    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual void execute(cmd_context & ctx) {
    }
};

class optimize_cmd : public cmd {
    opt_context& m_opt_ctx;
public:
    optimize_cmd(opt_context& opt_ctx):
        cmd("optimize"),
        m_opt_ctx(opt_ctx)
    {}
    virtual char const * get_descr(cmd_context & ctx) const { return "check sat modulo objective function";}
    virtual unsigned get_arity() const { return 0; }
    virtual void prepare(cmd_context & ctx) {}
    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual void execute(cmd_context & ctx) {
        opt::context& opt = m_opt_ctx();
        ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
        ptr_vector<expr>::const_iterator end = ctx.end_assertions();
        for (; it != end; ++it) {
            opt.add_hard_constraint(*it);
        }
        cancel_eh<opt::context> eh(opt);
        {
            scoped_ctrl_c ctrlc(eh);
            cmd_context::scoped_watch sw(ctx);
            try {
                opt.optimize();
            }
            catch (z3_error& ex) {
                ctx.regular_stream() << "(error: " << ex.msg() << "\")" << std::endl;
            }
            catch (z3_exception& ex) {
                ctx.regular_stream() << "(error: " << ex.msg() << "\")" << std::endl;
            }
        }
    }
};

void install_opt_cmds(cmd_context & ctx) {
    opt_context* opt_ctx = alloc(opt_context, ctx);
    ctx.insert(alloc(assert_weighted_cmd, ctx, *opt_ctx));
    ctx.insert(alloc(min_maximize_cmd, ctx, *opt_ctx, true));
    ctx.insert(alloc(min_maximize_cmd, ctx, *opt_ctx, false));
    ctx.insert(alloc(optimize_cmd, *opt_ctx));
}
