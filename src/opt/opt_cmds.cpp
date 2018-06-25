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

    - Add appropriate statistics tracking to opt::context

    - Deal with push/pop (later)

--*/
#include "opt/opt_cmds.h"
#include "cmd_context/cmd_context.h"
#include "ast/ast_pp.h"
#include "opt/opt_context.h"
#include "util/cancel_eh.h"
#include "util/scoped_ctrl_c.h"
#include "util/scoped_timer.h"
#include "cmd_context/parametric_cmd.h"
#include "opt/opt_params.hpp"
#include "model/model_smt2_pp.h"

static opt::context& get_opt(cmd_context& cmd, opt::context* opt) {
    if (opt) {
        return *opt;
    }
    if (!cmd.get_opt()) {
        cmd.set_opt(alloc(opt::context, cmd.m()));
    }
    return dynamic_cast<opt::context&>(*cmd.get_opt());
}


class assert_soft_cmd : public parametric_cmd {
    unsigned     m_idx;
    expr*        m_formula;
    opt::context* m_opt;

public:
    assert_soft_cmd(opt::context* opt):
        parametric_cmd("assert-soft"),
        m_idx(0),
        m_formula(nullptr),
        m_opt(opt)
    {}

    virtual ~assert_soft_cmd() {
    }

    virtual void reset(cmd_context & ctx) { 
        m_idx = 0; 
        m_formula = nullptr;
    }

    virtual char const * get_usage() const { return "<formula> [:weight <rational-weight>] [:id <symbol>]"; }
    virtual char const * get_main_descr() const { return "assert soft constraint with optional weight and identifier"; }

    // command invocation
    virtual void prepare(cmd_context & ctx) {
        reset(ctx);
    }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { 
        if (m_idx == 0) return CPK_EXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }

    virtual void init_pdescrs(cmd_context & ctx, param_descrs & p) {
        p.insert("weight", CPK_NUMERAL, "(default: 1) penalty of not satisfying constraint.");
        p.insert("id", CPK_SYMBOL, "(default: null) partition identifier for soft constraints.");
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
        if (!m_formula) {
            throw cmd_exception("assert-soft requires a formulas as argument.");
        }
        symbol w("weight");
        rational weight = ps().get_rat(symbol("weight"), rational::one());
        symbol id = ps().get_sym(symbol("id"), symbol::null);        
        get_opt(ctx, m_opt).add_soft_constraint(m_formula, weight, id);
        ctx.print_success();
        reset(ctx);
    }

    virtual void finalize(cmd_context & ctx) { 
    }

};

class min_maximize_cmd : public cmd {
    bool         m_is_max;
    opt::context* m_opt;

public:
    min_maximize_cmd(bool is_max, opt::context* opt):
        cmd(is_max?"maximize":"minimize"),
        m_is_max(is_max),
        m_opt(opt)
    {}

    virtual void reset(cmd_context & ctx) { }
    virtual char const * get_usage() const { return "<term>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "check sat modulo objective function";}
    virtual unsigned get_arity() const { return 1; }
    virtual void prepare(cmd_context & ctx) {}
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_EXPR; }

    virtual void set_next_arg(cmd_context & ctx, expr * t) {
        if (!is_app(t)) {
            throw cmd_exception("malformed objective term: it cannot be a quantifier or bound variable");
        }
        get_opt(ctx, m_opt).add_objective(to_app(t), m_is_max);
        ctx.print_success();
    }

    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual void execute(cmd_context & ctx) {
    }
};

class get_objectives_cmd : public cmd {
    opt::context* m_opt;
public:
    get_objectives_cmd(opt::context* opt):
        cmd("get-objectives"),
        m_opt(opt)
    {}
    
    virtual void reset(cmd_context & ctx) { }
    virtual char const * get_usage() const { return "(get-objectives)"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "retrieve the objective values (after optimization)"; }
    virtual unsigned get_arity() const { return 0; }
    virtual void prepare(cmd_context & ctx) {}


    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual void execute(cmd_context & ctx) {
        if (!ctx.ignore_check()) {
            get_opt(ctx, m_opt).display_assignment(ctx.regular_stream());        
        }
    }
};

void install_opt_cmds(cmd_context & ctx, opt::context* opt) {
    ctx.insert(alloc(assert_soft_cmd, opt));
    ctx.insert(alloc(min_maximize_cmd, true, opt));
    ctx.insert(alloc(min_maximize_cmd, false, opt));
    ctx.insert(alloc(get_objectives_cmd, opt));
}


