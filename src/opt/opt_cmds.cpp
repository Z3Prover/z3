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

    ~assert_soft_cmd() override {
    }

    void reset(cmd_context & ctx) override {
        m_idx = 0; 
        m_formula = nullptr;
    }

    char const * get_usage() const override { return "<formula> [:weight <rational-weight>] [:id <symbol>]"; }
    char const * get_main_descr() const override { return "assert soft constraint with optional weight and identifier"; }

    // command invocation
    void prepare(cmd_context & ctx) override {
        reset(ctx);
    }

    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override {
        if (m_idx == 0) return CPK_EXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }

    void init_pdescrs(cmd_context & ctx, param_descrs & p) override {
        p.insert("weight", CPK_NUMERAL, "(default: 1) penalty of not satisfying constraint.");
        p.insert("id", CPK_SYMBOL, "(default: null) partition identifier for soft constraints.");
    }

    void set_next_arg(cmd_context & ctx, expr * t) override {
        SASSERT(m_idx == 0);
        if (!ctx.m().is_bool(t)) {
            throw cmd_exception("Invalid type for expression. Expected Boolean type.");
        }
        m_formula = t;
        ++m_idx;
    }

    void failure_cleanup(cmd_context & ctx) override {
        reset(ctx);
    }

    void execute(cmd_context & ctx) override {
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

    void finalize(cmd_context & ctx) override {
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

    void reset(cmd_context & ctx) override { }
    char const * get_usage() const override { return "<term>"; }
    char const * get_descr(cmd_context & ctx) const override { return "check sat modulo objective function";}
    unsigned get_arity() const override { return 1; }
    void prepare(cmd_context & ctx) override {}
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override { return CPK_EXPR; }

    void set_next_arg(cmd_context & ctx, expr * t) override {
        if (!is_app(t)) {
            throw cmd_exception("malformed objective term: it cannot be a quantifier or bound variable");
        }
        get_opt(ctx, m_opt).add_objective(to_app(t), m_is_max);
        ctx.print_success();
    }

    void failure_cleanup(cmd_context & ctx) override {
        reset(ctx);
    }

    void execute(cmd_context & ctx) override {
    }
};

class get_objectives_cmd : public cmd {
    opt::context* m_opt;
public:
    get_objectives_cmd(opt::context* opt):
        cmd("get-objectives"),
        m_opt(opt)
    {}
    
    void reset(cmd_context & ctx) override { }
    char const * get_usage() const override { return "(get-objectives)"; }
    char const * get_descr(cmd_context & ctx) const override { return "retrieve the objective values (after optimization)"; }
    unsigned get_arity() const override { return 0; }
    void prepare(cmd_context & ctx) override {}


    void failure_cleanup(cmd_context & ctx) override {
        reset(ctx);
    }

    void execute(cmd_context & ctx) override {
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


