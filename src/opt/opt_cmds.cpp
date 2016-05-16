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
#include "opt_cmds.h"
#include "cmd_context.h"
#include "ast_pp.h"
#include "opt_context.h"
#include "cancel_eh.h"
#include "scoped_ctrl_c.h"
#include "scoped_timer.h"
#include "parametric_cmd.h"
#include "opt_params.hpp"
#include "model_smt2_pp.h"

static opt::context& get_opt(cmd_context& cmd) {
    if (!cmd.get_opt()) {
        cmd.set_opt(alloc(opt::context, cmd.m()));
    }
    return dynamic_cast<opt::context&>(*cmd.get_opt());
}


class assert_soft_cmd : public parametric_cmd {
    unsigned     m_idx;
    expr*        m_formula;

public:
    assert_soft_cmd():
        parametric_cmd("assert-soft"),
        m_idx(0),
        m_formula(0)
    {}

    virtual ~assert_soft_cmd() {
    }

    virtual void reset(cmd_context & ctx) { 
        m_idx = 0; 
        m_formula = 0;
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
        symbol w("weight");
        rational weight = ps().get_rat(symbol("weight"), rational(0));
        if (weight.is_zero()) {
            weight = rational::one();
        }
        symbol id = ps().get_sym(symbol("id"), symbol::null);
        get_opt(ctx).add_soft_constraint(m_formula, weight, id);
        reset(ctx);
    }

    virtual void finalize(cmd_context & ctx) { 
    }

};

class min_maximize_cmd : public cmd {
    bool         m_is_max;

public:
    min_maximize_cmd(bool is_max):
        cmd(is_max?"maximize":"minimize"),
        m_is_max(is_max)
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
        get_opt(ctx).add_objective(to_app(t), m_is_max);
    }

    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual void execute(cmd_context & ctx) {
    }
};

class alternate_min_max_cmd : public cmd {
    app_ref_vector*      m_vars;
    svector<bool>        m_is_max;
    unsigned             m_position;

    app_ref_vector& vars(cmd_context& ctx) {
        if (!m_vars) {
            m_vars = alloc(app_ref_vector, ctx.m());
        }
        return *m_vars;
    }
public:
    alternate_min_max_cmd():
        cmd("min-max"),
        m_vars(0),
        m_position(0)
    {}
    
    virtual void reset(cmd_context & ctx) { 
        dealloc(m_vars);
        m_vars = 0;
        m_is_max.reset();
        m_position = 0;
    }
    virtual char const * get_usage() const { return "(min | max | var)+ <term>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "check sat modulo alternating min-max objectives";}
    virtual unsigned get_arity() const { return 2; }
    virtual void prepare(cmd_context & ctx) {}
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        switch (m_position) {
        case 0: return CPK_SYMBOL_LIST;
        case 1: return CPK_EXPR;
        default: return CPK_SYMBOL;
        }
    }

    virtual void set_next_arg(cmd_context & ctx, unsigned num, symbol const * slist) {
        bool is_max = false;
        for (unsigned i = 0; i < num; ++i) {
            if (slist[i] == symbol("max")) {
                is_max = true;
            }
            else if (slist[i] == symbol("min")) {
                is_max = false;
            }
            else {
                m_is_max.push_back(is_max);
                vars(ctx).push_back(ctx.m().mk_const(ctx.find_func_decl(slist[i])));
            }
        }
        ++m_position;
    }

    virtual void set_next_arg(cmd_context & ctx, expr * t) {
        if (!is_app(t)) {
            throw cmd_exception("malformed objective term: it cannot be a quantifier or bound variable");
        }
        ++m_position;
        get_opt(ctx).min_max(to_app(t), vars(ctx), m_is_max);
        reset(ctx);
    }

    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual void execute(cmd_context & ctx) { }
};


void install_opt_cmds(cmd_context & ctx) {
    ctx.insert(alloc(assert_soft_cmd));
    ctx.insert(alloc(min_maximize_cmd, true));
    ctx.insert(alloc(min_maximize_cmd, false));
    ctx.insert(alloc(alternate_min_max_cmd));
}


