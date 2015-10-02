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



void install_opt_cmds(cmd_context & ctx) {
    ctx.insert(alloc(assert_soft_cmd));
    ctx.insert(alloc(min_maximize_cmd, true));
    ctx.insert(alloc(min_maximize_cmd, false));
}


#if 0
    ctx.insert(alloc(optimize_cmd));
    ctx.insert(alloc(assert_weighted_cmd));


class optimize_cmd : public parametric_cmd {
public:
    optimize_cmd():
        parametric_cmd("optimize")
    {}

    virtual ~optimize_cmd() {
    }

    virtual void init_pdescrs(cmd_context & ctx, param_descrs & p) {
        insert_timeout(p);
        insert_max_memory(p);
        p.insert("print_statistics", CPK_BOOL, "(default: false) print statistics.");
        opt::context::collect_param_descrs(p);
    }

    virtual char const * get_main_descr() const { return "check sat modulo objective function";}
    virtual char const * get_usage() const { return "(<keyword> <value>)*"; }
    virtual void prepare(cmd_context & ctx) {
        parametric_cmd::prepare(ctx);
    }
    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        return parametric_cmd::next_arg_kind(ctx);
    }


    virtual void execute(cmd_context & ctx) {
        params_ref p = ctx.params().merge_default_params(ps());
        opt::context& opt = get_opt(ctx);
        opt.updt_params(p);
        unsigned timeout = p.get_uint("timeout", UINT_MAX);

        ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
        ptr_vector<expr>::const_iterator end = ctx.end_assertions();
        for (; it != end; ++it) {
            opt.add_hard_constraint(*it);
        }
        lbool r = l_undef;
        cancel_eh<opt::context> eh(opt);        
        {
            scoped_ctrl_c ctrlc(eh);
            scoped_timer timer(timeout, &eh);
            cmd_context::scoped_watch sw(ctx);
            try {
                r = opt.optimize();
                if (r == l_true && opt.is_pareto()) {
                    while (r == l_true) {
                        display_result(ctx);
                        ctx.regular_stream() << "\n";
                        r = opt.optimize();
                    }
                    if (p.get_bool("print_statistics", false)) {
                        display_statistics(ctx);
                    }
                    return;
                }
            }
            catch (z3_error& ex) {
                ctx.regular_stream() << "(error: " << ex.msg() << "\")" << std::endl;
            }
            catch (z3_exception& ex) {
                ctx.regular_stream() << "(error: " << ex.msg() << "\")" << std::endl;
            }
        }
        switch(r) {
        case l_true: {
            ctx.regular_stream() << "sat\n";
            display_result(ctx);
            break;
        }
        case l_false:
            ctx.regular_stream() << "unsat\n";
            break;
        case l_undef:
            ctx.regular_stream() << "unknown\n";
            display_result(ctx);
            break;
        }
        if (p.get_bool("print_statistics", false)) {
            display_statistics(ctx);
        }
    }

    void display_result(cmd_context & ctx) {
        params_ref p = ctx.params().merge_default_params(ps());
        opt::context& opt = get_opt(ctx);
        opt.display_assignment(ctx.regular_stream());
        opt_params optp(p);
        if (optp.print_model()) {
            model_ref mdl;
            opt.get_model(mdl);
            if (mdl) {
                ctx.regular_stream() << "(model " << std::endl;
                model_smt2_pp(ctx.regular_stream(), ctx, *(mdl.get()), 2);
                ctx.regular_stream() << ")" << std::endl;                    
            }
        }
    }
private:

    void display_statistics(cmd_context& ctx) {
        statistics stats;
        get_opt(ctx).collect_statistics(stats);
        stats.update("time", ctx.get_seconds());
        stats.display_smt2(ctx.regular_stream());        
    }
};

class assert_weighted_cmd : public cmd {
    unsigned     m_idx;
    expr*        m_formula;
    rational     m_weight;
    symbol       m_id;

public:
    assert_weighted_cmd():
        cmd("assert-weighted"),
        m_idx(0),
        m_formula(0),
        m_weight(0)
    {}

    virtual ~assert_weighted_cmd() {
    }

    virtual void reset(cmd_context & ctx) { 
        m_idx = 0; 
        m_formula = 0;
        m_id = symbol::null;
    }

    virtual char const * get_usage() const { return "<formula> <rational-weight>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "assert soft constraint with weight"; }
    virtual unsigned get_arity() const { return VAR_ARITY; }

    // command invocation
    virtual void prepare(cmd_context & ctx) {}
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { 
        switch(m_idx) {
        case 0: return CPK_EXPR; 
        case 1: return CPK_NUMERAL; 
        default: return CPK_SYMBOL;
        }
    }
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

    virtual void set_next_arg(cmd_context & ctx, symbol const& s) {
        SASSERT(m_idx > 1);
        m_id = s;
        ++m_idx;
    }

    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual void execute(cmd_context & ctx) {
        get_opt(ctx).add_soft_constraint(m_formula, m_weight, m_id);
        reset(ctx);
    }

    virtual void finalize(cmd_context & ctx) { 
    }

};

#endif
