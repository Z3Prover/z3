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

class opt_context {
    cmd_context& ctx;
    scoped_ptr<opt::context> m_opt;
    hashtable<symbol, symbol_hash_proc, symbol_eq_proc> m_ids;    

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
    symbol       m_id;

public:
    assert_weighted_cmd(cmd_context& ctx, opt_context& opt_ctx):
        cmd("assert-weighted"),
        m_opt_ctx(opt_ctx),
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
        m_opt_ctx().add_soft_constraint(m_formula, m_weight, m_id);
        reset(ctx);
    }

    virtual void finalize(cmd_context & ctx) { 
    }

};


class assert_soft_cmd : public parametric_cmd {
    opt_context& m_opt_ctx;
    unsigned     m_idx;
    expr*        m_formula;

public:
    assert_soft_cmd(cmd_context& ctx, opt_context& opt_ctx):
        parametric_cmd("assert-soft"),
        m_opt_ctx(opt_ctx),
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
        p.insert("dweight", CPK_DECIMAL, "(default: 1.0) penalty as double of not satisfying constraint.");
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
            weight = ps().get_rat(symbol("dweight"), rational(0));
        }
        if (weight.is_zero()) {
            weight = rational::one();
        }
        symbol id = ps().get_sym(symbol("id"), symbol::null);
        m_opt_ctx().add_soft_constraint(m_formula, weight, id);
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
        if (!is_app(t)) {
            throw cmd_exception("malformed objective term: it cannot be a quantifier or bound variable");
        }
        m_opt_ctx().add_objective(to_app(t), m_is_max);
    }

    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual void execute(cmd_context & ctx) {
    }
};

class optimize_cmd : public parametric_cmd {
    opt_context& m_opt_ctx;
public:
    optimize_cmd(opt_context& opt_ctx):
        parametric_cmd("optimize"),
        m_opt_ctx(opt_ctx)
    {}

    virtual ~optimize_cmd() {
        dealloc(&m_opt_ctx);
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
        opt::context& opt = m_opt_ctx();
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
            opt.display_assignment(ctx.regular_stream());
            opt_params optp(p);
            if (optp.print_model()) {
                model_ref mdl;
                opt.get_model(mdl);
                if (mdl) {
                    ctx.regular_stream() << "(model " << std::endl;
                    model_smt2_pp(ctx.regular_stream(), ctx, *(mdl.get()), 2);
                    // m->display(ctx.regular_stream());
                    ctx.regular_stream() << ")" << std::endl;                    
                }
            }
            break;
        }
        case l_false:
            ctx.regular_stream() << "unsat\n";
            break;
        case l_undef:
            ctx.regular_stream() << "unknown\n";
            opt.display_range_assignment(ctx.regular_stream());
            break;
        }
        if (p.get_bool("print_statistics", false)) {
            display_statistics(ctx);
        }
    }
private:

    void display_statistics(cmd_context& ctx) {
        statistics stats;
        unsigned long long max_mem = memory::get_max_used_memory();
        unsigned long long mem = memory::get_allocation_size();
        stats.update("time", ctx.get_seconds());
        stats.update("memory", static_cast<double>(mem)/static_cast<double>(1024*1024));
        stats.update("max memory", static_cast<double>(max_mem)/static_cast<double>(1024*1024));
        m_opt_ctx().collect_statistics(stats);
        stats.display_smt2(ctx.regular_stream());        
    }
};



void install_opt_cmds(cmd_context & ctx) {
    opt_context* opt_ctx = alloc(opt_context, ctx);
    ctx.insert(alloc(assert_weighted_cmd, ctx, *opt_ctx));
    ctx.insert(alloc(assert_soft_cmd, ctx, *opt_ctx));
    ctx.insert(alloc(min_maximize_cmd, ctx, *opt_ctx, true));
    ctx.insert(alloc(min_maximize_cmd, ctx, *opt_ctx, false));
    ctx.insert(alloc(optimize_cmd, *opt_ctx));
}

#if 0
    ctx.insert(alloc(execute_cmd, *opt_ctx));

class execute_cmd : public parametric_cmd {
protected:
    expr * m_objective;
    unsigned m_idx;
    opt_context& m_opt_ctx;
public:
    execute_cmd(opt_context& opt_ctx):
        parametric_cmd("optimize"),
        m_objective(0),
        m_idx(0),
        m_opt_ctx(opt_ctx)
    {}

    virtual void init_pdescrs(cmd_context & ctx, param_descrs & p) {
        insert_timeout(p);
        insert_max_memory(p);
        p.insert("print_statistics", CPK_BOOL, "(default: false) print statistics.");
        opt::context::collect_param_descrs(p);
    }

    virtual char const * get_main_descr() const { return "check sat modulo objective function";}
    virtual char const * get_usage() const { return "<objective> (<keyword> <value>)*"; }
    virtual void prepare(cmd_context & ctx) {
        parametric_cmd::prepare(ctx);
        reset(ctx);
        m_opt_ctx(); // ensure symbol table is updated.
    }
    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }
    virtual void reset(cmd_context& ctx) {
        m_objective = 0;
        m_idx = 0;
    }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        if (m_idx == 0) return CPK_EXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }

    virtual void set_next_arg(cmd_context & ctx, expr * arg) {
        m_objective = arg;
        ++m_idx;
    }

    virtual void execute(cmd_context & ctx) {
        params_ref p = ctx.params().merge_default_params(ps());
        opt::context& opt = m_opt_ctx();
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
                r = opt.optimize(m_objective);
            }
            catch (z3_error& ex) {
                ctx.regular_stream() << "(error: " << ex.msg() << "\")" << std::endl;
            }
            catch (z3_exception& ex) {
                ctx.regular_stream() << "(error: " << ex.msg() << "\")" << std::endl;
            }
        }
        switch(r) {
        case l_true:
            ctx.regular_stream() << "sat\n";
            opt.display_assignment(ctx.regular_stream());
            break;
        case l_false:
            ctx.regular_stream() << "unsat\n";
            break;
        case l_undef:
            ctx.regular_stream() << "unknown\n";
            opt.display_range_assignment(ctx.regular_stream());
            break;
        }
        if (p.get_bool("print_statistics", false)) {
            display_statistics(ctx);
        }
    }
private:

    void display_statistics(cmd_context& ctx) {
        statistics stats;
        unsigned long long max_mem = memory::get_max_used_memory();
        unsigned long long mem = memory::get_allocation_size();
        stats.update("time", ctx.get_seconds());
        stats.update("memory", static_cast<double>(mem)/static_cast<double>(1024*1024));
        stats.update("max memory", static_cast<double>(max_mem)/static_cast<double>(1024*1024));
        m_opt_ctx().collect_statistics(stats);
        stats.display_smt2(ctx.regular_stream());        
    }
};
#endif
