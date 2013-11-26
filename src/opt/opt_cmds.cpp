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
#include "objective_ast.h"

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
        dealloc(&m_opt_ctx);
    }

    virtual void reset(cmd_context & ctx) { 
        if (m_formula) {
            ctx.m().dec_ref(m_formula);
        }
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
        ctx.m().inc_ref(t);
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

static expr* sexpr2expr(cmd_context & ctx, sexpr * s) {
    NOT_IMPLEMENTED_YET();
    return 0;
}

static opt::objective* sexpr2objective(cmd_context & ctx, sexpr * s) {
    if (s->is_symbol())
        throw cmd_exception("invalid objective, more arguments expected ", s->get_symbol(), s->get_line(), s->get_pos());   
    if (s->is_composite()) {
        sexpr * head = s->get_child(0);
        if (!head->is_symbol())
            throw cmd_exception("invalid objective, symbol expected", s->get_line(), s->get_pos());
        symbol const & cmd_name = head->get_symbol();
        if (cmd_name == "maximize" || cmd_name == "minimize") {
            if (s->get_num_children() != 2)
                throw cmd_exception("invalid objective, wrong number of arguments ", s->get_line(), s->get_pos());
            sexpr * arg = s->get_child(1);
            expr_ref term(sexpr2expr(ctx, arg), ctx.m());
            if (cmd_name == "maximize")
                return opt::objective::mk_max(term);
            else
                return opt::objective::mk_min(term);
        }
        else if (cmd_name == "maxsat") {
            if (s->get_num_children() != 2)
                throw cmd_exception("invalid objective, wrong number of arguments ", s->get_line(), s->get_pos());
            sexpr * arg = s->get_child(1);
            if (!arg->is_symbol())
                throw cmd_exception("invalid objective, symbol expected", s->get_line(), s->get_pos());
            symbol const & id = arg->get_symbol();
            // TODO: check whether id is declared via assert-weighted
            return opt::objective::mk_maxsat(id);
        }
        else if (cmd_name == "lex" || cmd_name == "box" || cmd_name == "pareto") {
            if (s->get_num_children() <= 2)
                throw cmd_exception("invalid objective, wrong number of arguments ", s->get_line(), s->get_pos());
            unsigned num_children = s->get_num_children();
            ptr_vector<opt::objective> args;
            for (unsigned i = 1; i < num_children; i++)
                args.push_back(sexpr2objective(ctx, s->get_child(i)));
            if (cmd_name == "lex") 
                return opt::objective::mk_lex(args.size(), args.c_ptr());
            else if (cmd_name == "box") 
                return opt::objective::mk_box(args.size(), args.c_ptr());
            else
                return opt::objective::mk_pareto(args.size(), args.c_ptr());
        }
        else {
            throw cmd_exception("invalid objective, unexpected input", s->get_line(), s->get_pos());
        }
    }
    return 0;
}

class execute_cmd : public parametric_cmd {
protected:
    sexpr * m_objective;
    opt_context& m_opt_ctx;
public:
    execute_cmd(opt_context& opt_ctx):
        parametric_cmd("optimize"),
        m_opt_ctx(opt_ctx)
    {}

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
        m_objective = 0;
    }
    virtual void failure_cleanup(cmd_context & ctx) {
        reset(ctx);
    }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        if (m_objective == 0) return CPK_SEXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }

    virtual void set_next_arg(cmd_context & ctx, sexpr * arg) {
        m_objective = arg;
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
                opt::objective * o = sexpr2objective(ctx, m_objective);
                r = opt.optimize(*o);
                dealloc(o);
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

void install_opt_cmds(cmd_context & ctx) {
    opt_context* opt_ctx = alloc(opt_context, ctx);
    ctx.insert(alloc(assert_weighted_cmd, ctx, *opt_ctx));
    ctx.insert(alloc(execute_cmd, *opt_ctx));
    //ctx.insert(alloc(min_maximize_cmd, ctx, *opt_ctx, true));
    //ctx.insert(alloc(min_maximize_cmd, ctx, *opt_ctx, false));
    //ctx.insert(alloc(optimize_cmd, *opt_ctx));
}
