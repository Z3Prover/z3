/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    simplifier_cmds.h

Abstract:
    Support for simplifier commands in SMT 2.0 front-end

Author:

    Nikolaj Bjorner (nbjorner) 2023-01-30

--*/
#include<sstream>
#include<vector>
#include "cmd_context/simplifier_cmds.h"
#include "cmd_context/cmd_context.h"
#include "cmd_context/cmd_util.h"
#include "cmd_context/parametric_cmd.h"
#include "model/model_smt2_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/simplifiers/then_simplifier.h"
#include "solver/simplifier_solver.h"

typedef dependent_expr_simplifier simplifier;

static simplifier_factory mk_and_then(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children < 2)
        throw cmd_exception("invalid and-then combinator, at least one argument expected", n->get_line(), n->get_pos());
    if (num_children == 2)
        return sexpr2simplifier(ctx, n->get_child(1));
    std::vector<simplifier_factory> args;
    for (unsigned i = 1; i < num_children; i++)
        args.push_back(sexpr2simplifier(ctx, n->get_child(i)));
    simplifier_factory result = [args](ast_manager& m, const params_ref& p, dependent_expr_state& st) {
        scoped_ptr<then_simplifier> s = alloc(then_simplifier, m, p, st);
        for (auto &  simp : args)
            s->add_simplifier(simp(m, p, st));
        return s.detach();
    };
    return result;
}

static simplifier_factory mk_using_params(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children < 2)
        throw cmd_exception("invalid using-params combinator, at least one argument expected", n->get_line(), n->get_pos());
    if (num_children == 2)
        return sexpr2simplifier(ctx, n->get_child(1));
    ast_manager& m = ctx.get_ast_manager();
    default_dependent_expr_state st(m);

    simplifier_factory fac = sexpr2simplifier(ctx, n->get_child(1));
    params_ref p;
    param_descrs descrs;
    scoped_ptr<dependent_expr_simplifier> s = fac(m, p, st);
    s->collect_param_descrs(descrs);
    params_ref params = sexpr2params(ctx, n, descrs);
    simplifier_factory result = [params, fac](auto& m, auto& p, auto& s) {   
        params_ref pp;
        pp.append(params);
        pp.append(p);
        return fac(m, pp, s);
    };
    return result;
}


simplifier_factory sexpr2simplifier(cmd_context & ctx, sexpr * n) {
    if (n->is_symbol()) {
        simplifier_cmd * cmd = ctx.find_simplifier_cmd(n->get_symbol());
        if (cmd != nullptr)
            return cmd->factory();
        throw cmd_exception("invalid tactic, unknown tactic ", n->get_symbol(), n->get_line(), n->get_pos());
    }
    else if (n->is_composite()) {
        unsigned num_children = n->get_num_children();
        if (num_children == 0)
            throw cmd_exception("invalid tactic, arguments expected", n->get_line(), n->get_pos());
        sexpr * head = n->get_child(0);
        if (!head->is_symbol())
            throw cmd_exception("invalid tactic, symbol expected", n->get_line(), n->get_pos());
        symbol const & cmd_name = head->get_symbol();
        if (cmd_name == "and-then" || cmd_name == "then")
            return mk_and_then(ctx, n);
        else if (cmd_name == "!" || cmd_name == "using-params" || cmd_name == "with")
            return mk_using_params(ctx, n);
        else
            throw cmd_exception("invalid tactic, unknown tactic combinator ", cmd_name, n->get_line(), n->get_pos());
    }
    else {
        throw cmd_exception("invalid tactic, unexpected input", n->get_line(), n->get_pos());
    }
}


void help_simplifier(cmd_context & ctx) {
    std::ostringstream buf;
    buf << "combinators:\n";
    buf << "- (and-then <simplifier>+) executes the given simplifiers sequentially.\n";
    buf << "- (using-params <tactic> <attribute>*) executes the given simplifier using the given attributes, where <attribute> ::= <keyword> <value>. ! is syntax sugar for using-params.\n";
    buf << "builtin simplifiers:\n";
    for (simplifier_cmd* cmd : ctx.simplifiers()) {
        buf << "- " << cmd->get_name() << " " << cmd->get_descr() << "\n";
        auto fac = cmd->factory();
        param_descrs descrs;
        ast_manager& m = ctx.get_ast_manager();
        default_dependent_expr_state st(m);
        params_ref p;
        scoped_ptr<dependent_expr_simplifier> s = fac(m, p, st);
        s->collect_param_descrs(descrs);
        descrs.display(buf, 4);
    }
    ctx.regular_stream() << '"' << escaped(buf.str()) << "\"\n";
}

ATOMIC_CMD(help_simplifier_cmd, "help-simplifier", "display the simplifier combinators and primitives.", help_simplifier(ctx););

class set_simplifier_cmd : public parametric_cmd {
protected:
    sexpr * m_simplifier = nullptr;
public:
    set_simplifier_cmd():
        parametric_cmd("set-simplifier") {}
    
    char const * get_usage() const override { return "<tactic> (<keyword> <value>)*"; }

    void prepare(cmd_context & ctx) override {
        parametric_cmd::prepare(ctx);
        m_simplifier = nullptr;
    }

    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override {
        if (m_simplifier == nullptr) return CPK_SEXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }

    void set_next_arg(cmd_context & ctx, sexpr * arg) override {
        m_simplifier = arg;
    }

    char const * get_main_descr() const override { return "update main solver with simplification pre-processing."; }

    void init_pdescrs(cmd_context & ctx, param_descrs & p) override {
    }

    void execute(cmd_context & ctx) override {
        if (!m_simplifier) 
            throw cmd_exception("set-simplifier needs a simplifier argument");
        
        auto simplifier_factory = sexpr2simplifier(ctx, m_simplifier);
        ctx.init_manager();
        auto* s = ctx.get_solver();
        ctx.set_simplifier_factory(simplifier_factory);
        if (!s) 
            return;
        if (s->get_num_assertions() > 0) 
            throw cmd_exception("set-simplifier cannot be invoked if there are already assertions");
        if (s->get_scope_level() > 0)
            throw cmd_exception("set-simplifier cannot be invoked above base scope level");
        ctx.set_solver(mk_simplifier_solver(s, &simplifier_factory));        
    }
};


void install_core_simplifier_cmds(cmd_context & ctx) {
    ctx.insert(alloc(set_simplifier_cmd));    
    ctx.insert(alloc(help_simplifier_cmd));
}
