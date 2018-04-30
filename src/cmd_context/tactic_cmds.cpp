/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    tactic_cmds.cpp

Abstract:
    Support for tactics in SMT 2.0 frontend.

Author:

    Leonardo (leonardo) 2011-10-20

Notes:

--*/
#include<sstream>
#include "cmd_context/tactic_cmds.h"
#include "cmd_context/cmd_context.h"
#include "cmd_context/cmd_util.h"
#include "cmd_context/parametric_cmd.h"
#include "util/scoped_timer.h"
#include "util/scoped_ctrl_c.h"
#include "util/cancel_eh.h"
#include "model/model_smt2_pp.h"
#include "ast/ast_smt2_pp.h"
#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "tactic/probe.h"
#include "solver/check_sat_result.h"
#include "cmd_context/cmd_context_to_goal.h"
#include "cmd_context/echo_tactic.h"

tactic_cmd::~tactic_cmd() {
    dealloc(m_factory);
}

tactic * tactic_cmd::mk(ast_manager & m) {
    return (*m_factory)(m, params_ref());
}

probe_info::probe_info(symbol const & n, char const * d, probe * p):
    m_name(n),
    m_descr(d),
    m_probe(p) {
}

probe_info::~probe_info() {
}

class declare_tactic_cmd : public cmd {
    symbol           m_name;
    sexpr *          m_decl;
public:
    declare_tactic_cmd():
        cmd("declare-tactic"),
        m_decl(nullptr) {
    }

    char const * get_usage() const override { return "<symbol> <tactic>"; }
    char const * get_descr(cmd_context & ctx) const override { return "declare a new tactic, use (help-tactic) for the tactic language syntax."; }
    unsigned get_arity() const override { return 2; }
    void prepare(cmd_context & ctx) override { m_name = symbol::null; m_decl = nullptr; }
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override {
        if (m_name == symbol::null) return CPK_SYMBOL;
        return CPK_SEXPR;
    }
    void set_next_arg(cmd_context & ctx, symbol const & s) override { m_name = s; }
    void set_next_arg(cmd_context & ctx, sexpr * n) override { m_decl = n; }
    void execute(cmd_context & ctx) override {
        tactic_ref t = sexpr2tactic(ctx, m_decl); // make sure the tactic is well formed.
        ctx.insert_user_tactic(m_name, m_decl);
    }
};

ATOMIC_CMD(get_user_tactics_cmd, "get-user-tactics", "display tactics defined using the declare-tactic command.", {
    ctx.regular_stream() << "(";
    std::ostringstream buf;
    cmd_context::user_tactic_iterator it  = ctx.begin_user_tactics();
    cmd_context::user_tactic_iterator end = ctx.end_user_tactics();
    for (bool first = true; it != end; ++it) {
        if (first) first = false; else buf << "\n ";
        buf << "(declare-tactic " << it->m_key << " ";
        it->m_value->display(buf);
        buf << ")";
    }
    std::string r = buf.str();
    ctx.regular_stream() << escaped(r.c_str());
    ctx.regular_stream() << ")\n";
});

void help_tactic(cmd_context & ctx) {
    std::ostringstream buf;
    buf << "combinators:\n";
    buf << "- (and-then <tactic>+) executes the given tactics sequencially.\n";
    buf << "- (or-else <tactic>+) tries the given tactics in sequence until one of them succeeds (i.e., the first that doesn't fail).\n";
    buf << "- (par-or <tactic>+) executes the given tactics in parallel until one of them succeeds (i.e., the first that doesn't fail).\n";
    buf << "- (par-then <tactic1> <tactic2>) executes tactic1 and then tactic2 to every subgoal produced by tactic1. All subgoals are processed in parallel.\n";
    buf << "- (try-for <tactic> <num>) executes the given tactic for at most <num> milliseconds, it fails if the execution takes more than <num> milliseconds.\n";
    buf << "- (if <probe> <tactic> <tactic>) if <probe> evaluates to true, then execute the first tactic. Otherwise execute the second.\n";
    buf << "- (when <probe> <tactic>) shorthand for (if <probe> <tactic> skip).\n";
    buf << "- (fail-if <probe>) fail if <probe> evaluates to true.\n";
    buf << "- (using-params <tactic> <attribute>*) executes the given tactic using the given attributes, where <attribute> ::= <keyword> <value>. ! is a syntax sugar for using-params.\n";
    buf << "builtin tactics:\n";
    cmd_context::tactic_cmd_iterator it  = ctx.begin_tactic_cmds();
    cmd_context::tactic_cmd_iterator end = ctx.end_tactic_cmds();
    for (; it != end; ++it) {
        tactic_cmd * cmd = *it;
        buf << "- " << cmd->get_name() << " " << cmd->get_descr() << "\n";
        tactic_ref t = cmd->mk(ctx.m());
        param_descrs descrs;
        t->collect_param_descrs(descrs);
        descrs.display(buf, 4);
    }
    buf << "builtin probes:\n";
    cmd_context::probe_iterator it2  = ctx.begin_probes();
    cmd_context::probe_iterator end2 = ctx.end_probes();
    for (; it2 != end2; ++it2) {
        probe_info * pinfo = *it2;
        buf << "- " << pinfo->get_name() << " " << pinfo->get_descr() << "\n";
    }
    ctx.regular_stream() << "\"" << escaped(buf.str().c_str()) << "\"\n";
}

ATOMIC_CMD(help_tactic_cmd, "help-tactic", "display the tactic combinators and primitives.", help_tactic(ctx););

class exec_given_tactic_cmd : public parametric_cmd {
protected:
    sexpr * m_tactic;
public:
    exec_given_tactic_cmd(char const * name):
        parametric_cmd(name) {
    }

    char const * get_usage() const override { return "<tactic> (<keyword> <value>)*"; }

    void prepare(cmd_context & ctx) override {
        parametric_cmd::prepare(ctx);
        m_tactic = nullptr;
    }

    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override {
        if (m_tactic == nullptr) return CPK_SEXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }

    void set_next_arg(cmd_context & ctx, sexpr * arg) override {
        m_tactic = arg;
    }

    void init_pdescrs(cmd_context & ctx, param_descrs & p) override {
        insert_timeout(p);
        insert_max_memory(p);
        p.insert("print_statistics", CPK_BOOL, "(default: false) print statistics.");
    }

    void display_statistics(cmd_context & ctx, tactic * t) {
        statistics stats;
        get_memory_statistics(stats);
        get_rlimit_statistics(ctx.m().limit(), stats);
        stats.update("time", ctx.get_seconds());
        t->collect_statistics(stats);
        stats.display_smt2(ctx.regular_stream());
    }
};

struct check_sat_tactic_result : public simple_check_sat_result {
public:
  labels_vec labels;

  check_sat_tactic_result(ast_manager & m) : simple_check_sat_result(m) {
  }

  void get_labels(svector<symbol> & r) override {
    r.append(labels);
  }

  virtual void add_labels(svector<symbol> & r) {
    labels.append(r);
  }
};

class check_sat_using_tactict_cmd : public exec_given_tactic_cmd {
public:
    check_sat_using_tactict_cmd():
        exec_given_tactic_cmd("check-sat-using") {
    }

    char const * get_main_descr() const override { return "check if the current context is satisfiable using the given tactic, use (help-tactic) for the tactic language syntax."; }

    void init_pdescrs(cmd_context & ctx, param_descrs & p) override {
        exec_given_tactic_cmd::init_pdescrs(ctx, p);
        p.insert("print_unsat_core", CPK_BOOL, "(default: false) print unsatisfiable core.");
        p.insert("print_proof", CPK_BOOL, "(default: false) print proof.");
        p.insert("print_model", CPK_BOOL, "(default: false) print model.");
    }

    void execute(cmd_context & ctx) override {
        if (!m_tactic) {
            throw cmd_exception("check-sat-using needs a tactic argument");
        }
        if (ctx.ignore_check())
            return;
        params_ref p = ctx.params().merge_default_params(ps());
        tactic_ref tref = using_params(sexpr2tactic(ctx, m_tactic), p);
        tref->set_logic(ctx.get_logic());
        ast_manager & m = ctx.m();
        unsigned timeout   = p.get_uint("timeout", ctx.params().m_timeout);
        unsigned rlimit  =   p.get_uint("rlimit", ctx.params().rlimit());
        labels_vec labels;
        goal_ref g = alloc(goal, m, ctx.produce_proofs(), ctx.produce_models(), ctx.produce_unsat_cores());
        assert_exprs_from(ctx, *g);
        TRACE("check_sat_using", g->display(tout););
        model_ref           md;
        proof_ref           pr(m);
        expr_dependency_ref core(m);
        std::string reason_unknown;
        ref<check_sat_tactic_result> result = alloc(check_sat_tactic_result, m);
        ctx.set_check_sat_result(result.get());
        {
            tactic & t = *tref;
            cancel_eh<reslimit>  eh(m.limit());
            {
                scoped_rlimit _rlimit(m.limit(), rlimit);
                scoped_ctrl_c ctrlc(eh);
                scoped_timer timer(timeout, &eh);
                cmd_context::scoped_watch sw(ctx);
                lbool r = l_undef;
                try {
                    r = check_sat(t, g, md, result->labels, pr, core, reason_unknown);                    
                    ctx.display_sat_result(r);
                    result->set_status(r);
                    if (r == l_undef) {
                        if (reason_unknown != "") {
                            result->m_unknown = reason_unknown;
                            // ctx.diagnostic_stream() << "\"" << escaped(reason_unknown.c_str(), true) << "\"" << std::endl;
                        }
                        else {
                            result->m_unknown = "unknown";
                        }
                    }
                }
                catch (z3_error & ex) {
                    throw ex;
                }
                catch (z3_exception & ex) {
                    result->set_status(l_undef);
                    result->m_unknown = ex.msg();
                    ctx.regular_stream() << "(error \"tactic failed: " << ex.msg() << "\")" << std::endl;
                }
                ctx.validate_check_sat_result(r);
            }
            t.collect_statistics(result->m_stats);
        }

        if (ctx.produce_unsat_cores()) {
            ptr_vector<expr> core_elems;
            m.linearize(core, core_elems);
            result->m_core.append(core_elems.size(), core_elems.c_ptr());
            if (p.get_bool("print_unsat_core", false)) {
                ctx.regular_stream() << "(unsat-core";
                for (expr * e : core_elems) {
                    ctx.regular_stream() << " ";
                    ctx.display(ctx.regular_stream(), e);
                }
                ctx.regular_stream() << ")" << std::endl;
            }
        }

        if (ctx.produce_models() && md) {
            result->m_model = md;
            if (p.get_bool("print_model", false)) {
                ctx.regular_stream() << "(model " << std::endl;
                model_smt2_pp(ctx.regular_stream(), ctx, *md, 2);
                ctx.regular_stream() << ")" << std::endl;
            }
            if (result->status() == l_true)
                ctx.validate_model();
        }

        if (ctx.produce_proofs() && pr) {
            result->m_proof = pr;
            if (p.get_bool("print_proof", false)) {
                ctx.regular_stream() << mk_ismt2_pp(pr, m) << "\n";
            }
        }

        if (p.get_bool("print_statistics", false))
            display_statistics(ctx, tref.get());
    }
};

class apply_tactic_cmd : public exec_given_tactic_cmd {
public:
    apply_tactic_cmd():
        exec_given_tactic_cmd("apply") {
    }

    char const * get_main_descr() const override { return "apply the given tactic to the current context, and print the resultant set of goals."; }

    void init_pdescrs(cmd_context & ctx, param_descrs & p) override {
        p.insert("print", CPK_BOOL, "(default: true) print resultant goals.");
#ifndef _EXTERNAL_RELEASE
        p.insert("print_proof", CPK_BOOL, "(default: false) print proof associated with each assertion.");
#endif
        p.insert("print_model_converter", CPK_BOOL, "(default: false) print model converter.");
        p.insert("print_benchmark", CPK_BOOL, "(default: false) display resultant goals as a SMT2 benchmark.");
        p.insert("print_dependencies", CPK_BOOL, "(default: false) print dependencies when displaying the resultant set of goals.");
        exec_given_tactic_cmd::init_pdescrs(ctx, p);
    }

    void execute(cmd_context & ctx) override {
        if (!m_tactic) {
            throw cmd_exception("apply needs a tactic argument");
        }
        params_ref p = ctx.params().merge_default_params(ps());
        tactic_ref tref = using_params(sexpr2tactic(ctx, m_tactic), p);
        {
            tactic & t = *(tref.get());
            ast_manager & m = ctx.m();
            goal_ref g = alloc(goal, m, ctx.produce_proofs(), ctx.produce_models(), ctx.produce_unsat_cores());
            assert_exprs_from(ctx, *g);

            unsigned timeout   = p.get_uint("timeout", ctx.params().m_timeout);
            unsigned rlimit  =   p.get_uint("rlimit", ctx.params().rlimit());

            goal_ref_buffer     result_goals;

            std::string reason_unknown;
            bool failed = false;
            cancel_eh<reslimit>  eh(m.limit());
            {
                scoped_rlimit _rlimit(m.limit(), rlimit);
                scoped_ctrl_c ctrlc(eh);
                scoped_timer timer(timeout, &eh);
                cmd_context::scoped_watch sw(ctx);
                try {
                    exec(t, g, result_goals);
                }
                catch (tactic_exception & ex) {
                    ctx.regular_stream() << "(error \"tactic failed: " << ex.msg() << "\")" << std::endl;
                    failed = true;
                }
            }

            if (!failed && p.get_bool("print", true)) {
                bool print_dependencies = p.get_bool("print_dependencies", false);
                ctx.regular_stream() << "(goals\n";
                unsigned sz = result_goals.size();
                for (unsigned i = 0; i < sz; i++) {
                    if (print_dependencies)
                        result_goals[i]->display_with_dependencies(ctx);
                    else
                        result_goals[i]->display(ctx);
                }
                ctx.regular_stream() << ")\n";
            }

#ifndef _EXTERNAL_RELEASE
            if (!failed && ctx.produce_proofs() && p.get_bool("print_proof", false)) {
                // TODO
            }
#endif

            if (!failed && p.get_bool("print_benchmark", false)) {
                unsigned num_goals = result_goals.size();
                SASSERT(num_goals > 0);
                if (num_goals == 1) {
                    // easy case
                    goal * fg = result_goals[0];
                    unsigned sz = fg->size();
                    ptr_buffer<expr> assertions;
                    for (unsigned i = 0; i < sz; i++) {
                        assertions.push_back(fg->form(i));
                    }
                    ctx.display_smt2_benchmark(ctx.regular_stream(), assertions.size(), assertions.c_ptr());
                }
                else {
                    // create a big OR
                    expr_ref_buffer or_args(m);
                    ptr_vector<expr> formulas;
                    for (unsigned i = 0; i < num_goals; i++) {
                        formulas.reset();
                        result_goals[i]->get_formulas(formulas);
                        if (formulas.size() == 1)
                            or_args.push_back(formulas[0]);
                        else
                            or_args.push_back(m.mk_and(formulas.size(), formulas.c_ptr()));
                    }
                    expr_ref assertion_ref(m);
                    assertion_ref = m.mk_or(or_args.size(), or_args.c_ptr());
                    expr * assertions[1] = { assertion_ref.get() };
                    ctx.display_smt2_benchmark(ctx.regular_stream(), 1, assertions);
                }
            }

            if (!failed && g->mc() && p.get_bool("print_model_converter", false))
                g->mc()->display(ctx.regular_stream());

            if (p.get_bool("print_statistics", false))
                display_statistics(ctx, tref.get());
        }
    }
};

// The install_tactics procedure is automatically generated for every
// component that includes the cmd_context & tactic modules.
void install_tactics(tactic_manager & ctx);

void install_core_tactic_cmds(cmd_context & ctx) {
    ctx.insert(alloc(declare_tactic_cmd));
    ctx.insert(alloc(get_user_tactics_cmd));
    ctx.insert(alloc(help_tactic_cmd));
    ctx.insert(alloc(check_sat_using_tactict_cmd));
    ctx.insert(alloc(apply_tactic_cmd));
    install_tactics(ctx);
}

static tactic * mk_and_then(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children < 2)
        throw cmd_exception("invalid and-then combinator, at least one argument expected", n->get_line(), n->get_pos());
    if (num_children == 2)
        return sexpr2tactic(ctx, n->get_child(1));
    tactic_ref_buffer args;
    for (unsigned i = 1; i < num_children; i++)
        args.push_back(sexpr2tactic(ctx, n->get_child(i)));
    return and_then(args.size(), args.c_ptr());
}

static tactic * mk_or_else(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children < 2)
        throw cmd_exception("invalid or-else combinator, at least one argument expected", n->get_line(), n->get_pos());
    if (num_children == 2)
        return sexpr2tactic(ctx, n->get_child(1));
    tactic_ref_buffer args;
    for (unsigned i = 1; i < num_children; i++)
        args.push_back(sexpr2tactic(ctx, n->get_child(i)));
    return or_else(args.size(), args.c_ptr());
}

static tactic * mk_par(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children < 2)
        throw cmd_exception("invalid par-or combinator, at least one argument expected", n->get_line(), n->get_pos());
    if (num_children == 2)
        return sexpr2tactic(ctx, n->get_child(1));
    tactic_ref_buffer args;
    for (unsigned i = 1; i < num_children; i++)
        args.push_back(sexpr2tactic(ctx, n->get_child(i)));
    return par(args.size(), args.c_ptr());
}

static tactic * mk_par_then(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children < 2)
        throw cmd_exception("invalid par-then combinator, at least one argument expected", n->get_line(), n->get_pos());
    if (num_children == 2)
        return sexpr2tactic(ctx, n->get_child(1));
    tactic_ref_buffer args;
    for (unsigned i = 1; i < num_children; i++)
        args.push_back(sexpr2tactic(ctx, n->get_child(i)));
    return par_and_then(args.size(), args.c_ptr());
}

static tactic * mk_try_for(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children != 3)
        throw cmd_exception("invalid try-for combinator, two arguments expected", n->get_line(), n->get_pos());
    if (!n->get_child(2)->is_numeral() || !n->get_child(2)->get_numeral().is_unsigned())
        throw cmd_exception("invalid try-for combinator, second argument must be an unsigned integer", n->get_line(), n->get_pos());
    tactic * t = sexpr2tactic(ctx, n->get_child(1));
    unsigned timeout = n->get_child(2)->get_numeral().get_unsigned();
    return try_for(t, timeout);
}

static tactic * mk_repeat(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children != 3 && num_children != 2)
        throw cmd_exception("invalid repeat combinator, one or two arguments expected", n->get_line(), n->get_pos());
    unsigned max = UINT_MAX;
    if (num_children == 3) {
        if (!n->get_child(2)->is_numeral() || !n->get_child(2)->get_numeral().is_unsigned())
            throw cmd_exception("invalid repeat combinator, second argument must be an unsigned integer", n->get_line(), n->get_pos());
        max = n->get_child(2)->get_numeral().get_unsigned();
    }
    tactic * t = sexpr2tactic(ctx, n->get_child(1));
    return repeat(t, max);
}

static tactic * mk_using_params(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children < 2)
        throw cmd_exception("invalid using-params combinator, at least one argument expected", n->get_line(), n->get_pos());
    if (num_children == 2)
        return sexpr2tactic(ctx, n->get_child(1));
    tactic_ref t = sexpr2tactic(ctx, n->get_child(1));
    param_descrs descrs;
    t->collect_param_descrs(descrs);
    params_ref p;
    unsigned i = 2;
    while (i < num_children) {
        sexpr * c = n->get_child(i);
        i++;
        if (!c->is_keyword())
            throw cmd_exception("invalid using-params combinator, keyword expected", c->get_line(), c->get_pos());
        if (i == num_children)
            throw cmd_exception("invalid using-params combinator, parameter value expected", c->get_line(), c->get_pos());
        symbol param_name = symbol(norm_param_name(c->get_symbol()).c_str());
        c = n->get_child(i);
        i++;
        switch (descrs.get_kind_in_module(param_name)) {
        case CPK_INVALID:
            throw cmd_exception("invalid using-params combinator, unknown parameter ", param_name, c->get_line(), c->get_pos());
        case CPK_BOOL:
            if (!c->is_symbol() || (c->get_symbol() != "true" && c->get_symbol() != "false"))
                throw cmd_exception("invalid parameter value, true or false expected", c->get_line(), c->get_pos());
            p.set_bool(param_name, c->get_symbol() == "true");
            break;
        case CPK_UINT:
            if (!c->is_numeral() || !c->get_numeral().is_unsigned())
                throw cmd_exception("invalid parameter value, unsigned integer expected", c->get_line(), c->get_pos());
            p.set_uint(param_name, c->get_numeral().get_unsigned());
            break;
        case CPK_NUMERAL:
            if (!c->is_numeral())
                throw cmd_exception("invalid parameter value, numeral expected", c->get_line(), c->get_pos());
            p.set_rat(param_name, c->get_numeral());
            break;
        case CPK_SYMBOL:
            if (!c->is_symbol())
                throw cmd_exception("invalid parameter value, symbol expected", c->get_line(), c->get_pos());
            p.set_sym(param_name, c->get_symbol());
            break;
        case CPK_DOUBLE:
            if (!c->is_numeral())
                throw cmd_exception("invalid parameter value, numeral expected", c->get_line(), c->get_pos());
            p.set_double(param_name, c->get_numeral().get_double());
            break;
        default:
            throw cmd_exception("invalid using-params combinator, unsupported parameter kind");
        }
    }
    return using_params(t.get(), p);
}

static tactic * mk_if(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children != 4)
        throw cmd_exception("invalid if/conditional combinator, three arguments expected", n->get_line(), n->get_pos());
    probe_ref   c = sexpr2probe(ctx, n->get_child(1));
    tactic_ref  t = sexpr2tactic(ctx, n->get_child(2));
    tactic_ref  e = sexpr2tactic(ctx, n->get_child(3));
    return cond(c.get(), t.get(), e.get());
}

static tactic * mk_fail_if(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children != 2)
        throw cmd_exception("invalid fail-if tactic, one argument expected", n->get_line(), n->get_pos());
    probe_ref   c = sexpr2probe(ctx, n->get_child(1));
    return fail_if(c.get());
}

static tactic * mk_when(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children != 3)
        throw cmd_exception("invalid when combinator, two arguments expected", n->get_line(), n->get_pos());
    probe_ref   c = sexpr2probe(ctx, n->get_child(1));
    tactic_ref  t = sexpr2tactic(ctx, n->get_child(2));
    return cond(c.get(), t.get(), mk_skip_tactic());
}

static tactic * mk_echo(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children < 2)
        throw cmd_exception("invalid echo tactic, must have at least one argument", n->get_line(), n->get_pos());
    tactic_ref res;
    for (unsigned i = 1; i < num_children; i++) {
        sexpr * curr = n->get_child(i);
        bool last = (i == num_children - 1);
        tactic * t;
        if (curr->is_string())
            t = mk_echo_tactic(ctx, curr->get_string().c_str(), last);
        else
            t = mk_probe_value_tactic(ctx, nullptr, sexpr2probe(ctx, curr), last);
        tactic * new_res;
        if (res.get() == nullptr)
            new_res = t;
        else
            new_res = and_then(res.get(), t);
        if (last)
            return new_res;
        res = new_res;
    }
    UNREACHABLE();
    return nullptr;
}

static tactic * mk_fail_if_branching(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children != 3 && num_children != 2)
        throw cmd_exception("invalid fail-if-branching combinator, one or two arguments expected", n->get_line(), n->get_pos());
    unsigned threshold = 1;
    if (num_children == 3) {
        if (!n->get_child(2)->is_numeral() || !n->get_child(2)->get_numeral().is_unsigned())
            throw cmd_exception("invalid fail-if-branching combinator, second argument must be an unsigned integer", n->get_line(), n->get_pos());
        threshold = n->get_child(2)->get_numeral().get_unsigned();
    }
    tactic * t = sexpr2tactic(ctx, n->get_child(1));
    return fail_if_branching(t, threshold);
}

static tactic * mk_if_no_proofs(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children != 2)
        throw cmd_exception("invalid if-no-proofs combinator, one argument expected", n->get_line(), n->get_pos());
    tactic * t = sexpr2tactic(ctx, n->get_child(1));
    return if_no_proofs(t);
}

static tactic * mk_if_no_models(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children != 2)
        throw cmd_exception("invalid if-no-models combinator, one argument expected", n->get_line(), n->get_pos());
    tactic * t = sexpr2tactic(ctx, n->get_child(1));
    return if_no_models(t);
}

static tactic * mk_if_no_unsat_cores(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children != 2)
        throw cmd_exception("invalid if-no-unsat-cores combinator, one argument expected", n->get_line(), n->get_pos());
    tactic * t = sexpr2tactic(ctx, n->get_child(1));
    return if_no_unsat_cores(t);
}

static tactic * mk_skip_if_failed(cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children != 2)
        throw cmd_exception("invalid skip-if-failed combinator, one argument expected", n->get_line(), n->get_pos());
    tactic * t = sexpr2tactic(ctx, n->get_child(1));
    return skip_if_failed(t);
}

tactic * sexpr2tactic(cmd_context & ctx, sexpr * n) {
    if (n->is_symbol()) {
        tactic_cmd * cmd = ctx.find_tactic_cmd(n->get_symbol());
        if (cmd != nullptr)
            return cmd->mk(ctx.m());
        sexpr * decl = ctx.find_user_tactic(n->get_symbol());
        if (decl != nullptr)
            return sexpr2tactic(ctx, decl);
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
        else if (cmd_name == "or-else")
            return mk_or_else(ctx, n);
        else if (cmd_name == "par")
            return mk_par(ctx, n);
        else if (cmd_name == "par-or")
            return mk_par(ctx, n);
        else if (cmd_name == "par-then")
            return mk_par_then(ctx, n);
        else if (cmd_name == "try-for")
            return mk_try_for(ctx, n);
        else if (cmd_name == "repeat")
            return mk_repeat(ctx, n);
        else if (cmd_name == "if" || cmd_name == "ite" || cmd_name == "cond")
            return mk_if(ctx, n);
        else if (cmd_name == "fail-if")
            return mk_fail_if(ctx, n);
        else if (cmd_name == "fail-if-branching")
            return mk_fail_if_branching(ctx, n);
        else if (cmd_name == "when")
            return mk_when(ctx, n);
        else if (cmd_name == "!" || cmd_name == "using-params" || cmd_name == "with")
            return mk_using_params(ctx, n);
        else if (cmd_name == "echo")
            return mk_echo(ctx, n);
        else if (cmd_name == "if-no-proofs")
            return mk_if_no_proofs(ctx, n);
        else if (cmd_name == "if-no-models")
            return mk_if_no_models(ctx, n);
        else if (cmd_name == "if-no-unsat-cores")
            return mk_if_no_unsat_cores(ctx, n);
        else if (cmd_name == "skip-if-failed")
            return mk_skip_if_failed(ctx, n);
        else
            throw cmd_exception("invalid tactic, unknown tactic combinator ", cmd_name, n->get_line(), n->get_pos());
    }
    else {
        throw cmd_exception("invalid tactic, unexpected input", n->get_line(), n->get_pos());
    }
}

static probe * mk_not_probe (cmd_context & ctx, sexpr * n) {
    SASSERT(n->is_composite());
    unsigned num_children = n->get_num_children();
    if (num_children != 2)
        throw cmd_exception("invalid probe expression, one argument expected", n->get_line(), n->get_pos());
    return mk_not(sexpr2probe(ctx, n->get_child(1)));
}

#define MK_BIN_PROBE(NAME)                                                                                      \
static probe * NAME ## _probe (cmd_context & ctx, sexpr * n) {                                                  \
    SASSERT(n->is_composite());                                                                                 \
    unsigned num_children = n->get_num_children();                                                              \
    if (num_children != 3)                                                                                      \
        throw cmd_exception("invalid probe expression, two arguments expected", n->get_line(), n->get_pos());   \
    ref<probe> p1 = sexpr2probe(ctx, n->get_child(1));                                                          \
    ref<probe> p2 = sexpr2probe(ctx, n->get_child(2));                                                          \
    return NAME(p1.get(), p2.get());                                                                            \
}

MK_BIN_PROBE(mk_eq);
MK_BIN_PROBE(mk_le);
MK_BIN_PROBE(mk_lt);
MK_BIN_PROBE(mk_ge);
MK_BIN_PROBE(mk_gt);
MK_BIN_PROBE(mk_implies);
MK_BIN_PROBE(mk_div);
MK_BIN_PROBE(mk_sub);

#define MK_NARY_PROBE(NAME)                                                                                     \
static probe * NAME ## _probe(cmd_context & ctx, sexpr * n) {                                                   \
    SASSERT(n->is_composite());                                                                                 \
    unsigned num_children = n->get_num_children();                                                              \
    if (num_children < 2)                                                                                       \
        throw cmd_exception("invalid probe, at least one argument expected", n->get_line(), n->get_pos());      \
    probe * r = sexpr2probe(ctx, n->get_child(1));                                                              \
    if (num_children == 2)                                                                                      \
        return r;                                                                                               \
    ref<probe> prev = r;                                                                                        \
    unsigned i = 1;                                                                                             \
    while (true) {                                                                                              \
        r = NAME(prev.get(), sexpr2probe(ctx, n->get_child(i)));                                                \
        if (i == num_children - 1)                                                                              \
            return r;                                                                                           \
        i++;                                                                                                    \
        prev = r;                                                                                               \
    }                                                                                                           \
}

MK_NARY_PROBE(mk_and);
MK_NARY_PROBE(mk_or);
MK_NARY_PROBE(mk_add);
MK_NARY_PROBE(mk_mul);

probe * sexpr2probe(cmd_context & ctx, sexpr * n) {
    if (n->is_symbol()) {
        probe_info * pinfo = ctx.find_probe(n->get_symbol());
        if (pinfo != nullptr)
            return pinfo->get();
        throw cmd_exception("invalid probe, unknown builtin probe ", n->get_symbol(), n->get_line(), n->get_pos());
    }
    else if (n->is_numeral()) {
        rational const & v = n->get_numeral();
        if (!v.is_int32())
            throw cmd_exception("invalid probe, constant is too big to fit in a fixed size integer", n->get_line(), n->get_pos());
        return mk_const_probe(static_cast<int>(v.get_int64()));
    }
    else if (n->is_composite()) {
        unsigned num_children = n->get_num_children();
        if (num_children == 0)
            throw cmd_exception("invalid probe, arguments expected", n->get_line(), n->get_pos());
        sexpr * head = n->get_child(0);
        if (!head->is_symbol())
            throw cmd_exception("invalid probe, symbol expected", n->get_line(), n->get_pos());
        symbol const & p_name = head->get_symbol();

        if (p_name == "=")
            return mk_eq_probe(ctx, n);
        else if (p_name == "<=")
            return mk_le_probe(ctx, n);
        else if (p_name == ">=")
            return mk_ge_probe(ctx, n);
        else if (p_name == "<")
            return mk_lt_probe(ctx, n);
        else if (p_name == ">")
            return mk_gt_probe(ctx, n);
        else if (p_name == "and")
            return mk_and_probe(ctx, n);
        else if (p_name == "or")
            return mk_or_probe(ctx, n);
        else if (p_name == "=>" || p_name == "implies")
            return mk_implies_probe(ctx, n);
        else if (p_name == "not")
            return mk_not_probe(ctx, n);
        else if (p_name == "*")
            return mk_mul_probe(ctx, n);
        else if (p_name == "+")
            return mk_add_probe(ctx, n);
        else if (p_name == "-")
            return mk_sub_probe(ctx, n);
        else if (p_name == "/")
            return mk_div_probe(ctx, n);
        else
            throw cmd_exception("invalid probe, unknown probe expression ", p_name, n->get_line(), n->get_pos());
    }
    else {
        throw cmd_exception("invalid probe, unexpected input", n->get_line(), n->get_pos());
    }
}

