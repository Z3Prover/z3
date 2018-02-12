/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    simplify_cmd.cpp

Abstract:
    SMT2 front-end 'simplify' command.

Author:

    Leonardo (leonardo) 2011-04-20

Notes:

--*/
#include "cmd_context/cmd_context.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/shared_occs.h"
#include "ast/ast_smt_pp.h"
#include "ast/for_each_expr.h"
#include "cmd_context/parametric_cmd.h"
#include "util/scoped_timer.h"
#include "util/scoped_ctrl_c.h"
#include "util/cancel_eh.h"
#include "ast/rewriter/seq_rewriter.h"
#include<iomanip>

class simplify_cmd : public parametric_cmd {

    class th_solver : public expr_solver {
        cmd_context& m_ctx;
        params_ref   m_params;
        ref<solver> m_solver;
    public:
        th_solver(cmd_context& ctx): m_ctx(ctx) {}
        
        lbool check_sat(expr* e) override {
            if (!m_solver) {
                m_solver = m_ctx.get_solver_factory()(m_ctx.m(), m_params, false, true, false, symbol::null);
            }
            m_solver->push();
            m_solver->assert_expr(e);
            lbool r = m_solver->check_sat(0,nullptr);
            m_solver->pop(1);
            return r;
        }
    };

    expr *                   m_target;
public:
    simplify_cmd(char const * name = "simplify"):parametric_cmd(name) {}

    char const * get_usage() const override { return "<term> (<keyword> <value>)*"; }

    char const * get_main_descr() const override {
        return "simplify the given term using builtin theory simplification rules.";
    }
    
    void init_pdescrs(cmd_context & ctx, param_descrs & p) override {
        th_rewriter::get_param_descrs(p);
        insert_timeout(p);
        p.insert("print", CPK_BOOL, "(default: true)  print the simplified term.");
        p.insert("print_proofs", CPK_BOOL, "(default: false) print a proof showing the original term is equal to the resultant one.");
        p.insert("print_statistics", CPK_BOOL, "(default: false) print statistics.");
    }
    
    ~simplify_cmd() override {
    }
    
    void prepare(cmd_context & ctx) override {
        parametric_cmd::prepare(ctx);
        m_target   = nullptr;
    }

    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override {
        if (m_target == nullptr) return CPK_EXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }
    
    void set_next_arg(cmd_context & ctx, expr * arg) override {
        m_target = arg;
    }
    
    void execute(cmd_context & ctx) override {
        if (m_target == nullptr)
            throw cmd_exception("invalid simplify command, argument expected");
        expr_ref r(ctx.m());
        proof_ref pr(ctx.m());
        if (m_params.get_bool("som", false))
            m_params.set_bool("flat", true);
        th_rewriter s(ctx.m(), m_params);
        th_solver solver(ctx);
        s.set_solver(alloc(th_solver, ctx));
        unsigned cache_sz;
        unsigned num_steps = 0;
        unsigned timeout   = m_params.get_uint("timeout", UINT_MAX);
        unsigned rlimit    = m_params.get_uint("rlimit", UINT_MAX);        
        bool failed = false;
        cancel_eh<reslimit> eh(ctx.m().limit());
        { 
            scoped_rlimit _rlimit(ctx.m().limit(), rlimit);
            scoped_ctrl_c ctrlc(eh);
            scoped_timer timer(timeout, &eh);
            cmd_context::scoped_watch sw(ctx);
            try {
                s(m_target, r, pr);
            }
            catch (z3_error & ex) {
                throw ex;
            }
            catch (z3_exception & ex) {
                ctx.regular_stream() << "(error \"simplifier failed: " << ex.msg() << "\")" << std::endl;
                failed = true;
                r = m_target;
            }
            cache_sz  = s.get_cache_size();
            num_steps = s.get_num_steps();
            s.cleanup();
        }
        if (m_params.get_bool("print", true)) {
            ctx.display(ctx.regular_stream(), r);
            ctx.regular_stream() << std::endl; 
        }
        if (!failed && m_params.get_bool("print_proofs", false)) {
            ast_smt_pp pp(ctx.m());
            pp.set_logic(ctx.get_logic());
            pp.display_expr_smt2(ctx.regular_stream(), pr.get());
            ctx.regular_stream() << std::endl;
        }
        if (m_params.get_bool("print_statistics", false)) {
            shared_occs s1(ctx.m());
            if (!failed)
                s1(r);
            unsigned long long max_mem = memory::get_max_used_memory();
            unsigned long long mem = memory::get_allocation_size();
            ctx.regular_stream() << "(:time " << std::fixed << std::setprecision(2) << ctx.get_seconds() << " :num-steps " << num_steps
                                 << " :memory " << std::fixed << std::setprecision(2) << static_cast<double>(mem)/static_cast<double>(1024*1024)
                                 << " :max-memory " << std::fixed << std::setprecision(2) << static_cast<double>(max_mem)/static_cast<double>(1024*1024)
                                 << " :cache-size: " << cache_sz
                                 << " :num-nodes-before " << get_num_exprs(m_target);
            if (!failed)
                ctx.regular_stream() << " :num-shared " << s1.num_shared() << " :num-nodes " << get_num_exprs(r);
            ctx.regular_stream() << ")" << std::endl;
        }
    }
};


void install_simplify_cmd(cmd_context & ctx, char const * cmd_name) {
    ctx.insert(alloc(simplify_cmd, cmd_name));
}
