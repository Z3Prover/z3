/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    eval_cmd.cpp

Abstract:

    eval_cmd

Author:

    Leonardo (leonardo) 2011-04-30

Notes:

--*/
#include "cmd_context/cmd_context.h"
#include "model/model_evaluator.h"
#include "cmd_context/parametric_cmd.h"
#include "util/scoped_timer.h"
#include "util/scoped_ctrl_c.h"
#include "util/cancel_eh.h"

class eval_cmd : public parametric_cmd {
    expr *                   m_target;
    symbol                   m_last; 
public:
    eval_cmd():parametric_cmd("eval") {}

    char const * get_usage() const override { return "<term> (<keyword> <value>)*"; }
    
    char const * get_main_descr() const override {
        return "evaluate the given term in the current model.";
    }

    void init_pdescrs(cmd_context & ctx, param_descrs & p) override {
        model_evaluator::get_param_descrs(p);
        insert_timeout(p);
        p.insert("model_index", CPK_UINT, "(default: 0) index of model from box optimization objective");
    }

    void prepare(cmd_context & ctx) override {
        parametric_cmd::prepare(ctx);
        m_target = nullptr;
    }

    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override {
        if (m_target == nullptr) return CPK_EXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }

    void set_next_arg(cmd_context & ctx, expr * arg) override {
        m_target = arg;
    }

    void execute(cmd_context & ctx) override {
        model_ref md;
        if (!ctx.is_model_available(md))
            throw cmd_exception("model is not available");
        if (!m_target)
            throw cmd_exception("no arguments passed to eval");
        unsigned index = m_params.get_uint("model_index", 0);
        if (index == 0 || !ctx.get_opt()) {
            // already have model.
        }
        else {
            ctx.get_opt()->get_box_model(md, index);
        }
        expr_ref r(ctx.m());
        unsigned timeout = m_params.get_uint("timeout", UINT_MAX);
        unsigned rlimit  = m_params.get_uint("rlimit", 0);
        // md->compress();
        model_evaluator ev(*(md.get()), m_params);
        ev.set_solver(alloc(th_solver, ctx));
        cancel_eh<reslimit> eh(ctx.m().limit());
        { 
            scoped_ctrl_c ctrlc(eh);
            scoped_timer timer(timeout, &eh);
            scoped_rlimit _rlimit(ctx.m().limit(), rlimit);
            cmd_context::scoped_watch sw(ctx);
            try {
                ev(m_target, r);
            }
            catch (model_evaluator_exception & ex) {
                ctx.regular_stream() << "(error \"evaluator failed: " << ex.msg() << "\")" << std::endl;
                return;
            }
        }
        ctx.display(ctx.regular_stream(), r.get());
        ctx.regular_stream() << std::endl;
    }
};

void install_eval_cmd(cmd_context & ctx) {
    ctx.insert(alloc(eval_cmd));
}
