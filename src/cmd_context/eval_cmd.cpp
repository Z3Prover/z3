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
#include"cmd_context.h"
#include"model_evaluator.h"
#include"parametric_cmd.h"
#include"scoped_timer.h"
#include"scoped_ctrl_c.h"
#include"cancel_eh.h"

class eval_cmd : public parametric_cmd {
    expr *                   m_target;
    symbol                   m_last; 
public:
    eval_cmd():parametric_cmd("eval") {}

    virtual char const * get_usage() const { return "<term> (<keyword> <value>)*"; }
    
    virtual char const * get_main_descr() const { 
        return "evaluate the given term in the current model.";
    }

    virtual void init_pdescrs(cmd_context & ctx, param_descrs & p) {
        model_evaluator::get_param_descrs(p);
        insert_timeout(p);
        p.insert("model_index", CPK_UINT, "(default: 0) index of model from box optimization objective");
    }

    virtual void prepare(cmd_context & ctx) { 
        parametric_cmd::prepare(ctx);
        m_target = 0; 
    }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        if (m_target == 0) return CPK_EXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }

    virtual void set_next_arg(cmd_context & ctx, expr * arg) {
        m_target = arg;
    }

    virtual void execute(cmd_context & ctx) {
        if (!ctx.is_model_available())
            throw cmd_exception("model is not available");
        model_ref md;
        unsigned index = m_params.get_uint("model_index", 0);
        check_sat_result * last_result = ctx.get_check_sat_result();
        SASSERT(last_result);
        if (index == 0 || !ctx.get_opt()) {
            last_result->get_model(md);
        }
        else {
            ctx.get_opt()->get_box_model(md, index);
        }
        expr_ref r(ctx.m());
        unsigned timeout = m_params.get_uint("timeout", UINT_MAX);
        unsigned rlimit  = m_params.get_uint("rlimit", 0);
        model_evaluator ev(*(md.get()), m_params);
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
