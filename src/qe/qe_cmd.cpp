
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "qe/qe_cmd.h"
#include "qe/qe.h"
#include "cmd_context/cmd_context.h"
#include "cmd_context/parametric_cmd.h"

class qe_cmd : public parametric_cmd {
    expr *                   m_target;
public:
    qe_cmd(char const* name = "elim-quantifiers"):parametric_cmd(name) {}
    
    char const * get_usage() const override { return "<term> (<keyword> <value>)*"; }

    char const * get_main_descr() const override {
        return "apply quantifier elimination to the supplied expression";
    }
    
    void init_pdescrs(cmd_context & ctx, param_descrs & p) override {
        insert_timeout(p);
        p.insert("print", CPK_BOOL, "(default: true)  print the simplified term.");
        p.insert("print_statistics", CPK_BOOL, "(default: false) print statistics.");
    }
    
    ~qe_cmd() override {
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
        proof_ref pr(ctx.m());
        qe::simplify_rewriter_star qe(ctx.m());
        expr_ref result(ctx.m());

        qe(m_target, result, pr);            

        if (m_params.get_bool("print", true)) {
            ctx.display(ctx.regular_stream(), result);
            ctx.regular_stream() << std::endl; 
        }
        if (m_params.get_bool("print_statistics", false)) {
            statistics st;
            qe.collect_statistics(st);
            st.display(ctx.regular_stream());
        }
    }

};

void install_qe_cmd(cmd_context & ctx, char const * cmd_name) {
    ctx.insert(alloc(qe_cmd, cmd_name));
}

