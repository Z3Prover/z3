#include "qe_cmd.h"
#include "qe.h"
#include "cmd_context.h"
#include "parametric_cmd.h"

class qe_cmd : public parametric_cmd {
    expr *                   m_target;
public:
    qe_cmd(char const* name = "elim-quantifiers"):parametric_cmd(name) {}
    
    virtual char const * get_usage() const { return "<term> (<keyword> <value>)*"; }

    virtual char const * get_main_descr() const { 
        return "apply quantifier elimination to the supplied expression";
    }
    
    virtual void init_pdescrs(cmd_context & ctx, param_descrs & p) {
        insert_timeout(p);
        p.insert("print", CPK_BOOL, "(default: true)  print the simplified term.");
        p.insert("print_statistics", CPK_BOOL, "(default: false) print statistics.");
    }
    
    virtual ~qe_cmd() {
    }
    
    virtual void prepare(cmd_context & ctx) { 
        parametric_cmd::prepare(ctx);
        m_target   = 0; 
    }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        if (m_target == 0) return CPK_EXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }
    
    virtual void set_next_arg(cmd_context & ctx, expr * arg) {
        m_target = arg;
    }
    
    virtual void execute(cmd_context & ctx) {
        smt_params par;
        proof_ref pr(ctx.m());
        qe::expr_quant_elim_star1 qe(ctx.m(), par);
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

