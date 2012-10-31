/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dl_cmds.cpp

Abstract:
    Datalog commands for SMT2 front-end.

Author:

    Leonardo (leonardo) 2011-03-28

Notes:

--*/
#include"cmd_context.h"
#include"dl_cmds.h"
#include"dl_external_relation.h"
#include"dl_context.h"
#include"dl_decl_plugin.h"
#include"dl_instruction.h"
#include"dl_compiler.h"
#include"dl_rule.h"
#include"ast_pp.h"
#include"parametric_cmd.h"
#include"cancel_eh.h"
#include"scoped_ctrl_c.h"
#include"scoped_timer.h"
#include<iomanip>


class dl_context {
    cmd_context &                 m_cmd;
    unsigned                      m_ref_count;
    datalog::dl_decl_plugin*      m_decl_plugin;
    scoped_ptr<datalog::context>  m_context;    

public:
    dl_context(cmd_context & ctx):
        m_cmd(ctx),
        m_ref_count(0),
        m_decl_plugin(0) {}
    
    void inc_ref() {
        ++m_ref_count;
    }
    
    void dec_ref() {
        --m_ref_count;
        if (0 == m_ref_count) {
            dealloc(this);
        }
    }
    
    void init() {
        ast_manager& m = m_cmd.m();
        if (!m_context) {
            m_context = alloc(datalog::context, m, m_cmd.params()); 
        }
        if (!m_decl_plugin) {
            symbol name("datalog_relation");
            if (m.has_plugin(name)) {
                m_decl_plugin = static_cast<datalog::dl_decl_plugin*>(m_cmd.m().get_plugin(m.get_family_id(name)));
            }
            else {
                m_decl_plugin = alloc(datalog::dl_decl_plugin);
                m.register_plugin(symbol("datalog_relation"), m_decl_plugin);
            }        
        }
    }
    
    void reset() {
        m_context = 0;
    }
    
    void add_rule(expr * rule, symbol const& name) {
        init();
        std::string error_msg;
        m_context->add_rule(rule, name);
    }    
    
    datalog::context & get_dl_context() {
        init();
        return *m_context;
    }
};


/**
   \brief rule command. It is also the owner of dl_context object.
*/
class dl_rule_cmd : public cmd {
    ref<dl_context> m_dl_ctx;
    mutable unsigned     m_arg_idx;
    expr*        m_t;
    symbol       m_name;
public:
    dl_rule_cmd(dl_context * dl_ctx):
        cmd("rule"),
        m_dl_ctx(dl_ctx),       
        m_arg_idx(0),
        m_t(0) {}
    virtual char const * get_usage() const { return "(forall (q) (=> (and body) head)) :optional-name"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "add a Horn rule."; }
    virtual unsigned get_arity() const { return VAR_ARITY; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { 
        switch(m_arg_idx) {
        case 0: return CPK_EXPR;
        case 1: return CPK_SYMBOL;
        default: return CPK_SYMBOL;
        }
    }
    virtual void set_next_arg(cmd_context & ctx, expr * t) {
        m_t = t;
        m_arg_idx++;
    }
    virtual void set_next_arg(cmd_context & ctx, symbol const & s) {
        m_name = s;
    }
    virtual void reset(cmd_context & ctx) { m_dl_ctx->reset(); prepare(ctx); }
    virtual void prepare(cmd_context& ctx) { m_arg_idx = 0; m_name = symbol::null; }
    virtual void finalize(cmd_context & ctx) { 
    }
    virtual void execute(cmd_context & ctx) {
        m_dl_ctx->add_rule(m_t, m_name);
    }
};

class dl_query_cmd : public parametric_cmd {
    ref<dl_context> m_dl_ctx;
    expr* m_target;
public:
    dl_query_cmd(dl_context * dl_ctx):
        parametric_cmd("query"),
        m_dl_ctx(dl_ctx),
        m_target(0) {
    }
    virtual char const * get_usage() const { return "(exists (q) (and body))"; }
    virtual char const * get_main_descr() const { 
        return "pose a query based on the Horn rules."; 
    }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { 
        if (m_target == 0) return CPK_EXPR;
        return parametric_cmd::next_arg_kind(ctx);
    }

    virtual void set_next_arg(cmd_context & ctx, expr * t) {
        m_target = t;
    }

    virtual void prepare(cmd_context & ctx) { 
        parametric_cmd::prepare(ctx);
        m_target   = 0; 
    }

    virtual void execute(cmd_context& ctx) {
        if (m_target == 0) {
            throw cmd_exception("invalid query command, argument expected");
        }
        datalog::context& dlctx = m_dl_ctx->get_dl_context();
        set_background(ctx);        
        dlctx.updt_params(m_params);
        unsigned timeout   = m_params.get_uint(":timeout", UINT_MAX);
        cancel_eh<datalog::context> eh(dlctx);
        lbool status = l_undef;
        {
            scoped_ctrl_c ctrlc(eh);
            scoped_timer timer(timeout, &eh);
            cmd_context::scoped_watch sw(ctx);
            try {
                status = dlctx.query(m_target);
            }
            catch (z3_error & ex) {
                throw ex;
            }
            catch (z3_exception& ex) {
                ctx.regular_stream() << "(error \"query failed: " << ex.msg() << "\")" << std::endl;
            }
            dlctx.cleanup();
        }
        switch (status) {
        case l_false:
            ctx.regular_stream() << "unsat\n";
            print_certificate(ctx);
            break;
        case l_true: 
            ctx.regular_stream() << "sat\n";
            print_answer(ctx);
            print_certificate(ctx);
            break;
        case l_undef: 
            ctx.regular_stream() << "unknown\n";
            switch(dlctx.get_status()) {
            case datalog::INPUT_ERROR:
                break;
                
            case datalog::MEMOUT:
                ctx.regular_stream() << "memory bounds exceeded\n";
                break;

            case datalog::TIMEOUT:
                ctx.regular_stream() << "timeout\n";
                break;
                
            case datalog::OK: 
                break;
            default:
                UNREACHABLE();
            }
            break;
        }
        print_statistics(ctx);
        m_target = 0;
    }

    virtual void init_pdescrs(cmd_context & ctx, param_descrs & p) {
        m_dl_ctx->get_dl_context().collect_params(p);
        insert_timeout(p);
        p.insert(":print-answer", CPK_BOOL, "(default: false) print answer instance(s) to query.");
        p.insert(":print-certificate", CPK_BOOL, "(default: false) print certificate for reachability or non-reachability.");
        p.insert(":print-statistics",  CPK_BOOL, "(default: false) print statistics.");
    }
   

private:
    void set_background(cmd_context& ctx) {
        datalog::context& dlctx = m_dl_ctx->get_dl_context();
        ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
        ptr_vector<expr>::const_iterator end = ctx.end_assertions();
        for (; it != end; ++it) {
            dlctx.assert_expr(*it);
        }
    }

    void print_answer(cmd_context& ctx) {
        if (m_params.get_bool(":print-answer", false)) {
            datalog::context& dlctx = m_dl_ctx->get_dl_context();
            ast_manager& m = ctx.m();
            expr_ref query_result(dlctx.get_answer_as_formula(), m);
            sbuffer<symbol> var_names;
            unsigned num_decls = 0;
            if (is_quantifier(m_target)) {
                num_decls = to_quantifier(m_target)->get_num_decls();
            }
            ctx.display(ctx.regular_stream(), query_result, 0, num_decls, "X", var_names);
            ctx.regular_stream() << std::endl;
        }
    }

    void print_statistics(cmd_context& ctx) {
        if (m_params.get_bool(":print-statistics", false)) {
            statistics st;
            datalog::context& dlctx = m_dl_ctx->get_dl_context();
            unsigned long long max_mem = memory::get_max_used_memory();
            unsigned long long mem = memory::get_allocation_size();
            dlctx.collect_statistics(st);
            st.update("time", ctx.get_seconds());            
            st.update("memory", static_cast<double>(mem)/static_cast<double>(1024*1024));
            st.update("max-memory", static_cast<double>(max_mem)/static_cast<double>(1024*1024));
            st.display_smt2(ctx.regular_stream());            
        }
    }

    void print_certificate(cmd_context& ctx) {
        if (m_params.get_bool(":print-certificate", false)) {
            datalog::context& dlctx = m_dl_ctx->get_dl_context();
            if (!dlctx.display_certificate(ctx.regular_stream())) {
                throw cmd_exception("certificates are not supported for selected DL_ENGINE");
            }
            ctx.regular_stream() << "\n";
        }
    }
};

class dl_declare_rel_cmd : public cmd {
    ref<dl_context>    m_dl_ctx;
    unsigned         m_arg_idx;
    mutable unsigned m_query_arg_idx;
    symbol           m_rel_name;
    scoped_ptr<sort_ref_vector>  m_domain;
    svector<symbol>  m_kinds;

    void ensure_domain(cmd_context& ctx) {
        if (!m_domain) m_domain = alloc(sort_ref_vector, ctx.m());
    }
public:
    dl_declare_rel_cmd(dl_context * dl_ctx):
        cmd("declare-rel"),
        m_dl_ctx(dl_ctx),
        m_domain(0) {}

    virtual char const * get_usage() const { return "<symbol> (<arg1 sort> ...) <representation>*"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "declare new relation"; }
    virtual unsigned get_arity() const { return VAR_ARITY; }

    virtual void prepare(cmd_context & ctx) {
        m_arg_idx = 0; 
        m_query_arg_idx = 0; 
        m_domain = 0;
        m_kinds.reset();
    }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { 
        switch(m_query_arg_idx++) {
        case 0: return CPK_SYMBOL;     // relation name
        case 1: return CPK_SORT_LIST;  // arguments
        default: return CPK_SYMBOL;    // optional representation specification
        }
    }
    virtual void set_next_arg(cmd_context & ctx, unsigned num, sort * const * slist) {
        ensure_domain(ctx);
        m_domain->append(num, slist);
        m_arg_idx++;
    }
    virtual void set_next_arg(cmd_context & ctx, symbol const & s) {
        if(m_arg_idx==0) {
            m_rel_name = s;
        }
        else {
            SASSERT(m_arg_idx>1);
            m_kinds.push_back(s);
        }
        m_arg_idx++;
    }
    virtual void execute(cmd_context & ctx) {
        if(m_arg_idx<2) {
            throw cmd_exception("at least 2 arguments expected");
        }
        ensure_domain(ctx);
        ast_manager& m = ctx.m();

        func_decl_ref pred(
            m.mk_func_decl(m_rel_name, m_domain->size(), m_domain->c_ptr(), m.mk_bool_sort()), m);
        ctx.insert(pred);
        datalog::context& dctx = m_dl_ctx->get_dl_context();
        dctx.register_predicate(pred, false);
        if(!m_kinds.empty()) {
            dctx.set_predicate_representation(pred, m_kinds.size(), m_kinds.c_ptr());
        }
        m_domain = 0;
    }

};

class dl_declare_var_cmd : public cmd {
    unsigned m_arg_idx;
    symbol   m_var_name;
    sort*    m_var_sort;
    ref<dl_context>   m_dl_ctx;
public:
    dl_declare_var_cmd(dl_context* dl_ctx):
        cmd("declare-var"),
        m_arg_idx(0),
        m_dl_ctx(dl_ctx)
    {}
    
    virtual char const * get_usage() const { return "<symbol> <sort>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "declare constant as variable"; }
    virtual unsigned get_arity() const { return 2; }

    virtual void prepare(cmd_context & ctx) {
        m_arg_idx = 0; 
    }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { 
        SASSERT(m_arg_idx <= 1);
        if (m_arg_idx == 0) {
            return CPK_SYMBOL;  
        }
        return CPK_SORT; 
    }

    virtual void set_next_arg(cmd_context & ctx, sort* s) {
        m_var_sort = s;
        ++m_arg_idx;
    }

    virtual void set_next_arg(cmd_context & ctx, symbol const & s) {
        m_var_name = s;   
        ++m_arg_idx;
    }

    virtual void execute(cmd_context & ctx) {
        ast_manager& m = ctx.m();
        func_decl_ref var(m.mk_func_decl(m_var_name, 0, static_cast<sort*const*>(0), m_var_sort), m);
        ctx.insert(var);
        m_dl_ctx->get_dl_context().register_variable(var);
    }

};

class dl_push_cmd : public cmd {
    ref<dl_context>   m_ctx;    
public:
    dl_push_cmd(dl_context* ctx):
        cmd("fixedpoint-push"),
        m_ctx(ctx)
    {}

    virtual char const * get_usage() const { return ""; }
    virtual char const * get_descr(cmd_context & ctx) const { return "push context on the fixedpoint engine"; }
        
    virtual void execute(cmd_context& ctx) {
        m_ctx->get_dl_context().push();
    }
};

class dl_pop_cmd : public cmd {
    ref<dl_context>   m_ctx;    
public:
    dl_pop_cmd(dl_context* ctx):
        cmd("fixedpoint-pop"),
        m_ctx(ctx)
    {}

    virtual char const * get_usage() const { return ""; }
    virtual char const * get_descr(cmd_context & ctx) const { return "pop context on the fixedpoint engine"; }
        
    virtual void execute(cmd_context& ctx) {
        m_ctx->get_dl_context().pop();
    }
};



void install_dl_cmds(cmd_context & ctx) {
    dl_context * dl_ctx = alloc(dl_context, ctx);
    ctx.insert(alloc(dl_rule_cmd, dl_ctx));
    ctx.insert(alloc(dl_query_cmd, dl_ctx));
    ctx.insert(alloc(dl_declare_rel_cmd, dl_ctx));
    ctx.insert(alloc(dl_declare_var_cmd, dl_ctx));
    PRIVATE_PARAMS(ctx.insert(alloc(dl_push_cmd, dl_ctx));); // not exposed to keep command-extensions simple.
    PRIVATE_PARAMS(ctx.insert(alloc(dl_pop_cmd, dl_ctx)););
}

