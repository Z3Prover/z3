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
#include"dl_register_engine.h"
#include"dl_decl_plugin.h"
#include"dl_instruction.h"
#include"dl_compiler.h"
#include"dl_rule.h"
#include"ast_pp.h"
#include"parametric_cmd.h"
#include"cancel_eh.h"
#include"scoped_ctrl_c.h"
#include"scoped_timer.h"
#include"trail.h"
#include"fixedpoint_params.hpp"
#include<iomanip>


struct dl_context {
    smt_params                    m_fparams;
    params_ref                    m_params_ref;
    fixedpoint_params             m_params; 
    cmd_context &                 m_cmd;
    datalog::register_engine      m_register_engine;
    dl_collected_cmds*            m_collected_cmds;
    unsigned                      m_ref_count;
    datalog::dl_decl_plugin*      m_decl_plugin;
    scoped_ptr<datalog::context>  m_context; 
    trail_stack<dl_context>       m_trail;

    fixedpoint_params const& get_params() { 
        init();
        return m_context->get_params();
    }

    dl_context(cmd_context & ctx, dl_collected_cmds* collected_cmds):
        m_params(m_params_ref),
        m_cmd(ctx),
        m_collected_cmds(collected_cmds),
        m_ref_count(0),
        m_decl_plugin(0),
        m_trail(*this) {}
    
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
            m_context = alloc(datalog::context, m, m_register_engine, m_fparams, m_params_ref);
        }
        if (!m_decl_plugin) {
            symbol name("datalog_relation");
            if (m.has_plugin(name)) {
                m_decl_plugin = static_cast<datalog::dl_decl_plugin*>(m_cmd.m().get_plugin(m.mk_family_id(name)));
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

    void register_predicate(func_decl* pred, unsigned num_kinds, symbol const* kinds) {
        if (m_collected_cmds) {
            m_collected_cmds->m_rels.push_back(pred);
            m_trail.push(push_back_vector<dl_context, func_decl_ref_vector>(m_collected_cmds->m_rels));
        }
        dlctx().register_predicate(pred, false);
        dlctx().set_predicate_representation(pred, num_kinds, kinds);        
    }
    
    void add_rule(expr * rule, symbol const& name, unsigned bound) {
        init();
        if (m_collected_cmds) {
            expr_ref rl = m_context->bind_vars(rule, true);
            m_collected_cmds->m_rules.push_back(rl);
            m_collected_cmds->m_names.push_back(name);
            m_trail.push(push_back_vector<dl_context, expr_ref_vector>(m_collected_cmds->m_rules));
            m_trail.push(push_back_vector<dl_context, svector<symbol> >(m_collected_cmds->m_names));
        }
        else {
        m_context->add_rule(rule, name, bound);
        }
    }    

    bool collect_query(expr* q) {
        if (m_collected_cmds) {
            expr_ref qr = m_context->bind_vars(q, false);
            m_collected_cmds->m_queries.push_back(qr);
            m_trail.push(push_back_vector<dl_context, expr_ref_vector>(m_collected_cmds->m_queries));
            return true;
        }        
        else {
            return false;
        }
    }

    void push() {
        m_trail.push_scope();
        dlctx().push();
    }

    void pop() {
        m_trail.pop_scope(1);
        dlctx().pop();
    }
    
    datalog::context & dlctx() {
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
    unsigned     m_bound;
public:
    dl_rule_cmd(dl_context * dl_ctx):
        cmd("rule"),
        m_dl_ctx(dl_ctx),       
        m_arg_idx(0),
        m_t(0),
        m_bound(UINT_MAX) {}
    virtual char const * get_usage() const { return "(forall (q) (=> (and body) head)) :optional-name :optional-recursion-bound"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "add a Horn rule."; }
    virtual unsigned get_arity() const { return VAR_ARITY; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { 
        switch(m_arg_idx) {
        case 0: return CPK_EXPR;
        case 1: return CPK_SYMBOL;
        case 2: return CPK_UINT;
        default: return CPK_SYMBOL;
        }
    }
    virtual void set_next_arg(cmd_context & ctx, expr * t) {
        m_t = t;
        m_arg_idx++;
    }
    virtual void set_next_arg(cmd_context & ctx, symbol const & s) {
        m_name = s;
        m_arg_idx++;
    }
    virtual void set_next_arg(cmd_context & ctx, unsigned bound) {
        m_bound = bound;
        m_arg_idx++;
    }
    virtual void reset(cmd_context & ctx) { m_dl_ctx->reset(); prepare(ctx); }
    virtual void prepare(cmd_context& ctx) { m_arg_idx = 0; m_name = symbol::null; m_bound = UINT_MAX; }
    virtual void finalize(cmd_context & ctx) { 
    }
    virtual void execute(cmd_context & ctx) {
      m_dl_ctx->add_rule(m_t, m_name, m_bound);
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
        if (m_dl_ctx->collect_query(m_target)) {
            return;
        }
        datalog::context& dlctx = m_dl_ctx->dlctx();
        set_background(ctx);        
        dlctx.updt_params(m_params);
        unsigned timeout   = m_dl_ctx->get_params().timeout(); 
        cancel_eh<reslimit> eh(ctx.m().limit());
        bool query_exn = false;
        lbool status = l_undef;
        {
            IF_VERBOSE(10, verbose_stream() << "(query)\n";);
            scoped_ctrl_c ctrlc(eh);
            scoped_timer timer(timeout, &eh);
            cmd_context::scoped_watch sw(ctx);
            try {
                status = dlctx.query(m_target);
            }
            catch (z3_error & ex) {
                ctx.regular_stream() << "(error \"query failed: " << ex.msg() << "\")" << std::endl;
                throw ex;
            }
            catch (z3_exception& ex) {
                ctx.regular_stream() << "(error \"query failed: " << ex.msg() << "\")" << std::endl;
                query_exn = true;
            }
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
            if(dlctx.get_status() == datalog::BOUNDED){
              ctx.regular_stream() << "bounded\n";
              print_certificate(ctx);
              break;
            }
            ctx.regular_stream() << "unknown\n";
            switch(dlctx.get_status()) {
            case datalog::INPUT_ERROR:
                ctx.regular_stream() << "input error\n";
                break;
                
            case datalog::MEMOUT:
                ctx.regular_stream() << "memory bounds exceeded\n";
                break;

            case datalog::TIMEOUT:
                ctx.regular_stream() << "timeout\n";
                break;
               
            case datalog::APPROX:
                ctx.regular_stream() << "approximated relations\n";
                break;

            case datalog::OK: 
                SASSERT(query_exn);
                break;

            case datalog::CANCELED:
                ctx.regular_stream() << "canceled\n";
                dlctx.display_profile(ctx.regular_stream());
                break;

            default:
                UNREACHABLE();
                break;
            }
            break;
        }
        dlctx.cleanup();
        print_statistics(ctx);
        m_target = 0;
    }

    virtual void init_pdescrs(cmd_context & ctx, param_descrs & p) {
        m_dl_ctx->dlctx().collect_params(p);
    }
   

private:
    void set_background(cmd_context& ctx) {
        datalog::context& dlctx = m_dl_ctx->dlctx();
        ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
        ptr_vector<expr>::const_iterator end = ctx.end_assertions();
        for (; it != end; ++it) {
            dlctx.assert_expr(*it);
        }
    }

    void print_answer(cmd_context& ctx) {
        if (m_dl_ctx->get_params().print_answer()) {
            datalog::context& dlctx = m_dl_ctx->dlctx();
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
        if (m_dl_ctx->get_params().print_statistics()) {
            statistics st;
            datalog::context& dlctx = m_dl_ctx->dlctx();
            dlctx.collect_statistics(st);
            st.update("time", ctx.get_seconds());            
            st.display_smt2(ctx.regular_stream());            
        }
    }

    void print_certificate(cmd_context& ctx) {
        if (m_dl_ctx->get_params().print_certificate()) {
            datalog::context& dlctx = m_dl_ctx->dlctx();
            dlctx.display_certificate(ctx.regular_stream());
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
        m_dl_ctx->register_predicate(pred, m_kinds.size(), m_kinds.c_ptr());
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
        m_dl_ctx->dlctx().register_variable(var);
    }
};

/**
   \brief fixedpoint-push command.
*/
class dl_push_cmd : public cmd {
    ref<dl_context> m_dl_ctx;
public:
    dl_push_cmd(dl_context * dl_ctx):
      cmd("fixedpoint-push"),
      m_dl_ctx(dl_ctx)
    {}

    virtual char const * get_usage() const { return ""; }
    virtual char const * get_descr(cmd_context & ctx) const { return "push the fixedpoint context"; }
    virtual unsigned get_arity() const { return 0; }
    virtual void execute(cmd_context & ctx) {
        m_dl_ctx->push();
    }
};

/**
   \brief fixedpoint-pop command.
*/
class dl_pop_cmd : public cmd {
    ref<dl_context> m_dl_ctx;
public:
    dl_pop_cmd(dl_context * dl_ctx):
      cmd("fixedpoint-pop"),
      m_dl_ctx(dl_ctx)
    {}

    virtual char const * get_usage() const { return ""; }
    virtual char const * get_descr(cmd_context & ctx) const { return "pop the fixedpoint context"; }
    virtual unsigned get_arity() const { return 0; }
    virtual void execute(cmd_context & ctx) {
        m_dl_ctx->pop();
    }
};


static void install_dl_cmds_aux(cmd_context& ctx, dl_collected_cmds* collected_cmds) {
    dl_context * dl_ctx = alloc(dl_context, ctx, collected_cmds);
    ctx.insert(alloc(dl_rule_cmd, dl_ctx));
    ctx.insert(alloc(dl_query_cmd, dl_ctx));
    ctx.insert(alloc(dl_declare_rel_cmd, dl_ctx));
    ctx.insert(alloc(dl_declare_var_cmd, dl_ctx));
    // #ifndef _EXTERNAL_RELEASE
    // TODO: we need these!
#if 1
    ctx.insert(alloc(dl_push_cmd, dl_ctx)); // not exposed to keep command-extensions simple.
    ctx.insert(alloc(dl_pop_cmd, dl_ctx));
#endif
    // #endif
}

void install_dl_cmds(cmd_context & ctx) {
    install_dl_cmds_aux(ctx, 0);
}

void install_dl_collect_cmds(dl_collected_cmds& collected_cmds, cmd_context & ctx) {
    install_dl_cmds_aux(ctx, &collected_cmds);
}
