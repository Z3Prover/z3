/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dbg_cmds.cpp

Abstract:
    SMT2 front-end commands for debugging purposes.

Author:

    Leonardo (leonardo) 2011-04-01

Notes:

--*/
#include<iomanip>
#include"cmd_context.h"
#include"cmd_util.h"
#include"rewriter.h"
#include"shared_occs.h"
#include"for_each_expr.h"
#include"rewriter.h"
#include"bool_rewriter.h"
#include"ast_lt.h"
#include"simplify_cmd.h"
#include"ast_smt2_pp.h"
#include"bound_manager.h"
#include"used_vars.h"
#include"var_subst.h"

#ifndef _EXTERNAL_RELEASE

BINARY_SYM_CMD(get_quantifier_body_cmd, 
               "dbg-get-qbody", 
               "<symbol> <quantifier>",
               "store the body of the quantifier in the global variable <symbol>",
               CPK_EXPR,
               expr *, {
    if (!is_quantifier(arg))
        throw cmd_exception("invalid command, term must be a quantifier");
    store_expr_ref(ctx, m_sym, to_quantifier(arg)->get_expr());
});

BINARY_SYM_CMD(set_cmd, 
               "dbg-set", 
               "<symbol> <term>",
               "store <term> in the global variable <symbol>",
               CPK_EXPR,
               expr *, {
    store_expr_ref(ctx, m_sym, arg);
});


UNARY_CMD(pp_var_cmd, "dbg-pp-var", "<symbol>", "pretty print a global variable that references an AST", CPK_SYMBOL, symbol const &, {
    expr * t = get_expr_ref(ctx, arg);
    SASSERT(t != 0);
    ctx.display(ctx.regular_stream(), t);
    ctx.regular_stream() << std::endl; 
});

BINARY_SYM_CMD(shift_vars_cmd,
               "dbg-shift-vars",
               "<symbol> <uint>",
               "shift the free variables by <uint> in the term referenced by the global variable <symbol>, the result is stored in <symbol>",
               CPK_UINT,
               unsigned, {
    expr * t = get_expr_ref(ctx, m_sym);
    expr_ref r(ctx.m());
    var_shifter s(ctx.m());
    s(t, arg, r);
    store_expr_ref(ctx, m_sym, r.get());
});               

UNARY_CMD(pp_shared_cmd, "dbg-pp-shared", "<term>", "display shared subterms of the given term", CPK_EXPR, expr *, {
    shared_occs s(ctx.m());
    s(arg);
    ctx.regular_stream() << "(shared";
    shared_occs::iterator it  = s.begin_shared();
    shared_occs::iterator end = s.end_shared();
    for (; it != end; ++it) {
        expr * curr = *it;
        ctx.regular_stream() << std::endl << "  "; 
        ctx.display(ctx.regular_stream(), curr, 2);
    }
    ctx.regular_stream() << ")" << std::endl;
});

UNARY_CMD(num_shared_cmd, "dbg-num-shared", "<term>", "return the number of shared subterms", CPK_EXPR, expr *, {
    shared_occs s(ctx.m());
    s(arg);
    ctx.regular_stream() << s.num_shared() << std::endl;
});

UNARY_CMD(size_cmd, "dbg-size", "<term>", "return the size of the given term", CPK_EXPR, expr *, {
    ctx.regular_stream() << get_num_exprs(arg) << std::endl;
});

class subst_cmd : public cmd {
    unsigned         m_idx;
    expr *           m_source;
    symbol           m_target;
    ptr_vector<expr> m_subst;
public:
    subst_cmd():cmd("dbg-subst") {}
    virtual char const * get_usage() const { return "<symbol> (<symbol>*) <symbol>"; }
    virtual char const * get_descr() const { return "substitute the free variables in the AST referenced by <symbol> using the ASTs referenced by <symbol>*"; }
    virtual unsigned get_arity() const { return 3; }
    virtual void prepare(cmd_context & ctx) { m_idx = 0; m_source = 0; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        if (m_idx == 1) return CPK_SYMBOL_LIST;
        return CPK_SYMBOL;
    }
    virtual void set_next_arg(cmd_context & ctx, symbol const & s) { 
        if (m_idx == 0) {
            m_source = get_expr_ref(ctx, s);
        }
        else {
            m_target = s;
        }
        m_idx++;
    }
    virtual void set_next_arg(cmd_context & ctx, unsigned num, symbol const * s) {
        m_subst.reset();
        unsigned i = num;
        while (i > 0) {
            --i;
            m_subst.push_back(get_expr_ref(ctx, s[i]));
        }
        m_idx++;
    }
    virtual void execute(cmd_context & ctx) {
        expr_ref r(ctx.m());
        beta_reducer p(ctx.m());
        p(m_source, m_subst.size(), m_subst.c_ptr(), r);
        store_expr_ref(ctx, m_target, r.get());
    }
};

UNARY_CMD(bool_rewriter_cmd, "dbg-bool-rewriter", "<term>", "apply the Boolean rewriter to the given term", CPK_EXPR, expr *, {
    expr_ref t(ctx.m());
    params_ref p;
    p.set_bool("flat", false);
    SASSERT(p.get_bool("flat", true) == false);
    bool_rewriter_star r(ctx.m(), p);
    r(arg, t);
    ctx.display(ctx.regular_stream(), t);
    ctx.regular_stream() << std::endl; 
});

UNARY_CMD(bool_frewriter_cmd, "dbg-bool-flat-rewriter", "<term>", "apply the Boolean (flattening) rewriter to the given term", CPK_EXPR, expr *, {
    expr_ref t(ctx.m());
    { 
        params_ref p;
        p.set_bool("flat", true);
        bool_rewriter_star r(ctx.m(), p);
        r(arg, t);
    }
    ctx.display(ctx.regular_stream(), t);
    ctx.regular_stream() << std::endl; 
});

UNARY_CMD(elim_and_cmd, "dbg-elim-and", "<term>", "apply the Boolean rewriter (eliminating AND operator and flattening) to the given term", CPK_EXPR, expr *, {
    expr_ref t(ctx.m());
    { 
        params_ref p;
        p.set_bool("flat", true);
        p.set_bool("elim_and", true);
        bool_rewriter_star r(ctx.m(), p);
        r(arg, t);
    }
    ctx.display(ctx.regular_stream(), t);
    ctx.regular_stream() << std::endl; 
});

class lt_cmd : public cmd {
    expr *           m_t1;
    expr *           m_t2;
public:
    lt_cmd():cmd("dbg-lt") {}
    virtual char const * get_usage() const { return "<term> <term>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "return true if the first term is smaller than the second one in the internal Z3 total order on terms."; }
    virtual unsigned get_arity() const { return 2; }
    virtual void prepare(cmd_context & ctx) { m_t1 = 0; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_EXPR; }
    virtual void set_next_arg(cmd_context & ctx, expr * arg) {
        if (m_t1 == 0)
            m_t1 = arg;
        else
            m_t2 = arg;
    }
    virtual void execute(cmd_context & ctx) {
        bool r = lt(m_t1, m_t2);
        ctx.regular_stream() << (r ? "true" : "false") << std::endl; 
    }
};


UNARY_CMD(some_value_cmd, "dbg-some-value", "<sort>", "retrieve some value of the given sort", CPK_SORT, sort *, {
    ast_manager & m = ctx.m();
    expr_ref val(m);
    val = m.get_some_value(arg);
    ctx.display(ctx.regular_stream(), val);
    ctx.regular_stream() << std::endl;
});

void tst_params(cmd_context & ctx) {
    params_ref p1;
    params_ref p2;
    p1.set_uint("val", 100);
    p2 = p1;
    SASSERT(p2.get_uint("val", 0) == 100);
    p2.set_uint("val", 200);
    SASSERT(p2.get_uint("val", 0) == 200);
    SASSERT(p1.get_uint("val", 0) == 100);
    p2 = p1;
    SASSERT(p2.get_uint("val", 0) == 100);
    SASSERT(p1.get_uint("val", 0) == 100);
    ctx.regular_stream() << "worked" << std::endl;
}

ATOMIC_CMD(params_cmd, "dbg-params", "test parameters", tst_params(ctx););


UNARY_CMD(translator_cmd, "dbg-translator", "<term>", "test AST translator", CPK_EXPR, expr *, {
    ast_manager & m = ctx.m();
    scoped_ptr<ast_manager> m2 = alloc(ast_manager, m.proof_mode());
    ast_translation proc(m, *m2);
    expr_ref s(m);
    expr_ref t(*m2);
    s = arg;
    t = proc(s.get());
    ctx.regular_stream() << mk_ismt2_pp(s, m) << "\n--->\n" << mk_ismt2_pp(t, *m2) << std::endl;
});

UNARY_CMD(sexpr_cmd, "dbg-sexpr", "<sexpr>", "display an s-expr", CPK_SEXPR, sexpr *, {
    arg->display(ctx.regular_stream());
    ctx.regular_stream() << std::endl;
});


#define GUARDED_CODE(CODE) try { CODE } catch (z3_error & ex) { throw ex; } catch (z3_exception & ex) { ctx.regular_stream() << "(error \"" << escaped(ex.msg()) << "\")" << std::endl; }

UNARY_CMD(set_next_id, "dbg-set-next-id", "<unsigned>", "set the next expression id to be at least the given value", CPK_UINT, unsigned, {
    ctx.m().set_next_expr_id(arg);
});


UNARY_CMD(used_vars_cmd, "dbg-used-vars", "<expr>", "test used_vars functor", CPK_EXPR, expr *, {
    used_vars proc;
    if (is_quantifier(arg)) 
        arg = to_quantifier(arg)->get_expr();
    proc(arg);
    ctx.regular_stream() << "(vars";
    for (unsigned i = 0; i < proc.get_max_found_var_idx_plus_1(); i++) {
        sort * s = proc.get(i);
        ctx.regular_stream() << "\n  (" << std::left << std::setw(6) << i << " ";
        if (s != 0)
            ctx.display(ctx.regular_stream(), s, 10);
        else 
            ctx.regular_stream() << "<not-used>";
        ctx.regular_stream() << ")";
    }
    ctx.regular_stream() << ")" << std::endl;
});

UNARY_CMD(elim_unused_vars_cmd, "dbg-elim-unused-vars", "<expr>", "eliminate unused vars from a quantifier", CPK_EXPR, expr *, {
    if (!is_quantifier(arg)) {
        ctx.display(ctx.regular_stream(), arg);
        return;
    }
    expr_ref r(ctx.m());
    elim_unused_vars(ctx.m(), to_quantifier(arg), r);
    SASSERT(!is_quantifier(r) || !to_quantifier(r)->may_have_unused_vars());
    ctx.display(ctx.regular_stream(), r);
    ctx.regular_stream() << std::endl;
});

class instantiate_cmd_core : public cmd {
protected:
    quantifier *     m_q;
    ptr_vector<expr> m_args;
public:
    instantiate_cmd_core(char const * name):cmd(name) {}
    virtual char const * get_usage() const { return "<quantifier> (<symbol>*)"; }
    virtual char const * get_descr() const { return "instantiate the quantifier using the given expressions."; }
    virtual unsigned get_arity() const { return 2; }
    virtual void prepare(cmd_context & ctx) { m_q = 0; m_args.reset(); }
    
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        if (m_q == 0) return CPK_EXPR;
        else return CPK_EXPR_LIST;
    }
    
    virtual void set_next_arg(cmd_context & ctx, expr * s) {
        if (!is_quantifier(s))
            throw cmd_exception("invalid command, quantifier expected.");
        m_q = to_quantifier(s);
    }
    
    virtual void set_next_arg(cmd_context & ctx, unsigned num, expr * const * ts) {
        if (num != m_q->get_num_decls())
            throw cmd_exception("invalid command, mismatch between the number of quantified variables and the number of arguments.");
        unsigned i = num;
        while (i > 0) {
            --i;
            sort * s = ctx.m().get_sort(ts[i]);
            if (s != m_q->get_decl_sort(i)) {
                std::ostringstream buffer;
                buffer << "invalid command, sort mismatch at position " << i;
                throw cmd_exception(buffer.str());
            }
        }
        m_args.append(num, ts);
    }

    virtual void execute(cmd_context & ctx) {
        expr_ref r(ctx.m());
        instantiate(ctx.m(), m_q, m_args.c_ptr(), r);
        ctx.display(ctx.regular_stream(), r);
        ctx.regular_stream() << std::endl;
    }
};

class instantiate_cmd : public instantiate_cmd_core {
public:
    instantiate_cmd():instantiate_cmd_core("dbg-instantiate") {}
};

class instantiate_nested_cmd : public instantiate_cmd_core {
public:
    instantiate_nested_cmd():instantiate_cmd_core("dbg-instantiate-nested") {}
    
    virtual char const * get_descr() const { return "instantiate the quantifier nested in the outermost quantifier, this command is used to test the instantiation procedure with quantifiers that contain free variables."; }

    virtual void set_next_arg(cmd_context & ctx, expr * s) {
        instantiate_cmd_core::set_next_arg(ctx, s);
        if (!is_quantifier(m_q->get_expr()))
            throw cmd_exception("invalid command, nested quantifier expected");
        m_q = to_quantifier(m_q->get_expr());
    }
};

#endif

void install_dbg_cmds(cmd_context & ctx) {
#ifndef _EXTERNAL_RELEASE
    ctx.insert(alloc(get_quantifier_body_cmd));
    ctx.insert(alloc(set_cmd));
    ctx.insert(alloc(pp_var_cmd));
    ctx.insert(alloc(shift_vars_cmd));
    ctx.insert(alloc(pp_shared_cmd));
    ctx.insert(alloc(num_shared_cmd));
    ctx.insert(alloc(size_cmd));
    ctx.insert(alloc(subst_cmd));
    ctx.insert(alloc(bool_rewriter_cmd));
    ctx.insert(alloc(bool_frewriter_cmd));
    ctx.insert(alloc(elim_and_cmd));
    install_simplify_cmd(ctx, "dbg-th-rewriter");
    ctx.insert(alloc(lt_cmd));
    ctx.insert(alloc(some_value_cmd));
    ctx.insert(alloc(params_cmd));
    ctx.insert(alloc(translator_cmd));
    ctx.insert(alloc(sexpr_cmd));
    ctx.insert(alloc(used_vars_cmd));
    ctx.insert(alloc(elim_unused_vars_cmd));
    ctx.insert(alloc(instantiate_cmd));
    ctx.insert(alloc(instantiate_nested_cmd));
    ctx.insert(alloc(set_next_id));
#endif
}
