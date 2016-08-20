/*++
  Copyright (c) 2013 Microsoft Corporation

  Module Name:

  interpolant_cmds.cpp

  Abstract:
  Commands for interpolation.

  Author:

  Leonardo (leonardo) 2011-12-23

  Notes:

  --*/
#include<sstream>
#include"cmd_context.h"
#include"cmd_util.h"
#include"scoped_timer.h"
#include"scoped_ctrl_c.h"
#include"cancel_eh.h"
#include"ast_pp.h"
#include"ast_smt_pp.h"
#include"ast_smt2_pp.h"
#include"parametric_cmd.h"
#include"mpq.h"
#include"expr2var.h"
#include"pp.h"
#include"iz3interp.h"
#include"iz3checker.h"
#include"iz3profiling.h"
#include"interp_params.hpp"
#include"scoped_proof.h"

static void show_interpolant_and_maybe_check(cmd_context & ctx,
                                             ptr_vector<ast> &cnsts,
                                             expr *t, 
                                             ptr_vector<ast> &interps,
                                             params_ref &m_params,
                                             bool check)
{
  
    if (m_params.get_bool("som", false))
        m_params.set_bool("flat", true);
    th_rewriter s(ctx.m(), m_params);
  
    for(unsigned i = 0; i < interps.size(); i++){

        expr_ref r(ctx.m());
        proof_ref pr(ctx.m());
        s(to_expr(interps[i]),r,pr);

        ctx.regular_stream()  << mk_pp(r.get(), ctx.m()) << std::endl;
#if 0
        ast_smt_pp pp(ctx.m());
        pp.set_logic(ctx.get_logic().str().c_str());
        pp.display_smt2(ctx.regular_stream(), to_expr(interps[i]));
        ctx.regular_stream() << std::endl;
#endif
    }

    s.cleanup();

    // verify, for the paranoid...
    if(check || interp_params(m_params).check()){
        std::ostringstream err;
        ast_manager &_m = ctx.m();

        // need a solver -- make one here FIXME is this right?
        bool proofs_enabled, models_enabled, unsat_core_enabled;
        params_ref p;
        ctx.params().get_solver_params(_m, p, proofs_enabled, models_enabled, unsat_core_enabled);
        scoped_ptr<solver> sp = (ctx.get_solver_factory())(_m, p, false, true, false, ctx.get_logic());

        if(iz3check(_m,sp.get(),err,cnsts,t,interps))
            ctx.regular_stream() << "correct\n";
        else 
            ctx.regular_stream() << "incorrect: " << err.str().c_str() << "\n";
    }

    for(unsigned i = 0; i < interps.size(); i++){
        ctx.m().dec_ref(interps[i]);
    }

    interp_params itp_params(m_params);
    if(itp_params.profile())
        profiling::print(ctx.regular_stream());

}

static void check_can_interpolate(cmd_context & ctx){
    if (!ctx.produce_interpolants())
        throw cmd_exception("interpolation is not enabled, use command (set-option :produce-interpolants true)");
}


static void get_interpolant_and_maybe_check(cmd_context & ctx, expr * t, params_ref &m_params, bool check) {

    check_can_interpolate(ctx);

    // get the proof, if there is one

    if (!ctx.has_manager() ||
        ctx.cs_state() != cmd_context::css_unsat)
        throw cmd_exception("proof is not available");
    expr_ref pr(ctx.m());
    pr = ctx.get_check_sat_result()->get_proof();
    if (pr == 0)
        throw cmd_exception("proof is not available");

    // get the assertions from the context

    ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
    ptr_vector<expr>::const_iterator end = ctx.end_assertions();
    ptr_vector<ast> cnsts((unsigned)(end - it));
    for (int i = 0; it != end; ++it, ++i)
        cnsts[i] = *it;
    
    // compute an interpolant
  
    ptr_vector<ast> interps;
 
    try {
        iz3interpolate(ctx.m(),pr.get(),cnsts,t,interps,0);
    }
    catch (iz3_bad_tree &) {
        throw cmd_exception("interpolation pattern contains non-asserted formula");
    }
    catch (iz3_incompleteness &) {
        throw cmd_exception("incompleteness in interpolator");
    }

    show_interpolant_and_maybe_check(ctx, cnsts, t, interps, m_params, check);
}

static void get_interpolant(cmd_context & ctx, expr * t, params_ref &m_params) {
    get_interpolant_and_maybe_check(ctx,t,m_params,false);
}

#if 0
static void get_and_check_interpolant(cmd_context & ctx, params_ref &m_params, expr * t) {
    get_interpolant_and_maybe_check(ctx,t,m_params,true);
}
#endif

static void compute_interpolant_and_maybe_check(cmd_context & ctx, expr * t, params_ref &m_params, bool check){
    
    // create a fresh solver suitable for interpolation
    bool proofs_enabled, models_enabled, unsat_core_enabled;
    params_ref p;
    ast_manager &_m = ctx.m();
    // TODO: the following is a HACK to enable proofs in the old smt solver
    // When we stop using that solver, this hack can be removed
    scoped_proof_mode spm(_m,PGM_FINE);
    ctx.params().get_solver_params(_m, p, proofs_enabled, models_enabled, unsat_core_enabled);
    p.set_bool("proof", true);
    scoped_ptr<solver> sp = (ctx.get_interpolating_solver_factory())(_m, p, true, models_enabled, false, ctx.get_logic());

    ptr_vector<ast> cnsts;
    ptr_vector<ast> interps;
    model_ref m;
  
    // compute an interpolant
  
    lbool res;
    try {
        res = iz3interpolate(_m, *sp.get(), t, cnsts, interps, m, 0);
    }
    catch (iz3_incompleteness &) {
        throw cmd_exception("incompleteness in interpolator");
    }

    switch(res){
    case l_false:
        ctx.regular_stream() << "unsat\n";
        show_interpolant_and_maybe_check(ctx, cnsts, t, interps, m_params, check);
        break;

    case l_true:
        ctx.regular_stream() << "sat\n";
        // TODO: how to return the model to the context, if it exists?
        break;

    case l_undef:
        ctx.regular_stream() << "unknown\n";
        // TODO: how to return the model to the context, if it exists?
        break;
    }    

    for(unsigned i = 0; i < cnsts.size(); i++)
        ctx.m().dec_ref(cnsts[i]);

}

static expr *make_tree(cmd_context & ctx, const ptr_vector<expr> &exprs){
    if(exprs.size() == 0)
        throw cmd_exception("not enough arguments");
    expr *foo = exprs[0];
    for(unsigned i = 1; i < exprs.size(); i++){
        foo = ctx.m().mk_and(ctx.m().mk_interp(foo),exprs[i]);
    }    
    return foo;
}

static void get_interpolant(cmd_context & ctx, const ptr_vector<expr> &exprs, params_ref &m_params) {
    expr_ref foo(make_tree(ctx, exprs),ctx.m());
    get_interpolant(ctx,foo.get(),m_params);
}

static void compute_interpolant(cmd_context & ctx, const ptr_vector<expr> &exprs, params_ref &m_params) {
    expr_ref foo(make_tree(ctx, exprs),ctx.m());
    compute_interpolant_and_maybe_check(ctx,foo.get(),m_params,false);
}


// UNARY_CMD(get_interpolant_cmd, "get-interpolant", "<fmla>", "get interpolant for marked positions in fmla", CPK_EXPR, expr *, get_interpolant(ctx, arg););

// UNARY_CMD(get_and_check_interpolant_cmd, "get-and-check-interpolant", "<fmla>", "get and check interpolant for marked positions in fmla", CPK_EXPR, expr *, get_and_check_interpolant(ctx, arg););

class get_interpolant_cmd : public parametric_cmd {
protected:
    ptr_vector<expr>                   m_targets;
public:
    get_interpolant_cmd(char const * name = "get-interpolant"):parametric_cmd(name) {}

    virtual char const * get_usage() const { return "<fmla>+"; }

    virtual char const * get_main_descr() const { 
        return "get interpolant for formulas";
    }
    
    virtual void init_pdescrs(cmd_context & ctx, param_descrs & p) {
    }
    
    virtual void prepare(cmd_context & ctx) { 
        parametric_cmd::prepare(ctx);
        m_targets.resize(0);
    }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        return CPK_EXPR;
    }
    
    virtual void set_next_arg(cmd_context & ctx, expr * arg) {
        m_targets.push_back(arg);
    }
    
    virtual void execute(cmd_context & ctx) {
        get_interpolant(ctx,m_targets,m_params);
    }
};

class compute_interpolant_cmd : public get_interpolant_cmd {
public:
    compute_interpolant_cmd(char const * name = "compute-interpolant"):get_interpolant_cmd(name) {}

    virtual void execute(cmd_context & ctx) {      
        compute_interpolant(ctx,m_targets,m_params);
    }

};

void install_interpolant_cmds(cmd_context & ctx) {
    ctx.insert(alloc(get_interpolant_cmd));
    ctx.insert(alloc(compute_interpolant_cmd));
    //    ctx.insert(alloc(get_and_check_interpolant_cmd));
}
