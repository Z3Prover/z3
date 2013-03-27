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
#include"pp_params.hpp"
#include"iz3interp.h"
#include"iz3checker.h"

static void get_interpolant_and_maybe_check(cmd_context & ctx, expr * t, bool check) {

  // get the proof, if there is one

  if (!ctx.produce_interpolants())
    throw cmd_exception("interpolation is not enabled, use command (set-option :produce-interpolants true)");
  if (!ctx.has_manager() ||
      ctx.cs_state() != cmd_context::css_unsat)
    throw cmd_exception("proof is not available");
  expr_ref pr(ctx.m());
  pr = ctx.get_check_sat_result()->get_proof();
  if (pr == 0)
    throw cmd_exception("proof is not available");

  // get the assertions

  ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
  ptr_vector<expr>::const_iterator end = ctx.end_assertions();
  ptr_vector<ast> cnsts(end - it);
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

  
  // if we lived, print it out
  for(unsigned i = 0; i < interps.size(); i++){
    ctx.regular_stream()  << mk_pp(interps[i], ctx.m()) << std::endl;
#if 0
    ast_smt_pp pp(ctx.m());
    pp.set_logic(ctx.get_logic().str().c_str());
    pp.display_smt2(ctx.regular_stream(), to_expr(interps[i]));
    ctx.regular_stream() << std::endl;
#endif
  }

  // verify, for the paranoid...
  if(check || ctx.check_interpolants()){
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
}

static void get_interpolant(cmd_context & ctx, expr * t) {
  get_interpolant_and_maybe_check(ctx,t,false);
}

static void get_and_check_interpolant(cmd_context & ctx, expr * t) {
  get_interpolant_and_maybe_check(ctx,t,true);
}

UNARY_CMD(get_interpolant_cmd, "get-interpolant", "<fmla>", "get interpolant for marked positions in fmla", CPK_EXPR, expr *, get_interpolant(ctx, arg););

// UNARY_CMD(get_and_check_interpolant_cmd, "get-and-check-interpolant", "<fmla>", "get and check interpolant for marked positions in fmla", CPK_EXPR, expr *, get_and_check_interpolant(ctx, arg););

void install_interpolant_cmds(cmd_context & ctx) {
    ctx.insert(alloc(get_interpolant_cmd));
    //    ctx.insert(alloc(get_and_check_interpolant_cmd));
}
