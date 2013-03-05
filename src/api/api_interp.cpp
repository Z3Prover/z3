/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    api_interp.cpp

Abstract:
    API for interpolation

Author:

    Ken McMillan

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_tactic.h"
#include"api_solver.h"
#include"api_model.h"
#include"api_stats.h"
#include"api_ast_vector.h"
#include"tactic2solver.h"
#include"scoped_ctrl_c.h"
#include"cancel_eh.h"
#include"scoped_timer.h"
#include"smt_strategic_solver.h"
#include"smt_solver.h"
#include"smt_implied_equalities.h"
#include"iz3interp.h"
#include"iz3profiling.h"

typedef interpolation_options_struct *Z3_interpolation_options;

extern "C" {

  Z3_context Z3_mk_interpolation_context(Z3_config cfg){
    if(!cfg) cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "PROOF_MODE", "2");
    Z3_set_param_value(cfg, "MODEL", "true");
    Z3_set_param_value(cfg, "PRE_SIMPLIFIER","false");
    Z3_set_param_value(cfg, "SIMPLIFY_CLAUSES","false");
    
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    return ctx;
  }
  
  void Z3_interpolate_proof(Z3_context ctx,
			    Z3_ast proof,
			    int num,
			    Z3_ast *cnsts,
			    unsigned *parents,
			    Z3_params options,
			    Z3_ast *interps,
			    int num_theory,
			    Z3_ast *theory
			    ){

      if(num > 1){ // if we have interpolants to compute
	
	ptr_vector<ast> pre_cnsts_vec(num);  // get constraints in a vector
	for(int i = 0; i < num; i++){
	  ast *a = to_ast(cnsts[i]);
	  pre_cnsts_vec[i] = a;
	}
	
	vector<int> pre_parents_vec;  // get parents in a vector
	if(parents){
          pre_parents_vec.resize(num);
	  for(int i = 0; i < num; i++)
	    pre_parents_vec[i] = parents[i];
        }
	
	ptr_vector<ast> theory_vec; // get background theory in a vector
	if(theory){
	  theory_vec.resize(num_theory);
	  for(int i = 0; i < num_theory; i++)
	    theory_vec[i] = to_ast(theory[i]);
	}
	
	ptr_vector<ast> interpolants(num-1); // make space for result
	
	scoped_ptr<ast_manager> _m(&mk_c(ctx)->m());
	iz3interpolate(_m,
		       to_ast(proof),
		       pre_cnsts_vec,
		       pre_parents_vec,
		       interpolants,
		       theory_vec,
		       0); // ignore params for now FIXME

	// copy result back
	for(unsigned i = 0; i < interpolants.size(); i++)
	  interps[i] = of_ast(interpolants[i]);
      }

  }

  Z3_lbool Z3_interpolate(Z3_context ctx,
			  int num,
			  Z3_ast *cnsts,
			  unsigned *parents,
			  Z3_params options,
			  Z3_ast *interps,
			  Z3_model *model,
			  Z3_literals *labels,
			  bool incremental,
			  int num_theory,
                          Z3_ast *theory
			  ){

    
    if(!incremental){

      profiling::timer_start("Z3 assert");

      Z3_push(ctx); // so we can rewind later
      
      for(int i = 0; i < num; i++)
	Z3_assert_cnstr(ctx,cnsts[i]);  // assert all the constraints

      if(theory){
	for(int i = 0; i < num_theory; i++)
	  Z3_assert_cnstr(ctx,theory[i]);
      }

      profiling::timer_stop("Z3 assert");
    }


    // Get a proof of unsat
      
    Z3_ast proof;
    Z3_lbool result;
    
    profiling::timer_start("Z3 solving");
    result = Z3_check_assumptions(ctx, 0, 0, model, &proof, 0, 0);
    profiling::timer_stop("Z3 solving");
    
    switch (result) {
    case Z3_L_FALSE:
      
      Z3_interpolate_proof(ctx,
			   proof,
			   num,
			   cnsts,
			   parents,
			   options,
			   interps,
			   num_theory,
			   theory);
      break;
      
    case Z3_L_UNDEF:
      if(labels)
	*labels = Z3_get_relevant_labels(ctx);
      break;

    case Z3_L_TRUE:
      if(labels)
	*labels = Z3_get_relevant_labels(ctx);
      break;
    }

    return result;

  }
  
  static std::string Z3_profile_string;
  
  Z3_string Z3_interpolation_profile(Z3_context ctx){
    std::ostringstream f;
    profiling::print(f);
    Z3_profile_string = f.str();
    return Z3_profile_string.c_str();
  }


  Z3_interpolation_options
  Z3_mk_interpolation_options(){
    return (Z3_interpolation_options) new interpolation_options_struct;
  }

  void
  Z3_del_interpolation_options(Z3_interpolation_options opts){
    delete opts;
  }

  void
  Z3_set_interpolation_option(Z3_interpolation_options opts, 
			      Z3_string name,
			      Z3_string value){
    opts->map[name] = value;
  }

};
