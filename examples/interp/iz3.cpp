#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <string>
#include <vector>
#include "z3.h"



int usage(const char **argv){
  std::cerr << "usage: " << argv[0] << " [options] file.smt" << std::endl;
  std::cerr << std::endl;
  std::cerr << "options:" << std::endl;
  std::cerr << "  -t,--tree        tree interpolation" << std::endl;
  std::cerr << "  -c,--check       check result" << std::endl;
  std::cerr << "  -p,--profile     profile execution" << std::endl;
  std::cerr << "  -w,--weak        weak interpolants" << std::endl;
  std::cerr << "  -f,--flat        ouput flat formulas" << std::endl;
  std::cerr << "  -o <file>        ouput to SMT-LIB file" << std::endl;
  std::cerr << "  -a,--anon        anonymize" << std::endl;
  std::cerr << "  -s,--simple      simple proof mode" << std::endl;
  std::cerr << std::endl;
  return 1;
}

int main(int argc, const char **argv) {
    
  bool tree_mode = false;
  bool check_mode = false;
  bool profile_mode = false;
  bool incremental_mode = false;
  std::string output_file;
  bool flat_mode = false;
  bool anonymize = false;
  bool write = false;

  Z3_config cfg = Z3_mk_config();
  // Z3_interpolation_options options = Z3_mk_interpolation_options();
  Z3_params options = 0;

  /* Parse the command line */
  int argn = 1;
  while(argn < argc-1){
    std::string flag = argv[argn];
    if(flag[0] == '-'){
      if(flag == "-t" || flag == "--tree")
	tree_mode = true;
      else if(flag == "-c" || flag == "--check")
	check_mode = true;
      else if(flag == "-p" || flag == "--profile")
	profile_mode = true;
#if 0
      else if(flag == "-w" || flag == "--weak")
        Z3_set_interpolation_option(options,"weak","1");
      else if(flag == "--secondary")
        Z3_set_interpolation_option(options,"secondary","1");
#endif
      else if(flag == "-i" || flag == "--incremental")
        incremental_mode = true;
      else if(flag == "-o"){
        argn++;
        if(argn >= argc) return usage(argv);
        output_file = argv[argn];
      }
      else if(flag == "-f" || flag == "--flat")
        flat_mode = true;
      else if(flag == "-a" || flag == "--anon")
        anonymize = true;
      else if(flag == "-w" || flag == "--write")
        write = true;
      else if(flag == "-s" || flag == "--simple")
        Z3_set_param_value(cfg,"PREPROCESS","false");
      else
        return usage(argv);
    }
    argn++;
  }
  if(argn != argc-1)
    return usage(argv);
  const char *filename = argv[argn];


  /* Create a Z3 context to contain formulas */
  Z3_context ctx = Z3_mk_interpolation_context(cfg);

  if(write || anonymize)
    Z3_set_ast_print_mode(ctx,Z3_PRINT_SMTLIB2_COMPLIANT);
  else if(!flat_mode)
    Z3_set_ast_print_mode(ctx,Z3_PRINT_SMTLIB_COMPLIANT);
  
  /* Read an interpolation problem */

  unsigned num;
  Z3_ast *constraints;
  unsigned *parents = 0;
  const char *error;
  bool ok;
  unsigned num_theory;
  Z3_ast *theory;

  ok = Z3_read_interpolation_problem(ctx, &num, &constraints, tree_mode ? &parents : 0, filename, &error, &num_theory, &theory);

  /* If parse failed, print the error message */

  if(!ok){
    std::cerr << error << "\n";
    return 1;
  }

  /* if we get only one formula, and it is a conjunction, split it into conjuncts. */
  if(!tree_mode && num == 1){
    Z3_app app = Z3_to_app(ctx,constraints[0]);
    Z3_func_decl func = Z3_get_app_decl(ctx,app);
    Z3_decl_kind dk = Z3_get_decl_kind(ctx,func);
    if(dk == Z3_OP_AND){
      int nconjs = Z3_get_app_num_args(ctx,app);
      if(nconjs > 1){
	std::cout << "Splitting formula into " << nconjs << " conjuncts...\n";
	num = nconjs;
	constraints = new Z3_ast[num];
	for(int k = 0; k < num; k++)
	  constraints[k] = Z3_get_app_arg(ctx,app,k);
      }
    }
  }

  /* Write out anonymized version. */

  if(write || anonymize){
#if 0
    Z3_anonymize_ast_vector(ctx,num,constraints);
#endif
    std::string ofn = output_file.empty() ? "iz3out.smt2" : output_file;
    Z3_write_interpolation_problem(ctx, num, constraints, parents, ofn.c_str(), num_theory,  theory);
    std::cout << "anonymized problem written to " << ofn << "\n";
    exit(0);
  }

  /* Compute an interpolant, or get a model. */

  Z3_ast *interpolants = (Z3_ast *)malloc((num-1) * sizeof(Z3_ast));
  Z3_model model = 0;
  Z3_lbool result;

  if(!incremental_mode){
    /* In non-incremental mode, we just pass the constraints. */
      result = Z3_L_UNDEF; // FIXME: Z3_interpolate(ctx, num, constraints, parents,  options, interpolants, &model, 0, false, num_theory, theory);
  }
  else {

    /* This is a somewhat useless demonstration of incremental mode.
      Here, we assert the constraints in the context, then pass them to
      iZ3 in an array, so iZ3 knows the sequence. Note it's safe to pass
      "true", even though we haven't techically asserted if. */

    Z3_push(ctx);
    std::vector<Z3_ast> asserted(num);

    /* We start with nothing asserted. */
    for(int i = 0; i < num; i++)
      asserted[i] = Z3_mk_true(ctx);

    /* Now we assert the constrints one at a time until UNSAT. */

    for(int i = 0; i < num; i++){
      asserted[i] = constraints[i];
      Z3_assert_cnstr(ctx,constraints[i]);  // assert one constraint
      result = Z3_L_UNDEF; // FIXME: Z3_interpolate(ctx, num, &asserted[0], parents,  options, interpolants, &model, 0, true, 0, 0);
      if(result == Z3_L_FALSE){
	for(unsigned j = 0; j < num-1; j++)
          /* Since we want the interpolant formulas to survive a "pop", we
            "persist" them here. */
          Z3_persist_ast(ctx,interpolants[j],1);
        break;
      }
    }
    Z3_pop(ctx,1);
  }
  
  switch (result) {
  
    /* If UNSAT, print the interpolants */
  case Z3_L_FALSE:
    printf("unsat\n");
    if(output_file.empty()){
      printf("interpolant:\n");
      for(int i = 0; i < num-1; i++)
        printf("%s\n", Z3_ast_to_string(ctx, interpolants[i]));
    }
    else {
#if 0
      Z3_write_interpolation_problem(ctx,num-1,interpolants,0,output_file.c_str());
      printf("interpolant written to %s\n",output_file.c_str());
#endif
    }
#if 1
    if(check_mode){
      std::cout << "Checking interpolant...\n";
      bool chk;
      chk = Z3_check_interpolant(ctx,num,constraints,parents,interpolants,&error,num_theory,theory);  
      if(chk)
	std::cout << "Interpolant is correct\n";
      else {
        std::cout << "Interpolant is incorrect\n";
        std::cout << error;
        return 1;
      }
    }
#endif
    break;
  case Z3_L_UNDEF:
    printf("fail\n");
    break;
  case Z3_L_TRUE:
    printf("sat\n");
    printf("model:\n%s\n", Z3_model_to_string(ctx, model));
    break;
  }

  if(profile_mode)
    std::cout << Z3_interpolation_profile(ctx);

  /* Delete the model if there is one */
  
  if (model)
    Z3_del_model(ctx, model);
  
  /* Delete logical context. */

  Z3_del_context(ctx);
  free(interpolants);

  return 0;
}


#if 0



int test(){
  int i;

  /* Create a Z3 context to contain formulas */

  Z3_config cfg = Z3_mk_config();
  Z3_context ctx = iz3_mk_context(cfg);
    
  int num = 2;

  Z3_ast *constraints = (Z3_ast *)malloc(num * sizeof(Z3_ast));

#if 1
  Z3_sort arr = Z3_mk_array_sort(ctx,Z3_mk_int_sort(ctx),Z3_mk_bool_sort(ctx)); 
  Z3_symbol  as  = Z3_mk_string_symbol(ctx, "a");
  Z3_symbol  bs  = Z3_mk_string_symbol(ctx, "b");
  Z3_symbol  xs  = Z3_mk_string_symbol(ctx, "x");

  Z3_ast a = Z3_mk_const(ctx,as,arr);
  Z3_ast b = Z3_mk_const(ctx,bs,arr);
  Z3_ast x = Z3_mk_const(ctx,xs,Z3_mk_int_sort(ctx));
  
  Z3_ast c1 = Z3_mk_eq(ctx,a,Z3_mk_store(ctx,b,x,Z3_mk_true(ctx)));
  Z3_ast c2 = Z3_mk_not(ctx,Z3_mk_select(ctx,a,x));
#else
  Z3_symbol  xs  = Z3_mk_string_symbol(ctx, "x");
  Z3_ast x = Z3_mk_const(ctx,xs,Z3_mk_bool_sort(ctx));
  Z3_ast c1 = Z3_mk_eq(ctx,x,Z3_mk_true(ctx));
  Z3_ast c2 = Z3_mk_eq(ctx,x,Z3_mk_false(ctx));

#endif

  constraints[0] = c1;
  constraints[1] = c2;
  
  /* print out the result for grins. */

  // Z3_string smtout = Z3_benchmark_to_smtlib_string (ctx, "foo", "QFLIA", "sat", "", num, constraints, Z3_mk_true(ctx));

  // Z3_string smtout = Z3_ast_to_string(ctx,constraints[0]);
  // Z3_string smtout = Z3_context_to_string(ctx);
  // puts(smtout);

  iz3_print(ctx,num,constraints,"iZ3temp.smt");

  /* Make room for interpolants. */

  Z3_ast *interpolants = (Z3_ast *)malloc((num-1) * sizeof(Z3_ast));

  /* Make room for the model. */

  Z3_model model = 0;

  /* Call the prover */

  Z3_lbool result = iz3_interpolate(ctx, num, constraints, interpolants, &model);

  switch (result) {
  
    /* If UNSAT, print the interpolants */
  case Z3_L_FALSE:
    printf("unsat, interpolants:\n");
    for(i = 0; i < num-1; i++)
      printf("%s\n", Z3_ast_to_string(ctx, interpolants[i]));
    break;
  case Z3_L_UNDEF:
    printf("fail\n");
    break;
  case Z3_L_TRUE:
    printf("sat\n");
    printf("model:\n%s\n", Z3_model_to_string(ctx, model));
    break;
  }

  /* Delete the model if there is one */
  
  if (model)
    Z3_del_model(ctx, model);
  
  /* Delete logical context (note, we call iz3_del_context, not
     Z3_del_context */

  iz3_del_context(ctx);

  return 1;
}

struct z3_error {
  Z3_error_code c;
  z3_error(Z3_error_code _c) : c(_c) {}
};

extern "C" {
  static void throw_z3_error(Z3_error_code c){
    throw z3_error(c);
  }
}

int main(int argc, const char **argv) {

  /* Create a Z3 context to contain formulas */

  Z3_config cfg = Z3_mk_config();
  Z3_context ctx = iz3_mk_context(cfg);
  Z3_set_error_handler(ctx, throw_z3_error);
    
  /* Make some constraints, by parsing an smtlib formatted file given as arg 1 */

  try {
    Z3_parse_smtlib_file(ctx, argv[1], 0, 0, 0, 0, 0, 0);
  }
  catch(const z3_error &err){
    std::cerr << "Z3 error: " << Z3_get_error_msg(err.c) << "\n";
    std::cerr << Z3_get_smtlib_error(ctx) << "\n";
    return(1);
  } 

  /* Get the constraints from the parser. */

  int num = Z3_get_smtlib_num_formulas(ctx);

  if(num == 0){
    std::cerr << "iZ3 error: File contains no formulas.\n";
    return 1;
  }


  Z3_ast *constraints = (Z3_ast *)malloc(num * sizeof(Z3_ast));

  int i;
  for (i = 0; i < num; i++)
    constraints[i] = Z3_get_smtlib_formula(ctx, i);

  /* if we get only one formula, and it is a conjunction, split it into conjuncts. */
  if(num == 1){
    Z3_app app = Z3_to_app(ctx,constraints[0]);
    Z3_func_decl func = Z3_get_app_decl(ctx,app);
    Z3_decl_kind dk = Z3_get_decl_kind(ctx,func);
    if(dk == Z3_OP_AND){
      int nconjs = Z3_get_app_num_args(ctx,app);
      if(nconjs > 1){
	std::cout << "Splitting formula into " << nconjs << " conjuncts...\n";
	num = nconjs;
	constraints = new Z3_ast[num];
	for(int k = 0; k < num; k++)
	  constraints[k] = Z3_get_app_arg(ctx,app,k);
      }
    }
  }


  /* print out the result for grins. */

  // Z3_string smtout = Z3_benchmark_to_smtlib_string (ctx, "foo", "QFLIA", "sat", "", num, constraints, Z3_mk_true(ctx));

  // Z3_string smtout = Z3_ast_to_string(ctx,constraints[0]);
  // Z3_string smtout = Z3_context_to_string(ctx);
  // puts(smtout);

  // iz3_print(ctx,num,constraints,"iZ3temp.smt");

  /* Make room for interpolants. */

  Z3_ast *interpolants = (Z3_ast *)malloc((num-1) * sizeof(Z3_ast));

  /* Make room for the model. */

  Z3_model model = 0;

  /* Call the prover */

  Z3_lbool result = iz3_interpolate(ctx, num, constraints, interpolants, &model);

  switch (result) {
  
    /* If UNSAT, print the interpolants */
  case Z3_L_FALSE:
    printf("unsat, interpolants:\n");
    for(i = 0; i < num-1; i++)
      printf("%s\n", Z3_ast_to_string(ctx, interpolants[i]));
    std::cout << "Checking interpolants...\n";
    const char *error;
    if(iZ3_check_interpolant(ctx, num, constraints, 0, interpolants, &error))
      std::cout << "Interpolant is correct\n";
    else {
      std::cout << "Interpolant is incorrect\n";
      std::cout << error << "\n";
    }
    break;
  case Z3_L_UNDEF:
    printf("fail\n");
    break;
  case Z3_L_TRUE:
    printf("sat\n");
    printf("model:\n%s\n", Z3_model_to_string(ctx, model));
    break;
  }

  /* Delete the model if there is one */
  
  if (model)
    Z3_del_model(ctx, model);
  
  /* Delete logical context (note, we call iz3_del_context, not
     Z3_del_context */

  iz3_del_context(ctx);

  return 0;
}

#endif
