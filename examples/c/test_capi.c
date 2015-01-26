#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<memory.h>
#include<setjmp.h>
#include<z3.h>

#define LOG_Z3_CALLS

#ifdef LOG_Z3_CALLS
#define LOG_MSG(msg) Z3_append_log(msg)
#else
#define LOG_MSG(msg) ((void)0)
#endif

/** 
   \defgroup capi_ex C API examples
*/
/*@{*/
/**
   @name Auxiliary Functions
*/
/*@{*/

/**
   \brief exit gracefully in case of error.
*/
void exitf(const char* message) 
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

/**
   \brief exit if unreachable code was reached.
*/
void unreachable() 
{
    exitf("unreachable code was reached");
}

/**
   \brief Simpler error handler.
 */
void error_handler(Z3_context c, Z3_error_code e) 
{
    printf("Error code: %d\n", e);
    exitf("incorrect use of Z3");
}

static jmp_buf g_catch_buffer;
/**
   \brief Low tech exceptions. 
   
   In high-level programming languages, an error handler can throw an exception.
*/
void throw_z3_error(Z3_context c, Z3_error_code e) 
{
    longjmp(g_catch_buffer, e);
}

/**
   \brief Create a logical context.  

   Enable model construction. Other configuration parameters can be passed in the cfg variable.

   Also enable tracing to stderr and register custom error handler.
*/
Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err) 
{
    Z3_context ctx;
    
    Z3_set_param_value(cfg, "model", "true");
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, err);
    
    return ctx;
}

/**
   \brief Create a logical context.

   Enable model construction only.

   Also enable tracing to stderr and register standard error handler.
*/
Z3_context mk_context() 
{
    Z3_config  cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    return ctx;
}

/**
   \brief Create a logical context.

   Enable fine-grained proof construction.
   Enable model construction.

   Also enable tracing to stderr and register standard error handler.
*/
Z3_context mk_proof_context() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx;
    Z3_set_param_value(cfg, "proof", "true");
    ctx = mk_context_custom(cfg, throw_z3_error);
    Z3_del_config(cfg);
    return ctx;
}

/**
   \brief Create a variable using the given name and type.
*/
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty) 
{
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

/**
   \brief Create a boolean variable using the given name.
*/
Z3_ast mk_bool_var(Z3_context ctx, const char * name) 
{
    Z3_sort ty = Z3_mk_bool_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create an integer variable using the given name.
*/
Z3_ast mk_int_var(Z3_context ctx, const char * name) 
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create a Z3 integer node using a C int. 
*/
Z3_ast mk_int(Z3_context ctx, int v) 
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return Z3_mk_int(ctx, v, ty);
}

/**
   \brief Create a real variable using the given name.
*/
Z3_ast mk_real_var(Z3_context ctx, const char * name) 
{
    Z3_sort ty = Z3_mk_real_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create the unary function application: <tt>(f x)</tt>.
*/
Z3_ast mk_unary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x) 
{
    Z3_ast args[1] = {x};
    return Z3_mk_app(ctx, f, 1, args);
}

/**
   \brief Create the binary function application: <tt>(f x y)</tt>.
*/
Z3_ast mk_binary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y) 
{
    Z3_ast args[2] = {x, y};
    return Z3_mk_app(ctx, f, 2, args);
}

/**
   \brief Check whether the logical context is satisfiable, and compare the result with the expected result.
   If the context is satisfiable, then display the model.
*/
void check(Z3_context ctx, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_check_and_get_model(ctx, &m);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
        break;
    case Z3_L_TRUE:
        printf("sat\n%s\n", Z3_model_to_string(ctx, m));
        break;
    }
    if (m) {
        Z3_del_model(ctx, m);
    }
    if (result != expected_result) {
        exitf("unexpected result");
    }
}

/**
   \brief Prove that the constraints already asserted into the logical
   context implies the given formula.  The result of the proof is
   displayed.
   
   Z3 is a satisfiability checker. So, one can prove \c f by showing
   that <tt>(not f)</tt> is unsatisfiable.

   The context \c ctx is not modified by this function.
*/
void prove(Z3_context ctx, Z3_ast f, Z3_bool is_valid)
{
    Z3_model m;
    Z3_ast   not_f;

    /* save the current state of the context */
    Z3_push(ctx);

    not_f = Z3_mk_not(ctx, f);
    Z3_assert_cnstr(ctx, not_f);
    
    m = 0;
    
    switch (Z3_check_and_get_model(ctx, &m)) {
    case Z3_L_FALSE:
        /* proved */
        printf("valid\n");
        if (!is_valid) {
            exitf("unexpected result");
        }
        break;
    case Z3_L_UNDEF:
        /* Z3 failed to prove/disprove f. */
        printf("unknown\n");
        if (m != 0) {
            /* m should be viewed as a potential counterexample. */
            printf("potential counterexample:\n%s\n", Z3_model_to_string(ctx, m));
        }
        if (is_valid) {
            exitf("unexpected result");
        }
        break;
    case Z3_L_TRUE:
        /* disproved */
        printf("invalid\n");
        if (m) {
            /* the model returned by Z3 is a counterexample */
            printf("counterexample:\n%s\n", Z3_model_to_string(ctx, m));
        }
        if (is_valid) {
            exitf("unexpected result");
        }
        break;
    }

    if (m) {
        Z3_del_model(ctx, m);
    }

    /* restore context */
    Z3_pop(ctx, 1);
}

/**
   \brief Assert the axiom: function f is injective in the i-th argument.
   
   The following axiom is asserted into the logical context:
   \code
   forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
   \endcode

   Where, \c finv is a fresh function declaration.
*/
void assert_inj_axiom(Z3_context ctx, Z3_func_decl f, unsigned i) 
{
    unsigned sz, j;
    Z3_sort finv_domain, finv_range;
    Z3_func_decl finv;
    Z3_sort * types; /* types of the quantified variables */
    Z3_symbol *   names; /* names of the quantified variables */
    Z3_ast * xs;         /* arguments for the application f(x_0, ..., x_i, ..., x_{n-1}) */
    Z3_ast   x_i, fxs, finv_fxs, eq;
    Z3_pattern p;
    Z3_ast   q;
    sz = Z3_get_domain_size(ctx, f);

    if (i >= sz) {
        exitf("failed to create inj axiom");
    }
    
    /* declare the i-th inverse of f: finv */
    finv_domain = Z3_get_range(ctx, f);
    finv_range  = Z3_get_domain(ctx, f, i);
    finv        = Z3_mk_fresh_func_decl(ctx, "inv", 1, &finv_domain, finv_range);

    /* allocate temporary arrays */
    types       = (Z3_sort *) malloc(sizeof(Z3_sort) * sz);
    names       = (Z3_symbol *) malloc(sizeof(Z3_symbol) * sz);
    xs          = (Z3_ast *) malloc(sizeof(Z3_ast) * sz);
    
    /* fill types, names and xs */
    for (j = 0; j < sz; j++) { types[j] = Z3_get_domain(ctx, f, j); };
    for (j = 0; j < sz; j++) { names[j] = Z3_mk_int_symbol(ctx, j); };
    for (j = 0; j < sz; j++) { xs[j]    = Z3_mk_bound(ctx, j, types[j]); };

    x_i = xs[i];

    /* create f(x_0, ..., x_i, ..., x_{n-1}) */ 
    fxs         = Z3_mk_app(ctx, f, sz, xs);

    /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
    finv_fxs    = mk_unary_app(ctx, finv, fxs);

    /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
    eq          = Z3_mk_eq(ctx, finv_fxs, x_i);

    /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
    p           = Z3_mk_pattern(ctx, 1, &fxs);
    printf("pattern: %s\n", Z3_pattern_to_string(ctx, p));
    printf("\n");

    /* create & assert quantifier */
    q           = Z3_mk_forall(ctx, 
                                 0, /* using default weight */
                                 1, /* number of patterns */
                                 &p, /* address of the "array" of patterns */
                                 sz, /* number of quantified variables */
                                 types, 
                                 names,
                                 eq);
    printf("assert axiom:\n%s\n", Z3_ast_to_string(ctx, q));
    Z3_assert_cnstr(ctx, q);

    /* free temporary arrays */
    free(types);
    free(names);
    free(xs);
}

/**
   \brief Assert the axiom: function f is commutative. 
   
   This example uses the SMT-LIB parser to simplify the axiom construction.
*/
void assert_comm_axiom(Z3_context ctx, Z3_func_decl f) 
{
    Z3_sort t;
    Z3_symbol f_name, t_name;
    Z3_ast q;

    t = Z3_get_range(ctx, f);

    if (Z3_get_domain_size(ctx, f) != 2 ||
        Z3_get_domain(ctx, f, 0) != t ||
        Z3_get_domain(ctx, f, 1) != t) {
        exitf("function must be binary, and argument types must be equal to return type");
    } 
    
    /* Inside the parser, function f will be referenced using the symbol 'f'. */
    f_name = Z3_mk_string_symbol(ctx, "f");
    
    /* Inside the parser, type t will be referenced using the symbol 'T'. */
    t_name = Z3_mk_string_symbol(ctx, "T");
	

    Z3_parse_smtlib_string(ctx, 
                           "(benchmark comm :formula (forall (x T) (y T) (= (f x y) (f y x))))",
                           1, &t_name, &t,
                           1, &f_name, &f);
    q = Z3_get_smtlib_formula(ctx, 0);
    printf("assert axiom:\n%s\n", Z3_ast_to_string(ctx, q));
    Z3_assert_cnstr(ctx, q);
}

/**
   \brief Z3 does not support explicitly tuple updates. They can be easily implemented 
   as macros. The argument \c t must have tuple type. 
   A tuple update is a new tuple where field \c i has value \c new_val, and all
   other fields have the value of the respective field of \c t.

   <tt>update(t, i, new_val)</tt> is equivalent to
   <tt>mk_tuple(proj_0(t), ..., new_val, ..., proj_n(t))</tt> 
*/
Z3_ast mk_tuple_update(Z3_context c, Z3_ast t, unsigned i, Z3_ast new_val) 
{
    Z3_sort         ty;
    Z3_func_decl   mk_tuple_decl;
    unsigned            num_fields, j;
    Z3_ast *            new_fields;
    Z3_ast              result;

    ty = Z3_get_sort(c, t);

    if (Z3_get_sort_kind(c, ty) != Z3_DATATYPE_SORT) {
        exitf("argument must be a tuple");
    }

    num_fields = Z3_get_tuple_sort_num_fields(c, ty);
    
    if (i >= num_fields) {
        exitf("invalid tuple update, index is too big");
    }
    
    new_fields = (Z3_ast*) malloc(sizeof(Z3_ast) * num_fields);
    for (j = 0; j < num_fields; j++) {
        if (i == j) {
            /* use new_val at position i */
            new_fields[j] = new_val;
        }
        else {
            /* use field j of t */
            Z3_func_decl proj_decl = Z3_get_tuple_sort_field_decl(c, ty, j);
            new_fields[j] = mk_unary_app(c, proj_decl, t);
        }
    }
    mk_tuple_decl = Z3_get_tuple_sort_mk_decl(c, ty);
    result = Z3_mk_app(c, mk_tuple_decl, num_fields, new_fields);
    free(new_fields);
    return result;
}

/**
   \brief Display a symbol in the given output stream.
*/
void display_symbol(Z3_context c, FILE * out, Z3_symbol s) 
{
    switch (Z3_get_symbol_kind(c, s)) {
    case Z3_INT_SYMBOL:
        fprintf(out, "#%d", Z3_get_symbol_int(c, s));
        break;
    case Z3_STRING_SYMBOL:
        fprintf(out, "%s", Z3_get_symbol_string(c, s));
        break;
    default:
        unreachable();
    }
}

/**
   \brief Display the given type.
*/
void display_sort(Z3_context c, FILE * out, Z3_sort ty) 
{
    switch (Z3_get_sort_kind(c, ty)) {
    case Z3_UNINTERPRETED_SORT:
        display_symbol(c, out, Z3_get_sort_name(c, ty));
        break;
    case Z3_BOOL_SORT:
        fprintf(out, "bool");
        break;
    case Z3_INT_SORT:
        fprintf(out, "int");
        break;
    case Z3_REAL_SORT:
        fprintf(out, "real");
        break;
    case Z3_BV_SORT:
        fprintf(out, "bv%d", Z3_get_bv_sort_size(c, ty));
        break;
    case Z3_ARRAY_SORT: 
        fprintf(out, "[");
        display_sort(c, out, Z3_get_array_sort_domain(c, ty));
        fprintf(out, "->");
        display_sort(c, out, Z3_get_array_sort_range(c, ty));
        fprintf(out, "]");
        break;
    case Z3_DATATYPE_SORT:
		if (Z3_get_datatype_sort_num_constructors(c, ty) != 1) 
		{
			fprintf(out, "%s", Z3_sort_to_string(c,ty));
			break;
		}
		{
        unsigned num_fields = Z3_get_tuple_sort_num_fields(c, ty);
        unsigned i;
        fprintf(out, "(");
        for (i = 0; i < num_fields; i++) {
            Z3_func_decl field = Z3_get_tuple_sort_field_decl(c, ty, i);
            if (i > 0) {
                fprintf(out, ", ");
            }
            display_sort(c, out, Z3_get_range(c, field));
        }
        fprintf(out, ")");
        break;
    }
    default:
        fprintf(out, "unknown[");
        display_symbol(c, out, Z3_get_sort_name(c, ty));
        fprintf(out, "]");
        break;
    }
}

/**
   \brief Custom ast pretty printer. 

   This function demonstrates how to use the API to navigate terms.
*/
void display_ast(Z3_context c, FILE * out, Z3_ast v) 
{
    switch (Z3_get_ast_kind(c, v)) {
    case Z3_NUMERAL_AST: {
        Z3_sort t;
        fprintf(out, "%s", Z3_get_numeral_string(c, v));
        t = Z3_get_sort(c, v);
        fprintf(out, ":");
        display_sort(c, out, t);
        break;
    }
    case Z3_APP_AST: {
        unsigned i;
        Z3_app app = Z3_to_app(c, v);
        unsigned num_fields = Z3_get_app_num_args(c, app);
        Z3_func_decl d = Z3_get_app_decl(c, app);
        fprintf(out, "%s", Z3_func_decl_to_string(c, d));
        if (num_fields > 0) {
            fprintf(out, "[");
            for (i = 0; i < num_fields; i++) {
                if (i > 0) {
                    fprintf(out, ", ");
                }
                display_ast(c, out, Z3_get_app_arg(c, app, i));
            }
            fprintf(out, "]");
        }
        break;
    }
    case Z3_QUANTIFIER_AST: {
        fprintf(out, "quantifier");
        ;	
    }
    default:
        fprintf(out, "#unknown");
    }
}

/**
   \brief Custom function interpretations pretty printer.
*/
void display_function_interpretations(Z3_context c, FILE * out, Z3_model m) 
{
    unsigned num_functions, i;

    fprintf(out, "function interpretations:\n");

    num_functions = Z3_get_model_num_funcs(c, m);
    for (i = 0; i < num_functions; i++) {
        Z3_func_decl fdecl;
        Z3_symbol name;
        Z3_ast func_else;
        unsigned num_entries, j;
        
        fdecl = Z3_get_model_func_decl(c, m, i);
        name = Z3_get_decl_name(c, fdecl);
        display_symbol(c, out, name);
        fprintf(out, " = {");
        num_entries = Z3_get_model_func_num_entries(c, m, i);
        for (j = 0; j < num_entries; j++) {
            unsigned num_args, k;
            if (j > 0) {
                fprintf(out, ", ");
            }
            num_args = Z3_get_model_func_entry_num_args(c, m, i, j);
            fprintf(out, "(");
            for (k = 0; k < num_args; k++) {
                if (k > 0) {
                    fprintf(out, ", ");
                }
                display_ast(c, out, Z3_get_model_func_entry_arg(c, m, i, j, k));
            }
            fprintf(out, "|->");
            display_ast(c, out, Z3_get_model_func_entry_value(c, m, i, j));
            fprintf(out, ")");
        }
        if (num_entries > 0) {
            fprintf(out, ", ");
        }
        fprintf(out, "(else|->");
        func_else = Z3_get_model_func_else(c, m, i);
        display_ast(c, out, func_else);
        fprintf(out, ")}\n");
    }
}

/**
   \brief Custom model pretty printer.
*/
void display_model(Z3_context c, FILE * out, Z3_model m) 
{
    unsigned num_constants;
    unsigned i;

    num_constants = Z3_get_model_num_constants(c, m);
    for (i = 0; i < num_constants; i++) {
        Z3_symbol name;
        Z3_func_decl cnst = Z3_get_model_constant(c, m, i);
        Z3_ast a, v;
        Z3_bool ok;
        name = Z3_get_decl_name(c, cnst);
        display_symbol(c, out, name);
        fprintf(out, " = ");
        a = Z3_mk_app(c, cnst, 0, 0);
        v = a;
        ok = Z3_eval(c, m, a, &v);
        display_ast(c, out, v);
        fprintf(out, "\n");
    }
    display_function_interpretations(c, out, m);
}

/**
   \brief Similar to #check, but uses #display_model instead of #Z3_model_to_string.
*/
void check2(Z3_context ctx, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_check_and_get_model(ctx, &m);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        printf("potential model:\n");
        display_model(ctx, stdout, m);
        break;
    case Z3_L_TRUE:
        printf("sat\n");
        display_model(ctx, stdout, m);
        break;
    }
    if (m) {
        Z3_del_model(ctx, m);
    }
    if (result != expected_result) {
        exitf("unexpected result");
    }
}

/**
   \brief Display Z3 version in the standard output.
*/
void display_version() 
{
    unsigned major, minor, build, revision;
    Z3_get_version(&major, &minor, &build, &revision);
    printf("Z3 %d.%d.%d.%d\n", major, minor, build, revision);
}
/*@}*/

/**
   @name Examples
*/
/*@{*/
/**
   \brief "Hello world" example: create a Z3 logical context, and delete it.
*/
void simple_example() 
{
    Z3_context ctx;
    LOG_MSG("simple_example");
    printf("\nsimple_example\n");
 
    ctx = mk_context();

    /* do something with the context */
    printf("CONTEXT:\n%sEND OF CONTEXT\n", Z3_context_to_string(ctx));

    /* delete logical context */
    Z3_del_context(ctx);
}

/**
  Demonstration of how Z3 can be used to prove validity of
  De Morgan's Duality Law: {e not(x and y) <-> (not x) or ( not y) }
*/
void demorgan() 
{
    Z3_config cfg;
    Z3_context ctx;
    Z3_sort bool_sort;
    Z3_symbol symbol_x, symbol_y;
    Z3_ast x, y, not_x, not_y, x_and_y, ls, rs, conjecture, negated_conjecture;
    Z3_ast args[2];

    printf("\nDeMorgan\n");
    LOG_MSG("DeMorgan");
    
    cfg                = Z3_mk_config();
    ctx                = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    bool_sort          = Z3_mk_bool_sort(ctx);
    symbol_x           = Z3_mk_int_symbol(ctx, 0);
    symbol_y           = Z3_mk_int_symbol(ctx, 1);
    x                  = Z3_mk_const(ctx, symbol_x, bool_sort);
    y                  = Z3_mk_const(ctx, symbol_y, bool_sort);
    
    /* De Morgan - with a negation around */
    /* !(!(x && y) <-> (!x || !y)) */
    not_x              = Z3_mk_not(ctx, x);
    not_y              = Z3_mk_not(ctx, y);
    args[0]            = x;
    args[1]            = y;
    x_and_y            = Z3_mk_and(ctx, 2, args);
    ls                 = Z3_mk_not(ctx, x_and_y);
    args[0]            = not_x;
    args[1]            = not_y;
    rs                 = Z3_mk_or(ctx, 2, args);
    conjecture         = Z3_mk_iff(ctx, ls, rs);
    negated_conjecture = Z3_mk_not(ctx, conjecture);
    
    Z3_assert_cnstr(ctx, negated_conjecture);
    switch (Z3_check(ctx)) {
    case Z3_L_FALSE:
        /* The negated conjecture was unsatisfiable, hence the conjecture is valid */
        printf("DeMorgan is valid\n");
        break;
    case Z3_L_UNDEF:
        /* Check returned undef */
        printf("Undef\n");
        break;
    case Z3_L_TRUE:
        /* The negated conjecture was satisfiable, hence the conjecture is not valid */
        printf("DeMorgan is not valid\n");
        break;
    }
    Z3_del_context(ctx);
}

/**
   \brief Find a model for <tt>x xor y</tt>.
*/
void find_model_example1() 
{
    Z3_context ctx;
    Z3_ast x, y, x_xor_y;

    printf("\nfind_model_example1\n");
    LOG_MSG("find_model_example1");

    ctx     = mk_context();

    x       = mk_bool_var(ctx, "x");
    y       = mk_bool_var(ctx, "y");
    x_xor_y = Z3_mk_xor(ctx, x, y);
    
    Z3_assert_cnstr(ctx, x_xor_y);

    printf("model for: x xor y\n");
    check(ctx, Z3_L_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Find a model for <tt>x < y + 1, x > 2</tt>.
   Then, assert <tt>not(x = y)</tt>, and find another model.
*/
void find_model_example2() 
{
    Z3_context ctx;
    Z3_ast x, y, one, two, y_plus_one;
    Z3_ast x_eq_y;
    Z3_ast args[2];
    Z3_ast c1, c2, c3;

    printf("\nfind_model_example2\n");
    LOG_MSG("find_model_example2");
    
    ctx        = mk_context();
    x          = mk_int_var(ctx, "x");
    y          = mk_int_var(ctx, "y");
    one        = mk_int(ctx, 1);
    two        = mk_int(ctx, 2);

    args[0]    = y;
    args[1]    = one;
    y_plus_one = Z3_mk_add(ctx, 2, args);

    c1         = Z3_mk_lt(ctx, x, y_plus_one);
    c2         = Z3_mk_gt(ctx, x, two);
    
    Z3_assert_cnstr(ctx, c1);
    Z3_assert_cnstr(ctx, c2);

    printf("model for: x < y + 1, x > 2\n");
    check(ctx, Z3_L_TRUE);

    /* assert not(x = y) */
    x_eq_y     = Z3_mk_eq(ctx, x, y);
    c3         = Z3_mk_not(ctx, x_eq_y);
    Z3_assert_cnstr(ctx, c3);

    printf("model for: x < y + 1, x > 2, not(x = y)\n");
    check(ctx, Z3_L_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Prove <tt>x = y implies g(x) = g(y)</tt>, and
   disprove <tt>x = y implies g(g(x)) = g(y)</tt>.

   This function demonstrates how to create uninterpreted types and
   functions.
*/
void prove_example1() 
{
    Z3_context ctx;
    Z3_symbol U_name, g_name, x_name, y_name;
    Z3_sort U;
    Z3_sort g_domain[1];
    Z3_func_decl g;
    Z3_ast x, y, gx, ggx, gy;
    Z3_ast eq, f;

    printf("\nprove_example1\n");
    LOG_MSG("prove_example1");
    
    ctx        = mk_context();
    
    /* create uninterpreted type. */
    U_name     = Z3_mk_string_symbol(ctx, "U");
    U          = Z3_mk_uninterpreted_sort(ctx, U_name);
    
    /* declare function g */
    g_name      = Z3_mk_string_symbol(ctx, "g");
    g_domain[0] = U;
    g           = Z3_mk_func_decl(ctx, g_name, 1, g_domain, U);

    /* create x and y */
    x_name      = Z3_mk_string_symbol(ctx, "x");
    y_name      = Z3_mk_string_symbol(ctx, "y");
    x           = Z3_mk_const(ctx, x_name, U);
    y           = Z3_mk_const(ctx, y_name, U);
    /* create g(x), g(y) */
    gx          = mk_unary_app(ctx, g, x);
    gy          = mk_unary_app(ctx, g, y);
    
    /* assert x = y */
    eq          = Z3_mk_eq(ctx, x, y);
    Z3_assert_cnstr(ctx, eq);

    /* prove g(x) = g(y) */
    f           = Z3_mk_eq(ctx, gx, gy);
    printf("prove: x = y implies g(x) = g(y)\n");
    prove(ctx, f, Z3_TRUE);

    /* create g(g(x)) */
    ggx         = mk_unary_app(ctx, g, gx);
    
    /* disprove g(g(x)) = g(y) */
    f           = Z3_mk_eq(ctx, ggx, gy);
    printf("disprove: x = y implies g(g(x)) = g(y)\n");
    prove(ctx, f, Z3_FALSE);

    Z3_del_context(ctx);
}

/**
   \brief Prove <tt>not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0 </tt>.
   Then, show that <tt>z < -1</tt> is not implied.

   This example demonstrates how to combine uninterpreted functions and arithmetic.
*/
void prove_example2() 
{
    Z3_context ctx;
    Z3_sort int_sort;
    Z3_symbol g_name;
    Z3_sort g_domain[1];
    Z3_func_decl g;
    Z3_ast x, y, z, zero, minus_one, x_plus_z, gx, gy, gz, gx_gy, ggx_gy;
    Z3_ast args[2];
    Z3_ast eq, c1, c2, c3, f;

    printf("\nprove_example2\n");
    LOG_MSG("prove_example2");
    
    ctx        = mk_context();

    /* declare function g */
    int_sort    = Z3_mk_int_sort(ctx);
    g_name      = Z3_mk_string_symbol(ctx, "g");
    g_domain[0] = int_sort;
    g           = Z3_mk_func_decl(ctx, g_name, 1, g_domain, int_sort);
    
    /* create x, y, and z */
    x           = mk_int_var(ctx, "x");
    y           = mk_int_var(ctx, "y");
    z           = mk_int_var(ctx, "z");

    /* create gx, gy, gz */
    gx          = mk_unary_app(ctx, g, x);
    gy          = mk_unary_app(ctx, g, y);
    gz          = mk_unary_app(ctx, g, z);
    
    /* create zero */
    zero        = mk_int(ctx, 0);

    /* assert not(g(g(x) - g(y)) = g(z)) */
    args[0]     = gx;
    args[1]     = gy;
    gx_gy       = Z3_mk_sub(ctx, 2, args);
    ggx_gy      = mk_unary_app(ctx, g, gx_gy);
    eq          = Z3_mk_eq(ctx, ggx_gy, gz);
    c1          = Z3_mk_not(ctx, eq);
    Z3_assert_cnstr(ctx, c1);

    /* assert x + z <= y */
    args[0]     = x;
    args[1]     = z;
    x_plus_z    = Z3_mk_add(ctx, 2, args);
    c2          = Z3_mk_le(ctx, x_plus_z, y);
    Z3_assert_cnstr(ctx, c2);

    /* assert y <= x */
    c3          = Z3_mk_le(ctx, y, x);
    Z3_assert_cnstr(ctx, c3);

    /* prove z < 0 */
    f           = Z3_mk_lt(ctx, z, zero);
    printf("prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0\n");
    prove(ctx, f, Z3_TRUE);

    /* disprove z < -1 */
    minus_one   = mk_int(ctx, -1);
    f           = Z3_mk_lt(ctx, z, minus_one);
    printf("disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1\n");
    prove(ctx, f, Z3_FALSE);

    Z3_del_context(ctx);
}

/**
   \brief Show how push & pop can be used to create "backtracking"
   points.

   This example also demonstrates how big numbers can be created in Z3.
*/
void push_pop_example1() 
{
    Z3_context ctx;
    Z3_sort int_sort;
    Z3_symbol x_sym, y_sym;
    Z3_ast x, y, big_number, three;
    Z3_ast c1, c2, c3;

    printf("\npush_pop_example1\n");
    LOG_MSG("push_pop_example1");

    ctx        = mk_context();

    /* create a big number */
    int_sort   = Z3_mk_int_sort(ctx);
    big_number = Z3_mk_numeral(ctx, "1000000000000000000000000000000000000000000000000000000", int_sort);
    
    /* create number 3 */
    three      = Z3_mk_numeral(ctx, "3", int_sort);

    /* create x */
    x_sym      = Z3_mk_string_symbol(ctx, "x");
    x          = Z3_mk_const(ctx, x_sym, int_sort);

    /* assert x >= "big number" */
    c1         = Z3_mk_ge(ctx, x, big_number);
    printf("assert: x >= 'big number'\n");
    Z3_assert_cnstr(ctx, c1);

    /* create a backtracking point */
    printf("push\n");
    Z3_push(ctx);

    printf("number of scopes: %d\n", Z3_get_num_scopes(ctx));

    /* assert x <= 3 */
    c2         = Z3_mk_le(ctx, x, three);
    printf("assert: x <= 3\n");
    Z3_assert_cnstr(ctx, c2);

    /* context is inconsistent at this point */
    check2(ctx, Z3_L_FALSE);

    /* backtrack: the constraint x <= 3 will be removed, since it was
       asserted after the last Z3_push. */
    printf("pop\n");
    Z3_pop(ctx, 1);

    printf("number of scopes: %d\n", Z3_get_num_scopes(ctx));


    /* the context is consistent again. */
    check2(ctx, Z3_L_TRUE);

    /* new constraints can be asserted... */
    
    /* create y */
    y_sym      = Z3_mk_string_symbol(ctx, "y");
    y          = Z3_mk_const(ctx, y_sym, int_sort);

    /* assert y > x */
    c3         = Z3_mk_gt(ctx, y, x);
    printf("assert: y > x\n");
    Z3_assert_cnstr(ctx, c3);

    /* the context is still consistent. */
    check2(ctx, Z3_L_TRUE);
    
    Z3_del_context(ctx);
}

/**
   \brief Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when 
   \c f is injective in the second argument.

   \sa assert_inj_axiom.
*/
void quantifier_example1() 
{
    Z3_config  cfg;
    Z3_context ctx;
    Z3_sort       int_sort;
    Z3_symbol         f_name;
    Z3_sort       f_domain[2];
    Z3_func_decl f;
    Z3_ast            x, y, w, v, fxy, fwv;
    Z3_ast            p1, p2, p3, not_p3;

    printf("\nquantifier_example1\n");
    LOG_MSG("quantifier_example1");

    cfg = Z3_mk_config();
    /* If quantified formulas are asserted in a logical context, then
       Z3 may return L_UNDEF. In this case, the model produced by Z3 should be viewed as a potential/candidate model.
    */

    /*
       The current model finder for quantified formulas cannot handle injectivity.
       So, we are limiting the number of iterations to avoid a long "wait".
    */
    Z3_global_param_set("smt.mbqi.max_iterations", "10");
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);

    /* declare function f */
    int_sort    = Z3_mk_int_sort(ctx);
    f_name      = Z3_mk_string_symbol(ctx, "f");
    f_domain[0] = int_sort;
    f_domain[1] = int_sort;
    f           = Z3_mk_func_decl(ctx, f_name, 2, f_domain, int_sort);
  
    /* assert that f is injective in the second argument. */
    assert_inj_axiom(ctx, f, 1);
    
    /* create x, y, v, w, fxy, fwv */
    x           = mk_int_var(ctx, "x");
    y           = mk_int_var(ctx, "y");
    v           = mk_int_var(ctx, "v");
    w           = mk_int_var(ctx, "w");
    fxy         = mk_binary_app(ctx, f, x, y);
    fwv         = mk_binary_app(ctx, f, w, v);
    
    /* assert f(x, y) = f(w, v) */
    p1          = Z3_mk_eq(ctx, fxy, fwv);
    Z3_assert_cnstr(ctx, p1);

    /* prove f(x, y) = f(w, v) implies y = v */
    p2          = Z3_mk_eq(ctx, y, v);
    printf("prove: f(x, y) = f(w, v) implies y = v\n");
    prove(ctx, p2, Z3_TRUE);

    /* disprove f(x, y) = f(w, v) implies x = w */
    /* using check2 instead of prove */
    p3          = Z3_mk_eq(ctx, x, w);
    not_p3      = Z3_mk_not(ctx, p3);
    Z3_assert_cnstr(ctx, not_p3);
    printf("disprove: f(x, y) = f(w, v) implies x = w\n");
    printf("that is: not(f(x, y) = f(w, v) implies x = w) is satisfiable\n");
    check2(ctx, Z3_L_UNDEF);
    printf("reason for last failure: %d (7 = quantifiers)\n", 
           Z3_get_search_failure(ctx));
    if (Z3_get_search_failure(ctx) != Z3_QUANTIFIERS) {
        exitf("unexpected result");
    }
    Z3_del_context(ctx);
    /* reset global parameters set by this function */
    Z3_global_param_reset_all(); 
}

/**
   \brief Prove <tt>store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))</tt>.
   
   This example demonstrates how to use the array theory.
*/
void array_example1() 
{
    Z3_context ctx;
    Z3_sort int_sort, array_sort;
    Z3_ast a1, a2, i1, v1, i2, v2, i3;
    Z3_ast st1, st2, sel1, sel2;
    Z3_ast antecedent, consequent;
    Z3_ast ds[3];
    Z3_ast thm;

    printf("\narray_example1\n");
    LOG_MSG("array_example1");

    ctx = mk_context();

    int_sort    = Z3_mk_int_sort(ctx);
    array_sort  = Z3_mk_array_sort(ctx, int_sort, int_sort);

    a1          = mk_var(ctx, "a1", array_sort);
    a2          = mk_var(ctx, "a2", array_sort);
    i1          = mk_var(ctx, "i1", int_sort);
    i2          = mk_var(ctx, "i2", int_sort);
    i3          = mk_var(ctx, "i3", int_sort);
    v1          = mk_var(ctx, "v1", int_sort);
    v2          = mk_var(ctx, "v2", int_sort);
    
    st1         = Z3_mk_store(ctx, a1, i1, v1);
    st2         = Z3_mk_store(ctx, a2, i2, v2);
    
    sel1        = Z3_mk_select(ctx, a1, i3);
    sel2        = Z3_mk_select(ctx, a2, i3);

    /* create antecedent */
    antecedent  = Z3_mk_eq(ctx, st1, st2);

    /* create consequent: i1 = i3 or  i2 = i3 or select(a1, i3) = select(a2, i3) */
    ds[0]       = Z3_mk_eq(ctx, i1, i3);
    ds[1]       = Z3_mk_eq(ctx, i2, i3);
    ds[2]       = Z3_mk_eq(ctx, sel1, sel2);
    consequent  = Z3_mk_or(ctx, 3, ds);

    /* prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3)) */
    thm         = Z3_mk_implies(ctx, antecedent, consequent);
    printf("prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))\n");
    printf("%s\n", Z3_ast_to_string(ctx, thm));
    prove(ctx, thm, Z3_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Show that <tt>distinct(a_0, ... , a_n)</tt> is
   unsatisfiable when \c a_i's are arrays from boolean to
   boolean and n > 4.

   This example also shows how to use the \c distinct construct.
*/
void array_example2() 
{
    Z3_context ctx;
    Z3_sort bool_sort, array_sort;
    Z3_ast      a[5];
    Z3_ast      d;
    unsigned      i, n;

    printf("\narray_example2\n");
    LOG_MSG("array_example2");

    for (n = 2; n <= 5; n++) {
        printf("n = %d\n", n);
        ctx = mk_context();
        
        bool_sort   = Z3_mk_bool_sort(ctx);
        array_sort  = Z3_mk_array_sort(ctx, bool_sort, bool_sort);
        
        /* create arrays */
        for (i = 0; i < n; i++) {
            Z3_symbol s = Z3_mk_int_symbol(ctx, i);
            a[i]          = Z3_mk_const(ctx, s, array_sort);
        }
        
        /* assert distinct(a[0], ..., a[n]) */
        d = Z3_mk_distinct(ctx, n, a);
        printf("%s\n", Z3_ast_to_string(ctx, d));
        Z3_assert_cnstr(ctx, d);

        /* context is satisfiable if n < 5 */
        check2(ctx, n < 5 ? Z3_L_TRUE : Z3_L_FALSE);
        
        Z3_del_context(ctx);
    }
}

/**
   \brief Simple array type construction/deconstruction example.
*/
void array_example3() 
{
    Z3_context ctx;
    Z3_sort bool_sort, int_sort, array_sort;
    Z3_sort domain, range;
    printf("\narray_example3\n");
    LOG_MSG("array_example3");

    ctx      = mk_context();

    bool_sort  = Z3_mk_bool_sort(ctx);
    int_sort   = Z3_mk_int_sort(ctx); 
    array_sort = Z3_mk_array_sort(ctx, int_sort, bool_sort);

    if (Z3_get_sort_kind(ctx, array_sort) != Z3_ARRAY_SORT) {
        exitf("type must be an array type");
    }
    
    domain = Z3_get_array_sort_domain(ctx, array_sort);
    range  = Z3_get_array_sort_range(ctx, array_sort);

    printf("domain: ");
    display_sort(ctx, stdout, domain);
    printf("\n");
    printf("range:  ");
    display_sort(ctx, stdout, range);
    printf("\n");

	if (int_sort != domain || bool_sort != range) {
        exitf("invalid array type");
    }

    Z3_del_context(ctx);
}

/**
   \brief Simple tuple type example. It creates a tuple that is a pair of real numbers.
*/
void tuple_example1() 
{
    Z3_context         ctx;
    Z3_sort        real_sort, pair_sort;
    Z3_symbol          mk_tuple_name;
    Z3_func_decl  mk_tuple_decl;
    Z3_symbol          proj_names[2]; 
    Z3_sort        proj_sorts[2]; 
    Z3_func_decl  proj_decls[2];
    Z3_func_decl  get_x_decl, get_y_decl;

    printf("\ntuple_example1\n");
    LOG_MSG("tuple_example1");
    
    ctx       = mk_context();

    real_sort = Z3_mk_real_sort(ctx);

    /* Create pair (tuple) type */
    mk_tuple_name = Z3_mk_string_symbol(ctx, "mk_pair");
    proj_names[0] = Z3_mk_string_symbol(ctx, "get_x");
    proj_names[1] = Z3_mk_string_symbol(ctx, "get_y");
    proj_sorts[0] = real_sort;
    proj_sorts[1] = real_sort;
    /* Z3_mk_tuple_sort will set mk_tuple_decl and proj_decls */
    pair_sort     = Z3_mk_tuple_sort(ctx, mk_tuple_name, 2, proj_names, proj_sorts, &mk_tuple_decl, proj_decls);
    get_x_decl    = proj_decls[0]; /* function that extracts the first element of a tuple. */
    get_y_decl    = proj_decls[1]; /* function that extracts the second element of a tuple. */
    
    printf("tuple_sort: ");
    display_sort(ctx, stdout, pair_sort);
    printf("\n");

    {
        /* prove that get_x(mk_pair(x,y)) == 1 implies x = 1*/
        Z3_ast app1, app2, x, y, one;
        Z3_ast eq1, eq2, eq3, thm;
        
        x    = mk_real_var(ctx, "x");
        y    = mk_real_var(ctx, "y");
        app1 = mk_binary_app(ctx, mk_tuple_decl, x, y);
        app2 = mk_unary_app(ctx, get_x_decl, app1); 
        one  = Z3_mk_numeral(ctx, "1", real_sort);
        eq1  = Z3_mk_eq(ctx, app2, one);
        eq2  = Z3_mk_eq(ctx, x, one);
        thm  = Z3_mk_implies(ctx, eq1, eq2);
        printf("prove: get_x(mk_pair(x, y)) = 1 implies x = 1\n");
        prove(ctx, thm, Z3_TRUE);

        /* disprove that get_x(mk_pair(x,y)) == 1 implies y = 1*/
        eq3  = Z3_mk_eq(ctx, y, one);
        thm  = Z3_mk_implies(ctx, eq1, eq3);
        printf("disprove: get_x(mk_pair(x, y)) = 1 implies y = 1\n");
        prove(ctx, thm, Z3_FALSE);
    }

    {
        /* prove that get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2 */
        Z3_ast p1, p2, x1, x2, y1, y2;
        Z3_ast antecedents[2];
        Z3_ast antecedent, consequent, thm;
        
        p1             = mk_var(ctx, "p1", pair_sort);
        p2             = mk_var(ctx, "p2", pair_sort);
        x1             = mk_unary_app(ctx, get_x_decl, p1);
        y1             = mk_unary_app(ctx, get_y_decl, p1);
        x2             = mk_unary_app(ctx, get_x_decl, p2);
        y2             = mk_unary_app(ctx, get_y_decl, p2);
        antecedents[0] = Z3_mk_eq(ctx, x1, x2);
        antecedents[1] = Z3_mk_eq(ctx, y1, y2);
        antecedent     = Z3_mk_and(ctx, 2, antecedents);
        consequent     = Z3_mk_eq(ctx, p1, p2);
        thm            = Z3_mk_implies(ctx, antecedent, consequent);
        printf("prove: get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2\n");
        prove(ctx, thm, Z3_TRUE);

        /* disprove that get_x(p1) = get_x(p2) implies p1 = p2 */
        thm            = Z3_mk_implies(ctx, antecedents[0], consequent);
        printf("disprove: get_x(p1) = get_x(p2) implies p1 = p2\n");
        prove(ctx, thm, Z3_FALSE);
    }

    {
        /* demonstrate how to use the mk_tuple_update function */
        /* prove that p2 = update(p1, 0, 10) implies get_x(p2) = 10 */
        Z3_ast p1, p2, one, ten, updt, x, y;
        Z3_ast antecedent, consequent, thm;

        p1             = mk_var(ctx, "p1", pair_sort);
        p2             = mk_var(ctx, "p2", pair_sort);
        one            = Z3_mk_numeral(ctx, "1", real_sort);
        ten            = Z3_mk_numeral(ctx, "10", real_sort);
        updt           = mk_tuple_update(ctx, p1, 0, ten);
        antecedent     = Z3_mk_eq(ctx, p2, updt);
        x              = mk_unary_app(ctx, get_x_decl, p2);
        consequent     = Z3_mk_eq(ctx, x, ten);
        thm            = Z3_mk_implies(ctx, antecedent, consequent);
        printf("prove: p2 = update(p1, 0, 10) implies get_x(p2) = 10\n");
        prove(ctx, thm, Z3_TRUE);

        /* disprove that p2 = update(p1, 0, 10) implies get_y(p2) = 10 */
        y              = mk_unary_app(ctx, get_y_decl, p2);
        consequent     = Z3_mk_eq(ctx, y, ten);
        thm            = Z3_mk_implies(ctx, antecedent, consequent);
        printf("disprove: p2 = update(p1, 0, 10) implies get_y(p2) = 10\n");
        prove(ctx, thm, Z3_FALSE);
    }

    Z3_del_context(ctx);
}

/**
   \brief Simple bit-vector example. This example disproves that x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers
*/
void bitvector_example1() 
{
    Z3_context         ctx;
    Z3_sort        bv_sort;
    Z3_ast             x, zero, ten, x_minus_ten, c1, c2, thm;

    printf("\nbitvector_example1\n");
    LOG_MSG("bitvector_example1");
    
    ctx       = mk_context();
    
    bv_sort   = Z3_mk_bv_sort(ctx, 32);
    
    x           = mk_var(ctx, "x", bv_sort);
    zero        = Z3_mk_numeral(ctx, "0", bv_sort);
    ten         = Z3_mk_numeral(ctx, "10", bv_sort);
    x_minus_ten = Z3_mk_bvsub(ctx, x, ten);
    /* bvsle is signed less than or equal to */
    c1          = Z3_mk_bvsle(ctx, x, ten);
    c2          = Z3_mk_bvsle(ctx, x_minus_ten, zero);
    thm         = Z3_mk_iff(ctx, c1, c2);
    printf("disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers\n");
    prove(ctx, thm, Z3_FALSE);
    
    Z3_del_context(ctx);
}

/**
   \brief Find x and y such that: x ^ y - 103 == x * y
*/
void bitvector_example2()
{
    Z3_context ctx = mk_context();
 
    /* construct x ^ y - 103 == x * y */
    Z3_sort bv_sort = Z3_mk_bv_sort(ctx, 32);
    Z3_ast x = mk_var(ctx, "x", bv_sort);
    Z3_ast y = mk_var(ctx, "y", bv_sort);
    Z3_ast x_xor_y = Z3_mk_bvxor(ctx, x, y);
    Z3_ast c103 = Z3_mk_numeral(ctx, "103", bv_sort);
    Z3_ast lhs = Z3_mk_bvsub(ctx, x_xor_y, c103);
    Z3_ast rhs = Z3_mk_bvmul(ctx, x, y);
    Z3_ast ctr = Z3_mk_eq(ctx, lhs, rhs);

    printf("\nbitvector_example2\n");
    LOG_MSG("bitvector_example2");
    printf("find values of x and y, such that x ^ y - 103 == x * y\n");
    
    /* add the constraint <tt>x ^ y - 103 == x * y<\tt> to the logical context */
    Z3_assert_cnstr(ctx, ctr);
    
    /* find a model (i.e., values for x an y that satisfy the constraint */
    check(ctx, Z3_L_TRUE);
    
    Z3_del_context(ctx);
}

/**
   \brief Demonstrate how to use #Z3_eval.
*/
void eval_example1() 
{
    Z3_context ctx;
    Z3_ast x, y, two;
    Z3_ast c1, c2;
    Z3_model m;

    printf("\neval_example1\n");
    LOG_MSG("eval_example1");
    
    ctx        = mk_context();
    x          = mk_int_var(ctx, "x");
    y          = mk_int_var(ctx, "y");
    two        = mk_int(ctx, 2);
    
    /* assert x < y */
    c1         = Z3_mk_lt(ctx, x, y);
    Z3_assert_cnstr(ctx, c1);

    /* assert x > 2 */
    c2         = Z3_mk_gt(ctx, x, two);
    Z3_assert_cnstr(ctx, c2);

    /* find model for the constraints above */
    if (Z3_check_and_get_model(ctx, &m) == Z3_L_TRUE) {
        Z3_ast   x_plus_y;
        Z3_ast   args[2] = {x, y};
        Z3_ast v;
        printf("MODEL:\n%s", Z3_model_to_string(ctx, m));
        x_plus_y = Z3_mk_add(ctx, 2, args);
        printf("\nevaluating x+y\n");
        if (Z3_eval(ctx, m, x_plus_y, &v)) {
            printf("result = ");
            display_ast(ctx, stdout, v);
            printf("\n");
        }
        else {
            exitf("failed to evaluate: x+y");
        }
        Z3_del_model(ctx, m);
    }
    else {
        exitf("the constraints are satisfiable");
    }

    Z3_del_context(ctx);
}

/**
   \brief Several logical context can be used simultaneously.
*/
void two_contexts_example1() 
{
    Z3_context ctx1, ctx2;
    Z3_ast x1, x2;

    printf("\ntwo_contexts_example1\n");
    LOG_MSG("two_contexts_example1");

    /* using the same (default) configuration to initialized both logical contexts. */
    ctx1 = mk_context();
    ctx2 = mk_context();
    
    x1 = Z3_mk_const(ctx1, Z3_mk_int_symbol(ctx1,0), Z3_mk_bool_sort(ctx1));
    x2 = Z3_mk_const(ctx2, Z3_mk_int_symbol(ctx2,0), Z3_mk_bool_sort(ctx2));

    Z3_del_context(ctx1);
    
    /* ctx2 can still be used. */
    printf("%s\n", Z3_ast_to_string(ctx2, x2));
    
    Z3_del_context(ctx2);
}

/**
   \brief Demonstrates how error codes can be read insted of registering an error handler.
 */
void error_code_example1() 
{
    Z3_config cfg;
    Z3_context ctx;
    Z3_ast x;
    Z3_model m;
    Z3_ast v;
    Z3_func_decl x_decl;
    const char * str;

    printf("\nerror_code_example1\n");
    LOG_MSG("error_code_example11");

    /* Do not register an error handler, as we want to use Z3_get_error_code manually */
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, NULL);
    Z3_del_config(cfg);

    x          = mk_bool_var(ctx, "x");
    x_decl     = Z3_get_app_decl(ctx, Z3_to_app(ctx, x));
    Z3_assert_cnstr(ctx, x);
    
    if (Z3_check_and_get_model(ctx, &m) != Z3_L_TRUE) {
        exitf("unexpected result");
    }

    if (!Z3_eval_func_decl(ctx, m, x_decl, &v)) {
        exitf("did not obtain value for declaration.\n");
    }
    if (Z3_get_error_code(ctx) == Z3_OK) {
        printf("last call succeeded.\n");
    }
    /* The following call will fail since the value of x is a boolean */
    str = Z3_get_numeral_string(ctx, v);
    if (Z3_get_error_code(ctx) != Z3_OK) {
        printf("last call failed.\n");
    }
    Z3_del_model(ctx, m);
    Z3_del_context(ctx);
}

/**
   \brief Demonstrates how error handlers can be used.
*/
void error_code_example2() {
    Z3_config cfg;
    Z3_context ctx = NULL;
    int r;

    printf("\nerror_code_example2\n");
    LOG_MSG("error_code_example2");
    
    /* low tech try&catch */
    r = setjmp(g_catch_buffer);
    if (r == 0) {
        Z3_ast x, y, app;
        
        cfg = Z3_mk_config();
        ctx = mk_context_custom(cfg, throw_z3_error);
        Z3_del_config(cfg);
        
        x   = mk_int_var(ctx, "x");
        y   = mk_bool_var(ctx, "y");
        printf("before Z3_mk_iff\n"); 
        /* the next call will produce an error */
        app = Z3_mk_iff(ctx, x, y);
        unreachable();
        Z3_del_context(ctx);
    }
    else {
        printf("Z3 error: %s.\n", Z3_get_error_msg((Z3_error_code)r));
        if (ctx != NULL) {
            Z3_del_context(ctx);
        }
    }
}

/**
   \brief Demonstrates how to use the SMTLIB parser.
 */
void parser_example1() 
{
    Z3_context ctx;
    unsigned i, num_formulas;

    printf("\nparser_example1\n");
    LOG_MSG("parser_example1");
    
    ctx        = mk_context();
   
    Z3_parse_smtlib_string(ctx, 
                           "(benchmark tst :extrafuns ((x Int) (y Int)) :formula (> x y) :formula (> x 0))",
                           0, 0, 0,
                           0, 0, 0);
    num_formulas = Z3_get_smtlib_num_formulas(ctx);
    for (i = 0; i < num_formulas; i++) {
        Z3_ast f = Z3_get_smtlib_formula(ctx, i);
        printf("formula %d: %s\n", i, Z3_ast_to_string(ctx, f));
        Z3_assert_cnstr(ctx, f);
    }
    
    check(ctx, Z3_L_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Demonstrates how to initialize the parser symbol table.
 */
void parser_example2() 
{
    Z3_context ctx;
    Z3_ast x, y;
    Z3_symbol         names[2];
    Z3_func_decl decls[2];
    Z3_ast f;

    printf("\nparser_example2\n");
    LOG_MSG("parser_example2");

    ctx        = mk_context();

    /* Z3_enable_arithmetic doesn't need to be invoked in this example
       because it will be implicitly invoked by mk_int_var.
    */
    
    x        = mk_int_var(ctx, "x");
    decls[0] = Z3_get_app_decl(ctx, Z3_to_app(ctx, x));
    y        = mk_int_var(ctx, "y");
    decls[1] = Z3_get_app_decl(ctx, Z3_to_app(ctx, y));
    
    names[0] = Z3_mk_string_symbol(ctx, "a");
    names[1] = Z3_mk_string_symbol(ctx, "b");
    
    Z3_parse_smtlib_string(ctx, 
                           "(benchmark tst :formula (> a b))",
                           0, 0, 0,
                           /* 'x' and 'y' declarations are inserted as 'a' and 'b' into the parser symbol table. */
                           2, names, decls);
    f = Z3_get_smtlib_formula(ctx, 0);
    printf("formula: %s\n", Z3_ast_to_string(ctx, f));
    Z3_assert_cnstr(ctx, f);
    check(ctx, Z3_L_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Demonstrates how to initialize the parser symbol table.
 */
void parser_example3() 
{
    Z3_config  cfg;
    Z3_context ctx;
    Z3_sort       int_sort;
    Z3_symbol     g_name;
    Z3_sort       g_domain[2];
    Z3_func_decl  g;
    Z3_ast        thm;

    printf("\nparser_example3\n");
    LOG_MSG("parser_example3");

    cfg = Z3_mk_config();
    /* See quantifer_example1 */
    Z3_set_param_value(cfg, "model", "true");
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);

    /* declare function g */
    int_sort    = Z3_mk_int_sort(ctx);
    g_name      = Z3_mk_string_symbol(ctx, "g");
    g_domain[0] = int_sort;
    g_domain[1] = int_sort;
    g           = Z3_mk_func_decl(ctx, g_name, 2, g_domain, int_sort);
    
    assert_comm_axiom(ctx, g);

    Z3_parse_smtlib_string(ctx, 
                           "(benchmark tst :formula (forall (x Int) (y Int) (implies (= x y) (= (g x 0) (g 0 y)))))",
                           0, 0, 0,
                           1, &g_name, &g);
    thm = Z3_get_smtlib_formula(ctx, 0);
    printf("formula: %s\n", Z3_ast_to_string(ctx, thm));
    prove(ctx, thm, Z3_TRUE);

    Z3_del_context(ctx);
}

/**
   \brief Display the declarations, assumptions and formulas in a SMT-LIB string.
*/
void parser_example4() 
{
    Z3_context ctx;
    unsigned i, num_decls, num_assumptions, num_formulas;

    printf("\nparser_example4\n");
    LOG_MSG("parser_example4");
    
    ctx        = mk_context();
    
    Z3_parse_smtlib_string(ctx, 
                           "(benchmark tst :extrafuns ((x Int) (y Int)) :assumption (= x 20) :formula (> x y) :formula (> x 0))",
                           0, 0, 0,
                           0, 0, 0);
    num_decls = Z3_get_smtlib_num_decls(ctx);
    for (i = 0; i < num_decls; i++) {
        Z3_func_decl d = Z3_get_smtlib_decl(ctx, i);
        printf("declaration %d: %s\n", i, Z3_func_decl_to_string(ctx, d));
    }
    num_assumptions = Z3_get_smtlib_num_assumptions(ctx);
    for (i = 0; i < num_assumptions; i++) {
        Z3_ast a = Z3_get_smtlib_assumption(ctx, i);
        printf("assumption %d: %s\n", i, Z3_ast_to_string(ctx, a));
    }
    num_formulas = Z3_get_smtlib_num_formulas(ctx);
    for (i = 0; i < num_formulas; i++) {
        Z3_ast f = Z3_get_smtlib_formula(ctx, i);
        printf("formula %d: %s\n", i, Z3_ast_to_string(ctx, f));
    }
    Z3_del_context(ctx);
}

/**
   \brief Demonstrates how to handle parser errors using Z3 error handling support.
*/
void parser_example5() {
    Z3_config  cfg;
    Z3_context ctx = NULL;
    int r;

    printf("\nparser_example5\n");
    LOG_MSG("parser_example5");

    r = setjmp(g_catch_buffer);
    if (r == 0) {
        cfg = Z3_mk_config();
        ctx = mk_context_custom(cfg, throw_z3_error);
        Z3_del_config(cfg);
                
        Z3_parse_smtlib_string(ctx, 
                               /* the following string has a parsing error: missing parenthesis */
                               "(benchmark tst :extrafuns ((x Int (y Int)) :formula (> x y) :formula (> x 0))",
                               0, 0, 0,
                               0, 0, 0);
        unreachable();
        Z3_del_context(ctx);
    }
    else {
        printf("Z3 error: %s.\n", Z3_get_error_msg((Z3_error_code)r));
        if (ctx != NULL) {
            printf("Error message: '%s'.\n",Z3_get_smtlib_error(ctx));
            Z3_del_context(ctx);
        }
    }
}

/**
    \brief Demonstrate different ways of creating rational numbers: decimal and fractional representations.
*/
void numeral_example() {
    Z3_context ctx;
    Z3_ast n1, n2;
    Z3_sort real_ty;
    printf("\nnumeral_example\n");
    LOG_MSG("numeral_example");
    
    ctx        = mk_context();
    real_ty    = Z3_mk_real_sort(ctx);
    n1 = Z3_mk_numeral(ctx, "1/2", real_ty);
    n2 = Z3_mk_numeral(ctx, "0.5", real_ty);
    printf("Numerals n1:%s", Z3_ast_to_string(ctx, n1));
    printf(" n2:%s\n", Z3_ast_to_string(ctx, n2));
    prove(ctx, Z3_mk_eq(ctx, n1, n2), Z3_TRUE);

    n1 = Z3_mk_numeral(ctx, "-1/3", real_ty);
    n2 = Z3_mk_numeral(ctx, "-0.33333333333333333333333333333333333333333333333333", real_ty);
    printf("Numerals n1:%s", Z3_ast_to_string(ctx, n1));
    printf(" n2:%s\n", Z3_ast_to_string(ctx, n2));
    prove(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, n1, n2)), Z3_TRUE);
    Z3_del_context(ctx);
}
 
/**
   \brief Test ite-term (if-then-else terms).
*/
void ite_example() 
{
    Z3_context ctx;
    Z3_ast f, one, zero, ite;
    
    printf("\nite_example\n");
    LOG_MSG("ite_example");

    ctx = mk_context();
    
    f    = Z3_mk_false(ctx);
    one  = mk_int(ctx, 1);
    zero = mk_int(ctx, 0);
    ite  = Z3_mk_ite(ctx, f, one, zero);
    
    printf("term: %s\n", Z3_ast_to_string(ctx, ite));

    /* delete logical context */
    Z3_del_context(ctx);
}

/**
   \brief Create an enumeration data type.
*/
void enum_example() {
    Z3_context ctx = mk_context();
    Z3_sort fruit;
    Z3_symbol name = Z3_mk_string_symbol(ctx, "fruit");
    Z3_symbol enum_names[3];
    Z3_func_decl enum_consts[3];
    Z3_func_decl enum_testers[3];
    Z3_ast apple, orange, banana, fruity;
    Z3_ast ors[3];
    
    printf("\nenum_example\n");
    LOG_MSG("enum_example");

    enum_names[0] = Z3_mk_string_symbol(ctx,"apple");
    enum_names[1] = Z3_mk_string_symbol(ctx,"banana");
    enum_names[2] = Z3_mk_string_symbol(ctx,"orange");

    fruit = Z3_mk_enumeration_sort(ctx, name, 3, enum_names, enum_consts, enum_testers);
       
    printf("%s\n", Z3_func_decl_to_string(ctx, enum_consts[0]));
    printf("%s\n", Z3_func_decl_to_string(ctx, enum_consts[1]));
    printf("%s\n", Z3_func_decl_to_string(ctx, enum_consts[2]));

    printf("%s\n", Z3_func_decl_to_string(ctx, enum_testers[0]));
    printf("%s\n", Z3_func_decl_to_string(ctx, enum_testers[1]));
    printf("%s\n", Z3_func_decl_to_string(ctx, enum_testers[2]));

    apple  = Z3_mk_app(ctx, enum_consts[0], 0, 0);
    banana = Z3_mk_app(ctx, enum_consts[1], 0, 0);
    orange = Z3_mk_app(ctx, enum_consts[2], 0, 0);

    /* Apples are different from oranges */
    prove(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, apple, orange)), Z3_TRUE);

    /* Apples pass the apple test */
    prove(ctx, Z3_mk_app(ctx, enum_testers[0], 1, &apple), Z3_TRUE);

    /* Oranges fail the apple test */
    prove(ctx, Z3_mk_app(ctx, enum_testers[0], 1, &orange), Z3_FALSE);
    prove(ctx, Z3_mk_not(ctx, Z3_mk_app(ctx, enum_testers[0], 1, &orange)), Z3_TRUE);

    fruity = mk_var(ctx, "fruity", fruit);

    /* If something is fruity, then it is an apple, banana, or orange */
    ors[0] = Z3_mk_eq(ctx, fruity, apple);
    ors[1] = Z3_mk_eq(ctx, fruity, banana);
    ors[2] = Z3_mk_eq(ctx, fruity, orange);

    prove(ctx, Z3_mk_or(ctx, 3, ors), Z3_TRUE);

    /* delete logical context */
    Z3_del_context(ctx);
}

/**
   \brief Create a list datatype.
*/
void list_example() {
    Z3_context ctx = mk_context();
    Z3_sort int_ty, int_list;
    Z3_func_decl nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl;
    Z3_ast nil, l1, l2, x, y, u, v, fml, fml1;
    Z3_ast ors[2];
    

    printf("\nlist_example\n");
    LOG_MSG("list_example");

    int_ty = Z3_mk_int_sort(ctx);

    int_list = Z3_mk_list_sort(ctx, Z3_mk_string_symbol(ctx, "int_list"), int_ty,
                               &nil_decl, &is_nil_decl, &cons_decl, &is_cons_decl, &head_decl, &tail_decl);
                    
    nil = Z3_mk_app(ctx, nil_decl, 0, 0);
    l1 = mk_binary_app(ctx, cons_decl, mk_int(ctx, 1), nil);
    l2 = mk_binary_app(ctx, cons_decl, mk_int(ctx, 2), nil);

    /* nil != cons(1, nil) */
    prove(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil, l1)), Z3_TRUE);

    /* cons(2,nil) != cons(1, nil) */
    prove(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, l1, l2)), Z3_TRUE);

    /* cons(x,nil) = cons(y, nil) => x = y */
    x = mk_var(ctx, "x", int_ty);
    y = mk_var(ctx, "y", int_ty);    
    l1 = mk_binary_app(ctx, cons_decl, x, nil);
	l2 = mk_binary_app(ctx, cons_decl, y, nil);
    prove(ctx, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), Z3_TRUE);

    /* cons(x,u) = cons(x, v) => u = v */
    u = mk_var(ctx, "u", int_list);
    v = mk_var(ctx, "v", int_list);    
    l1 = mk_binary_app(ctx, cons_decl, x, u);
	l2 = mk_binary_app(ctx, cons_decl, y, v);
    prove(ctx, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, u, v)), Z3_TRUE);
    prove(ctx, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), Z3_TRUE);

    /* is_nil(u) or is_cons(u) */
    ors[0] = Z3_mk_app(ctx, is_nil_decl, 1, &u);
    ors[1] = Z3_mk_app(ctx, is_cons_decl, 1, &u);
    prove(ctx, Z3_mk_or(ctx, 2, ors), Z3_TRUE);

    /* occurs check u != cons(x,u) */    
    prove(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, u, l1)), Z3_TRUE);

    /* destructors: is_cons(u) => u = cons(head(u),tail(u)) */
    fml1 = Z3_mk_eq(ctx, u, mk_binary_app(ctx, cons_decl, mk_unary_app(ctx, head_decl, u), mk_unary_app(ctx, tail_decl, u)));
    fml = Z3_mk_implies(ctx, Z3_mk_app(ctx, is_cons_decl, 1, &u), fml1);
    printf("Formula %s\n", Z3_ast_to_string(ctx, fml));
    prove(ctx, fml, Z3_TRUE);

    prove(ctx, fml1, Z3_FALSE);

    /* delete logical context */
    Z3_del_context(ctx);
}

/**
   \brief Create a binary tree datatype.
*/ 
void tree_example() {
    Z3_context ctx = mk_context();
    Z3_sort cell;
    Z3_func_decl nil_decl, is_nil_decl, cons_decl, is_cons_decl, car_decl, cdr_decl;
    Z3_ast nil, l1, l2, x, y, u, v, fml, fml1;
    Z3_symbol head_tail[2] = { Z3_mk_string_symbol(ctx, "car"), Z3_mk_string_symbol(ctx, "cdr") };
    Z3_sort sorts[2] = { 0, 0 };
    unsigned sort_refs[2] = { 0, 0 };
    Z3_constructor nil_con, cons_con;
    Z3_constructor constructors[2];
    Z3_func_decl cons_accessors[2];
    Z3_ast ors[2];

    printf("\ntree_example\n");
    LOG_MSG("tree_example");

    nil_con  = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "nil"), Z3_mk_string_symbol(ctx, "is_nil"), 0, 0, 0, 0);
    cons_con = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "cons"), Z3_mk_string_symbol(ctx, "is_cons"), 2, head_tail, sorts, sort_refs);
    constructors[0] = nil_con;
    constructors[1] = cons_con;
    
    cell = Z3_mk_datatype(ctx, Z3_mk_string_symbol(ctx, "cell"), 2, constructors);

    Z3_query_constructor(ctx, nil_con, 0, &nil_decl, &is_nil_decl, 0);
    Z3_query_constructor(ctx, cons_con, 2, &cons_decl, &is_cons_decl, cons_accessors);
    car_decl = cons_accessors[0];
    cdr_decl = cons_accessors[1];

    Z3_del_constructor(ctx,nil_con);
    Z3_del_constructor(ctx,cons_con);


    nil = Z3_mk_app(ctx, nil_decl, 0, 0);
    l1 = mk_binary_app(ctx, cons_decl, nil, nil);
    l2 = mk_binary_app(ctx, cons_decl, l1, nil);

    /* nil != cons(nil, nil) */
    prove(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil, l1)), Z3_TRUE);

    /* cons(x,u) = cons(x, v) => u = v */
    u = mk_var(ctx, "u", cell);
    v = mk_var(ctx, "v", cell);    
    x = mk_var(ctx, "x", cell);
    y = mk_var(ctx, "y", cell);    
    l1 = mk_binary_app(ctx, cons_decl, x, u);
    l2 = mk_binary_app(ctx, cons_decl, y, v);
    prove(ctx, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, u, v)), Z3_TRUE);
    prove(ctx, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), Z3_TRUE);

    /* is_nil(u) or is_cons(u) */
    ors[0] = Z3_mk_app(ctx, is_nil_decl, 1, &u);
    ors[1] = Z3_mk_app(ctx, is_cons_decl, 1, &u);
    prove(ctx, Z3_mk_or(ctx, 2, ors), Z3_TRUE);

    /* occurs check u != cons(x,u) */    
    prove(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, u, l1)), Z3_TRUE);

    /* destructors: is_cons(u) => u = cons(car(u),cdr(u)) */
    fml1 = Z3_mk_eq(ctx, u, mk_binary_app(ctx, cons_decl, mk_unary_app(ctx, car_decl, u), mk_unary_app(ctx, cdr_decl, u)));
    fml = Z3_mk_implies(ctx, Z3_mk_app(ctx, is_cons_decl, 1, &u), fml1);
    printf("Formula %s\n", Z3_ast_to_string(ctx, fml));
    prove(ctx, fml, Z3_TRUE);

    prove(ctx, fml1, Z3_FALSE);

    /* delete logical context */
    Z3_del_context(ctx);


}

/**
   \brief Create a forest of trees.

   forest ::= nil | cons(tree, forest)
   tree   ::= nil | cons(forest, forest)
*/ 

void forest_example() {
    Z3_context ctx = mk_context();
    Z3_sort tree, forest;
    Z3_func_decl nil1_decl, is_nil1_decl, cons1_decl, is_cons1_decl, car1_decl, cdr1_decl;
    Z3_func_decl nil2_decl, is_nil2_decl, cons2_decl, is_cons2_decl, car2_decl, cdr2_decl;
    Z3_ast nil1, nil2, t1, t2, t3, t4, f1, f2, f3, l1, l2, x, y, u, v;
    Z3_symbol head_tail[2] = { Z3_mk_string_symbol(ctx, "car"), Z3_mk_string_symbol(ctx, "cdr") };
    Z3_sort sorts[2] = { 0, 0 };
    unsigned sort_refs[2] = { 0, 0 };
    Z3_constructor nil1_con, cons1_con, nil2_con, cons2_con;
    Z3_constructor constructors1[2], constructors2[2];
    Z3_func_decl cons_accessors[2];
    Z3_ast ors[2];
    Z3_constructor_list clist1, clist2;
    Z3_constructor_list clists[2];
    Z3_symbol sort_names[2] = { Z3_mk_string_symbol(ctx, "forest"), Z3_mk_string_symbol(ctx, "tree") };

    printf("\nforest_example\n");
    LOG_MSG("forest_example");

    /* build a forest */
    nil1_con  = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "nil1"), Z3_mk_string_symbol(ctx, "is_nil1"), 0, 0, 0, 0);
    sort_refs[0] = 1; /* the car of a forest is a tree */
    sort_refs[1] = 0;
    cons1_con = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "cons1"), Z3_mk_string_symbol(ctx, "is_cons1"), 2, head_tail, sorts, sort_refs);
    constructors1[0] = nil1_con;
    constructors1[1] = cons1_con;

    /* build a tree */
    nil2_con  = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "nil2"), Z3_mk_string_symbol(ctx, "is_nil2"),0, 0, 0, 0);
    sort_refs[0] = 0; /* both branches of a tree are forests */
    sort_refs[1] = 0;
    cons2_con = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "cons2"), Z3_mk_string_symbol(ctx, "is_cons2"),2, head_tail, sorts, sort_refs);
    constructors2[0] = nil2_con;
    constructors2[1] = cons2_con;
    
    clist1 = Z3_mk_constructor_list(ctx, 2, constructors1);
    clist2 = Z3_mk_constructor_list(ctx, 2, constructors2);

    clists[0] = clist1;
    clists[1] = clist2;

    Z3_mk_datatypes(ctx, 2, sort_names, sorts, clists);
    forest = sorts[0];
    tree = sorts[1];

    Z3_query_constructor(ctx, nil1_con, 0, &nil1_decl, &is_nil1_decl, 0);
    Z3_query_constructor(ctx, cons1_con, 2, &cons1_decl, &is_cons1_decl, cons_accessors);
    car1_decl = cons_accessors[0];
    cdr1_decl = cons_accessors[1];

    Z3_query_constructor(ctx, nil2_con, 0, &nil2_decl, &is_nil2_decl, 0);
    Z3_query_constructor(ctx, cons2_con, 2, &cons2_decl, &is_cons2_decl, cons_accessors);
    car2_decl = cons_accessors[0];
    cdr2_decl = cons_accessors[1];
    
    Z3_del_constructor_list(ctx, clist1);
    Z3_del_constructor_list(ctx, clist2);
    Z3_del_constructor(ctx,nil1_con);
    Z3_del_constructor(ctx,cons1_con);
    Z3_del_constructor(ctx,nil2_con);
    Z3_del_constructor(ctx,cons2_con);

    nil1 = Z3_mk_app(ctx, nil1_decl, 0, 0);
    nil2 = Z3_mk_app(ctx, nil2_decl, 0, 0);
    f1 = mk_binary_app(ctx, cons1_decl, nil2, nil1);
    t1 = mk_binary_app(ctx, cons2_decl, nil1, nil1);
    t2 = mk_binary_app(ctx, cons2_decl, f1, nil1);
    t3 = mk_binary_app(ctx, cons2_decl, f1, f1);
    t4 = mk_binary_app(ctx, cons2_decl, nil1, f1);
    f2 = mk_binary_app(ctx, cons1_decl, t1, nil1);
    f3 = mk_binary_app(ctx, cons1_decl, t1, f1);


    /* nil != cons(nil,nil) */
    prove(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil1, f1)), Z3_TRUE);
    prove(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil2, t1)), Z3_TRUE);


    /* cons(x,u) = cons(x, v) => u = v */
    u = mk_var(ctx, "u", forest);
    v = mk_var(ctx, "v", forest);    
    x = mk_var(ctx, "x", tree);
    y = mk_var(ctx, "y", tree);
    l1 = mk_binary_app(ctx, cons1_decl, x, u);
    l2 = mk_binary_app(ctx, cons1_decl, y, v);
    prove(ctx, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, u, v)), Z3_TRUE);
    prove(ctx, Z3_mk_implies(ctx, Z3_mk_eq(ctx,l1,l2), Z3_mk_eq(ctx, x, y)), Z3_TRUE);

    /* is_nil(u) or is_cons(u) */
    ors[0] = Z3_mk_app(ctx, is_nil1_decl, 1, &u);
    ors[1] = Z3_mk_app(ctx, is_cons1_decl, 1, &u);
    prove(ctx, Z3_mk_or(ctx, 2, ors), Z3_TRUE);

    /* occurs check u != cons(x,u) */    
    prove(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, u, l1)), Z3_TRUE);

    /* delete logical context */
    Z3_del_context(ctx);
}



/**
   \brief Create a binary tree datatype of the form
        BinTree ::=   nil 
                    | node(value : Int, left : BinTree, right : BinTree)
*/ 
void binary_tree_example() {
    Z3_context ctx = mk_context();
    Z3_sort cell;
    Z3_func_decl 
        nil_decl, /* nil : BinTree   (constructor) */
        is_nil_decl, /* is_nil : BinTree -> Bool (tester, return true if the given BinTree is a nil) */
        node_decl, /* node : Int, BinTree, BinTree -> BinTree  (constructor) */
        is_node_decl, /* is_node : BinTree -> Bool (tester, return true if the given BinTree is a node) */
        value_decl,  /* value : BinTree -> Int  (accessor for nodes) */
        left_decl,   /* left : BinTree -> BinTree (accessor for nodes, retrieves the left child of a node) */
        right_decl;  /* right : BinTree -> BinTree (accessor for nodes, retrieves the right child of a node) */
    Z3_symbol node_accessor_names[3] = { Z3_mk_string_symbol(ctx, "value"), Z3_mk_string_symbol(ctx, "left"), Z3_mk_string_symbol(ctx, "right") };
    Z3_sort   node_accessor_sorts[3] = { Z3_mk_int_sort(ctx), 0, 0 };
    unsigned  node_accessor_sort_refs[3] = { 0, 0, 0 };
    Z3_constructor nil_con, node_con;
    Z3_constructor constructors[2];
    Z3_func_decl node_accessors[3];

    printf("\nbinary_tree_example\n");
    LOG_MSG("binary_tree_example");

    /* nil_con and node_con are auxiliary datastructures used to create the new recursive datatype BinTree */
    nil_con  = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "nil"), Z3_mk_string_symbol(ctx, "is-nil"), 0, 0, 0, 0);
    node_con = Z3_mk_constructor(ctx, Z3_mk_string_symbol(ctx, "node"), Z3_mk_string_symbol(ctx, "is-cons"), 
                                 3, node_accessor_names, node_accessor_sorts, node_accessor_sort_refs);
    constructors[0] = nil_con;
    constructors[1] = node_con;
    
    /* create the new recursive datatype */
    cell = Z3_mk_datatype(ctx, Z3_mk_string_symbol(ctx, "BinTree"), 2, constructors);

    /* retrieve the new declarations: constructors (nil_decl, node_decl), testers (is_nil_decl, is_cons_del), and 
       accessors (value_decl, left_decl, right_decl */
    Z3_query_constructor(ctx, nil_con, 0, &nil_decl, &is_nil_decl, 0);
    Z3_query_constructor(ctx, node_con, 3, &node_decl, &is_node_decl, node_accessors);
    value_decl = node_accessors[0];
    left_decl  = node_accessors[1];
    right_decl = node_accessors[2];

    /* delete auxiliary/helper structures */
    Z3_del_constructor(ctx, nil_con);
    Z3_del_constructor(ctx, node_con);

    /* small example using the recursive datatype BinTree */
    {
        /* create nil */
        Z3_ast nil = Z3_mk_app(ctx, nil_decl, 0, 0);
        /* create node1 ::= node(10, nil, nil) */
        Z3_ast args1[3] = { mk_int(ctx, 10), nil, nil };
        Z3_ast node1    = Z3_mk_app(ctx, node_decl, 3, args1);
        /* create node2 ::= node(30, node1, nil) */
        Z3_ast args2[3] = { mk_int(ctx, 30), node1, nil };
        Z3_ast node2    = Z3_mk_app(ctx, node_decl, 3, args2);
        /* create node3 ::= node(20, node2, node1); */
        Z3_ast args3[3] = { mk_int(ctx, 20), node2, node1 };
        Z3_ast node3    = Z3_mk_app(ctx, node_decl, 3, args3);

        /* prove that nil != node1 */
        prove(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, nil, node1)), Z3_TRUE);

        /* prove that nil = left(node1) */
        prove(ctx, Z3_mk_eq(ctx, nil, mk_unary_app(ctx, left_decl, node1)), Z3_TRUE);

        /* prove that node1 = right(node3) */
        prove(ctx, Z3_mk_eq(ctx, node1, mk_unary_app(ctx, right_decl, node3)), Z3_TRUE);

        /* prove that !is-nil(node2) */
        prove(ctx, Z3_mk_not(ctx, mk_unary_app(ctx, is_nil_decl, node2)), Z3_TRUE);

        /* prove that value(node2) >= 0 */
        prove(ctx, Z3_mk_ge(ctx, mk_unary_app(ctx, value_decl, node2), mk_int(ctx, 0)), Z3_TRUE);
    }

    /* delete logical context */
    Z3_del_context(ctx);
}

/**
   \brief Prove a theorem and extract, and print the proof.

   This example illustrates the use of #Z3_check_assumptions.
*/ 
void unsat_core_and_proof_example() {
    Z3_context ctx = mk_proof_context();
    Z3_ast pa = mk_bool_var(ctx, "PredA");
    Z3_ast pb = mk_bool_var(ctx, "PredB");
    Z3_ast pc = mk_bool_var(ctx, "PredC");
    Z3_ast pd = mk_bool_var(ctx, "PredD");
    Z3_ast p1 = mk_bool_var(ctx, "P1");
    Z3_ast p2 = mk_bool_var(ctx, "P2");
    Z3_ast p3 = mk_bool_var(ctx, "P3");
    Z3_ast p4 = mk_bool_var(ctx, "P4");
    Z3_ast assumptions[4] = { Z3_mk_not(ctx, p1), Z3_mk_not(ctx, p2), Z3_mk_not(ctx, p3), Z3_mk_not(ctx, p4) };
    Z3_ast args1[3] = { pa, pb, pc };
    Z3_ast f1 = Z3_mk_and(ctx, 3, args1);
    Z3_ast args2[3] = { pa, Z3_mk_not(ctx, pb), pc };
    Z3_ast f2 = Z3_mk_and(ctx, 3, args2);
    Z3_ast args3[2] = { Z3_mk_not(ctx, pa), Z3_mk_not(ctx, pc) };
    Z3_ast f3 = Z3_mk_or(ctx, 2, args3);
    Z3_ast f4 = pd;
    Z3_ast g1[2] = { f1, p1 };
    Z3_ast g2[2] = { f2, p2 };
    Z3_ast g3[2] = { f3, p3 };
    Z3_ast g4[2] = { f4, p4 };    
    Z3_ast core[4] = { 0, 0, 0, 0 };
    unsigned core_size = 4;
    Z3_ast proof;
    Z3_model m      = 0;
    Z3_lbool result;
    unsigned i;

    printf("\nunsat_core_and_proof_example\n");
    LOG_MSG("unsat_core_and_proof_example");
    
    Z3_assert_cnstr(ctx, Z3_mk_or(ctx, 2, g1));
    Z3_assert_cnstr(ctx, Z3_mk_or(ctx, 2, g2));
    Z3_assert_cnstr(ctx, Z3_mk_or(ctx, 2, g3));
    Z3_assert_cnstr(ctx, Z3_mk_or(ctx, 2, g4));

    result = Z3_check_assumptions(ctx, 4, assumptions, &m, &proof, &core_size, core);

    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        printf("proof: %s\n", Z3_ast_to_string(ctx, proof));

        printf("\ncore:\n");
        for (i = 0; i < core_size; ++i) {
			printf("%s\n", Z3_ast_to_string(ctx, core[i]));
        }
        printf("\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        printf("potential model:\n");
        display_model(ctx, stdout, m);
        break;
    case Z3_L_TRUE:
        printf("sat\n");
        display_model(ctx, stdout, m);
        break;
    }
    if (m) {
        Z3_del_model(ctx, m);
    }

    /* delete logical context */
    Z3_del_context(ctx);
}

#define MAX_RETRACTABLE_ASSERTIONS 1024

/**
   \brief Very simple logical context wrapper with support for retractable constraints.
   A retractable constraint can be "removed" without using push/pop.
*/
typedef struct {
    Z3_context m_context;
    // IMPORTANT: the fields m_answer_literals, m_retracted and m_num_answer_literals must be saved/restored
    // if push/pop operations are performed on m_context.
    Z3_ast     m_answer_literals[MAX_RETRACTABLE_ASSERTIONS];
    Z3_bool    m_retracted[MAX_RETRACTABLE_ASSERTIONS]; // true if the assertion was retracted.
    unsigned   m_num_answer_literals;
} Z3_ext_context_struct;

typedef Z3_ext_context_struct * Z3_ext_context;

/**
   \brief Create a logical context wrapper with support for retractable constraints.
 */
Z3_ext_context mk_ext_context() {
    Z3_ext_context ctx         = (Z3_ext_context) malloc(sizeof(Z3_ext_context_struct));
    ctx->m_context             = mk_context();
    ctx->m_num_answer_literals = 0;
    return ctx;
}

/**
   \brief Delete the given logical context wrapper.
*/
void del_ext_context(Z3_ext_context ctx) {
    Z3_del_context(ctx->m_context);
    free(ctx);
}

/**
   \brief Create a retractable constraint.
   
   \return An id that can be used to retract/reassert the constraint.
*/
unsigned assert_retractable_cnstr(Z3_ext_context ctx, Z3_ast c) {
    unsigned result;
    Z3_sort ty;
    Z3_ast ans_lit;
    Z3_ast args[2];
    if (ctx->m_num_answer_literals == MAX_RETRACTABLE_ASSERTIONS) {
        exitf("maximum number of retractable constraints was exceeded.");
    }
    ty      = Z3_mk_bool_sort(ctx->m_context);
    ans_lit = Z3_mk_fresh_const(ctx->m_context, "k", ty);
    result  = ctx->m_num_answer_literals;
    ctx->m_answer_literals[result] = ans_lit;
    ctx->m_retracted[result]       = Z3_FALSE;
    ctx->m_num_answer_literals++;
    // assert: c OR (not ans_lit)
    args[0] = c;
    args[1] = Z3_mk_not(ctx->m_context, ans_lit);
    Z3_assert_cnstr(ctx->m_context, Z3_mk_or(ctx->m_context, 2, args));
    return result;
}

/**
   \brief Retract an constraint asserted using #assert_retractable_cnstr.
*/
void retract_cnstr(Z3_ext_context ctx, unsigned id) {
    if (id >= ctx->m_num_answer_literals) {
        exitf("invalid constraint id.");
    }
    ctx->m_retracted[id] = Z3_TRUE;
}

/**
   \brief Reassert a constraint retracted using #retract_cnstr.
*/
void reassert_cnstr(Z3_ext_context ctx, unsigned id) {
    if (id >= ctx->m_num_answer_literals) {
        exitf("invalid constraint id.");
    }
    ctx->m_retracted[id] = Z3_FALSE;
}

/**
   \brief Check whether the logical context wrapper with support for retractable assertions is feasible or not.
*/
Z3_lbool ext_check(Z3_ext_context ctx) {
    Z3_lbool result;
    unsigned num_assumptions = 0;
    Z3_ast assumptions[MAX_RETRACTABLE_ASSERTIONS];
    Z3_ast core[MAX_RETRACTABLE_ASSERTIONS];
    unsigned core_size;
    Z3_ast   dummy_proof = 0; // we don't care about the proof in this example.
    Z3_model dummy_model = 0; // we don't care about the model in this example.
    unsigned i;
    for (i = 0; i < ctx->m_num_answer_literals; i++) {
        if (ctx->m_retracted[i] == Z3_FALSE) {
            // Since the answer literal was not retracted, we added it as an assumption.
            // Recall that we assert (C \/ (not ans_lit)). Therefore, adding ans_lit as an assumption has the effect of "asserting" C.
            // If the constraint was "retracted" (ctx->m_retracted[i] == Z3_true), then we don't really need to add (not ans_lit) as an assumption.
            assumptions[num_assumptions] = ctx->m_answer_literals[i];
            num_assumptions ++;
        }
    }
    result = Z3_check_assumptions(ctx->m_context, num_assumptions, assumptions, &dummy_model, &dummy_proof, &core_size, core);
    if (result == Z3_L_FALSE) {
        // Display the UNSAT core
        printf("unsat core: ");
        for (i = 0; i < core_size; i++) {
            // In this example, we display the core based on the assertion ids.
            unsigned j;
            for (j = 0; j < ctx->m_num_answer_literals; j++) {
                if (core[i] == ctx->m_answer_literals[j]) {
                    printf("%d ", j);
                    break;
                }
            }
            if (j == ctx->m_num_answer_literals) {
                exitf("bug in Z3, the core contains something that is not an assumption.");
            }
        }
        printf("\n");
    }

    if (dummy_model) {
        Z3_del_model(ctx->m_context, dummy_model);
    }

    return result;
}

/**
   \brief Simple example using the functions: #mk_ext_context, #assert_retractable_cnstr, #retract_cnstr, #reassert_cnstr and #del_ext_context.
*/
void incremental_example1() {
    Z3_ext_context ext_ctx = mk_ext_context();
    Z3_context     ctx     = ext_ctx->m_context;
    Z3_ast x, y, z, two, one;
    unsigned c1, c2, c3, c4;
    Z3_bool result;

    printf("\nincremental_example1\n");
    LOG_MSG("incremental_example1");

    x          = mk_int_var(ctx, "x");
    y          = mk_int_var(ctx, "y");
    z          = mk_int_var(ctx, "z");
    two        = mk_int(ctx, 2);
    one        = mk_int(ctx, 1);
    
    /* assert x < y */
    c1 = assert_retractable_cnstr(ext_ctx, Z3_mk_lt(ctx, x, y));
    /* assert x = z */
    c2 = assert_retractable_cnstr(ext_ctx, Z3_mk_eq(ctx, x, z));
    /* assert x > 2 */
    c3 = assert_retractable_cnstr(ext_ctx, Z3_mk_gt(ctx, x, two));
    /* assert y < 1 */
    c4 = assert_retractable_cnstr(ext_ctx, Z3_mk_lt(ctx, y, one));
    
    result = ext_check(ext_ctx); 
    if (result != Z3_L_FALSE)
        exitf("bug in Z3");
    printf("unsat\n");

    retract_cnstr(ext_ctx, c4);
    result = ext_check(ext_ctx);
    if (result != Z3_L_TRUE)
        exitf("bug in Z3");
    printf("sat\n");

    reassert_cnstr(ext_ctx, c4);
    result = ext_check(ext_ctx);
    if (result != Z3_L_FALSE)
        exitf("bug in Z3");
    printf("unsat\n");

    retract_cnstr(ext_ctx, c2);
    result = ext_check(ext_ctx);
    if (result != Z3_L_FALSE)
        exitf("bug in Z3");
    printf("unsat\n");

    retract_cnstr(ext_ctx, c3);
    result = ext_check(ext_ctx);
    if (result != Z3_L_TRUE)
        exitf("bug in Z3");
    printf("sat\n");

    del_ext_context(ext_ctx);
}

/**
   \brief Simple example showing how to use reference counters in Z3
   to manage memory efficiently.
*/
void reference_counter_example() {
    Z3_config cfg;
    Z3_context ctx;
    Z3_sort ty;
    Z3_ast x, y, x_xor_y;
    Z3_symbol sx, sy;

    printf("\nreference_counter_example\n");
    LOG_MSG("reference_counter_example");

    cfg                = Z3_mk_config();
    Z3_set_param_value(cfg, "model", "true");
    // Create a Z3 context where the user is reponsible for managing
    // Z3_ast reference counters.
    ctx                = Z3_mk_context_rc(cfg);
    Z3_del_config(cfg); 

    ty      = Z3_mk_bool_sort(ctx);
    Z3_inc_ref(ctx, Z3_sort_to_ast(ctx, ty)); // Z3_sort_to_ast(ty) is just syntax sugar for ((Z3_ast) ty)
    sx      = Z3_mk_string_symbol(ctx, "x");
    // Z3_symbol is not a Z3_ast. No reference counting is not needed.
    x       = Z3_mk_const(ctx, sx, ty);
    Z3_inc_ref(ctx, x);
    sy      = Z3_mk_string_symbol(ctx, "y");
    y       = Z3_mk_const(ctx, sy, ty);
    Z3_inc_ref(ctx, y);
    // ty is not needed anymore.
    Z3_dec_ref(ctx, Z3_sort_to_ast(ctx, ty)); 
    x_xor_y = Z3_mk_xor(ctx, x, y);
    Z3_inc_ref(ctx, x_xor_y);
    // x and y are not needed anymore.
    Z3_dec_ref(ctx, x); 
    Z3_dec_ref(ctx, y);
    Z3_assert_cnstr(ctx, x_xor_y);
    // x_or_y is not needed anymore.
    Z3_dec_ref(ctx, x_xor_y); 
    
    printf("model for: x xor y\n");
    check(ctx, Z3_L_TRUE);

    // Test push & pop
    Z3_push(ctx);
    Z3_pop(ctx, 1);

    Z3_del_context(ctx);
}

/**
   \brief Demonstrates how to use SMT2 parser.
*/
void smt2parser_example() {
    Z3_context ctx;
    Z3_ast fs;
    printf("\nsmt2parser_example\n");
    LOG_MSG("smt2parser_example");

    ctx = mk_context();
    fs  = Z3_parse_smtlib2_string(ctx, "(declare-fun a () (_ BitVec 8)) (assert (bvuge a #x10)) (assert (bvule a #xf0))", 0, 0, 0, 0, 0, 0);
    printf("formulas: %s\n", Z3_ast_to_string(ctx, fs));
    Z3_del_context(ctx);
}

/**
   \brief Demonstrates how to use the function \c Z3_substitute to replace subexpressions in a Z3 AST.
*/
void substitute_example() {
    Z3_context ctx;
    Z3_sort int_ty;
    Z3_ast a, b;
    Z3_func_decl f;
    Z3_func_decl g;
    Z3_ast fab, ga, ffabga, r;

    printf("\nsubstitute_example\n");
    LOG_MSG("substitute_example");

    ctx = mk_context();
    int_ty = Z3_mk_int_sort(ctx);
    a = mk_int_var(ctx,"a");
    b = mk_int_var(ctx,"b");
    { 
        Z3_sort f_domain[2] = { int_ty, int_ty };
        f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "f"), 2, f_domain, int_ty);
    }
    g = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "g"), 1, &int_ty, int_ty);
    { 
        Z3_ast args[2] = { a, b };
        fab = Z3_mk_app(ctx, f, 2, args);
    }
    ga = Z3_mk_app(ctx, g, 1, &a);
    {
        Z3_ast args[2] = { fab, ga };
        ffabga = Z3_mk_app(ctx, f, 2, args);
    }
    // Replace b -> 0, g(a) -> 1 in f(f(a, b), g(a))
    {
        Z3_ast zero = Z3_mk_numeral(ctx, "0", int_ty);
        Z3_ast one  = Z3_mk_numeral(ctx, "1", int_ty);
        Z3_ast from[2] = { b, ga };
        Z3_ast to[2] = { zero, one };
        r = Z3_substitute(ctx, ffabga, 2, from, to);
    }
    // Display r
    printf("substitution result: %s\n", Z3_ast_to_string(ctx, r));
    Z3_del_context(ctx);
}

/**
   \brief Demonstrates how to use the function \c Z3_substitute_vars to replace (free) variables with expressions in a Z3 AST.
*/
void substitute_vars_example() {
    Z3_context ctx;
    Z3_sort int_ty;
    Z3_ast x0, x1;
    Z3_ast a, b, gb;
    Z3_func_decl f;
    Z3_func_decl g;
    Z3_ast f01, ff010, r;

    printf("\nsubstitute_vars_example\n");
    LOG_MSG("substitute_vars_example");

    ctx = mk_context();
    int_ty = Z3_mk_int_sort(ctx);
    x0 = Z3_mk_bound(ctx, 0, int_ty);
    x1 = Z3_mk_bound(ctx, 1, int_ty);
    { 
        Z3_sort f_domain[2] = { int_ty, int_ty };
        f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "f"), 2, f_domain, int_ty);
    }
    g = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "g"), 1, &int_ty, int_ty);
    { 
        Z3_ast args[2] = { x0, x1 };
        f01 = Z3_mk_app(ctx, f, 2, args);
    }
    {
        Z3_ast args[2] = { f01, x0 };
        ff010 = Z3_mk_app(ctx, f, 2, args);
    }
    a = mk_int_var(ctx, "a");
    b = mk_int_var(ctx, "b");
    gb = Z3_mk_app(ctx, g, 1, &b);
    // Replace x0 -> a, x1 -> g(b) in f(f(x0,x1),x0)
    {
        Z3_ast to[2] = { a, gb };
        r = Z3_substitute_vars(ctx, ff010, 2, to);
    }
    // Display r
    printf("substitution result: %s\n", Z3_ast_to_string(ctx, r));
    Z3_del_context(ctx);
}

/**
   \brief Demonstrates some basic features of the FloatingPoint theory.
*/

void fpa_example() {
    Z3_config cfg;
    Z3_context ctx;
    Z3_sort double_sort, rm_sort;
    Z3_symbol s_rm, s_x, s_y, s_x_plus_y;
    Z3_ast rm, x, y, n, x_plus_y, c1, c2, c3, c4, c5, c6;
	Z3_ast args[2], args2[2], and_args[3], args3[3];

    printf("\nFPA-example\n");
    LOG_MSG("FPA-example");
        
    cfg = Z3_mk_config();
    ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    double_sort = Z3_mk_fpa_sort(ctx, 11, 53);
    rm_sort = Z3_mk_fpa_rounding_mode_sort(ctx);

	// Show that there are x, y s.t. (x + y) = 42.0 (with rounding mode).    
	s_rm = Z3_mk_string_symbol(ctx, "rm");
	rm = Z3_mk_const(ctx, s_rm, rm_sort);
	s_x = Z3_mk_string_symbol(ctx, "x");
	s_y = Z3_mk_string_symbol(ctx, "y");
	x = Z3_mk_const(ctx, s_x, double_sort);
	y = Z3_mk_const(ctx, s_y, double_sort);
	n = Z3_mk_fpa_numeral_double(ctx, 42.0, double_sort);

	s_x_plus_y = Z3_mk_string_symbol(ctx, "x_plus_y");
	x_plus_y = Z3_mk_const(ctx, s_x_plus_y, double_sort);
	c1 = Z3_mk_eq(ctx, x_plus_y, Z3_mk_fpa_add(ctx, rm, x, y));

	args[0] = c1;
	args[1] = Z3_mk_eq(ctx, x_plus_y, n);
	c2 = Z3_mk_and(ctx, 2, (Z3_ast*)&args);

	args2[0] = c2;
	args2[1] = Z3_mk_not(ctx, Z3_mk_eq(ctx, rm, Z3_mk_fpa_rtz(ctx)));
	c3 = Z3_mk_and(ctx, 2, (Z3_ast*)&args2);

	and_args[0] = Z3_mk_not(ctx, Z3_mk_fpa_is_zero(ctx, y));
	and_args[1] = Z3_mk_not(ctx, Z3_mk_fpa_is_nan(ctx, y));
	and_args[2] = Z3_mk_not(ctx, Z3_mk_fpa_is_infinite(ctx, y));
	args3[0] = c3;
	args3[1] = Z3_mk_and(ctx, 3, and_args);
	c4 = Z3_mk_and(ctx, 2, (Z3_ast*)&args3);
        
	printf("c4: %s\n", Z3_ast_to_string(ctx, c4));
	Z3_push(ctx);                  
	Z3_assert_cnstr(ctx, c4);
	check(ctx, Z3_L_TRUE);
	Z3_pop(ctx, 1);

	// Show that the following are equal:
	//   (fp #b0 #b10000000001 #xc000000000000) 
	//   ((_ to_fp 11 53) #x401c000000000000))
	//   ((_ to_fp 11 53) RTZ 1.75 2)))
	//   ((_ to_fp 11 53) RTZ 7.0)))
	
	Z3_push(ctx);
	c1 = Z3_mk_fpa_fp(ctx, 
					  Z3_mk_numeral(ctx, "0", Z3_mk_bv_sort(ctx, 1)),
					  Z3_mk_numeral(ctx, "3377699720527872", Z3_mk_bv_sort(ctx, 52)),
					  Z3_mk_numeral(ctx, "1025", Z3_mk_bv_sort(ctx, 11)));
	c2 = Z3_mk_fpa_to_fp_bv(ctx,
							Z3_mk_numeral(ctx, "4619567317775286272", Z3_mk_bv_sort(ctx, 64)),
							Z3_mk_fpa_sort(ctx, 11, 53));
	c3 = Z3_mk_fpa_to_fp_int_real(ctx,
                                  Z3_mk_fpa_rtz(ctx),
								  Z3_mk_numeral(ctx, "2", Z3_mk_int_sort(ctx)),
                                  Z3_mk_numeral(ctx, "1.75", Z3_mk_real_sort(ctx)),                                  
                                  Z3_mk_fpa_sort(ctx, 11, 53));
	c4 = Z3_mk_fpa_to_fp_real(ctx,
							  Z3_mk_fpa_rtz(ctx),
							  Z3_mk_numeral(ctx, "7.0", Z3_mk_real_sort(ctx)),
							  Z3_mk_fpa_sort(ctx, 11, 53));
	args3[0] = Z3_mk_eq(ctx, c1, c2);
	args3[1] = Z3_mk_eq(ctx, c1, c3);
	args3[2] = Z3_mk_eq(ctx, c1, c4);
	c5 = Z3_mk_and(ctx, 3, args3);

	printf("c5: %s\n", Z3_ast_to_string(ctx, c5));
	Z3_assert_cnstr(ctx, c5);
	check(ctx, Z3_L_TRUE);
	Z3_pop(ctx, 1);

    Z3_del_context(ctx);
}

/*@}*/
/*@}*/

int main() {
#ifdef LOG_Z3_CALLS
    Z3_open_log("z3.log");
#endif
    display_version();
    simple_example();
    demorgan();
    find_model_example1();
    find_model_example2();
    prove_example1();
    prove_example2();
    push_pop_example1();
    quantifier_example1();
    array_example1();
    array_example2();
    array_example3();
    tuple_example1();
    bitvector_example1();
    bitvector_example2();
    eval_example1();
    two_contexts_example1();
    error_code_example1();
    error_code_example2();
    parser_example1();
    parser_example2();
    parser_example3();
    parser_example4();
    parser_example5();
    numeral_example();
    ite_example();
    list_example();
    tree_example();
    forest_example();
    binary_tree_example();
    enum_example();
    unsat_core_and_proof_example();
    incremental_example1();
    reference_counter_example();
    smt2parser_example();
    substitute_example();
    substitute_vars_example();
    fpa_example();
    return 0;
}
