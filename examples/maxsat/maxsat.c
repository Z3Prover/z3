
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

/*
  Simple MAXSAT solver on top of the Z3 API.
*/
#include<stdio.h>
#include<stdlib.h>
#include<memory.h>
#include<z3.h>

/** 
   \defgroup maxsat_ex MaxSAT/MaxSMT examples
*/
/*@{*/

/**
   \brief Exit gracefully in case of error.
*/
void error(char * msg) 
{
    fprintf(stderr, "%s\n", msg);
    exit(1);
}

/**
   \brief Create a logical context.
   Enable model construction only.
*/
Z3_context mk_context() 
{
    Z3_config  cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "MODEL", "true");
    ctx = Z3_mk_context(cfg);
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
   \brief Create a fresh boolean variable.
*/
Z3_ast mk_fresh_bool_var(Z3_context ctx) 
{
    return Z3_mk_fresh_const(ctx, "k", Z3_mk_bool_sort(ctx));
}

/**
   \brief Create an array with \c num_vars fresh boolean variables.
*/
Z3_ast * mk_fresh_bool_var_array(Z3_context ctx, unsigned num_vars) 
{
    Z3_ast * result = (Z3_ast *) malloc(sizeof(Z3_ast) * num_vars);
    unsigned i;
    for (i = 0; i < num_vars; i++) {
        result[i] = mk_fresh_bool_var(ctx);
    }
    return result;
}

/**
   \brief Delete array of boolean variables.
*/
void del_bool_var_array(Z3_ast * arr) 
{
    free(arr);
}

/**
   \brief Create a binary OR.
*/
Z3_ast mk_binary_or(Z3_context ctx, Z3_ast in_1, Z3_ast in_2) 
{
    Z3_ast args[2] = { in_1, in_2 };
    return Z3_mk_or(ctx, 2, args);
}

/**
   \brief Create a ternary OR.
*/
Z3_ast mk_ternary_or(Z3_context ctx, Z3_ast in_1, Z3_ast in_2, Z3_ast in_3) 
{
    Z3_ast args[3] = { in_1, in_2, in_3 };
    return Z3_mk_or(ctx, 3, args);
}

/**
   \brief Create a binary AND.
*/
Z3_ast mk_binary_and(Z3_context ctx, Z3_ast in_1, Z3_ast in_2) 
{
    Z3_ast args[2] = { in_1, in_2 };
    return Z3_mk_and(ctx, 2, args);
}



/**
   \brief Free the given array of cnstrs that was allocated using get_hard_constraints or get_soft_constraints. 
*/
void free_cnstr_array(Z3_ast * cnstrs) 
{
    free(cnstrs);
}

/**
   \brief Assert hard constraints stored in the given array.
*/
void assert_hard_constraints(Z3_context ctx, Z3_solver s, unsigned num_cnstrs, Z3_ast * cnstrs) 
{
    unsigned i;
    for (i = 0; i < num_cnstrs; i++) {
        Z3_solver_assert(ctx, s, cnstrs[i]);
    }
}

/**
   \brief Assert soft constraints stored in the given array.
   This function will assert each soft-constraint C_i as (C_i or k_i) where k_i is a fresh boolean variable.
   It will also return an array containing these fresh variables.
*/
Z3_ast * assert_soft_constraints(Z3_context ctx, Z3_solver s, unsigned num_cnstrs, Z3_ast * cnstrs) 
{
    unsigned i;
    Z3_ast * aux_vars;
    aux_vars = mk_fresh_bool_var_array(ctx, num_cnstrs);
    for (i = 0; i < num_cnstrs; i++) {
        Z3_ast assumption = cnstrs[i];
        Z3_solver_assert(ctx, s, mk_binary_or(ctx, assumption, aux_vars[i]));
    }
    return aux_vars;
}

/**
   \brief Create a full adder with inputs \c in_1, \c in_2 and \c cin.
   The output of the full adder is stored in \c out, and the carry in \c c_out.
*/
void mk_full_adder(Z3_context ctx, Z3_ast in_1, Z3_ast in_2, Z3_ast cin, Z3_ast * out, Z3_ast * cout) 
{
    *cout = mk_ternary_or(ctx, mk_binary_and(ctx, in_1, in_2), mk_binary_and(ctx, in_1, cin), mk_binary_and(ctx, in_2, cin));
    *out  = Z3_mk_xor(ctx, Z3_mk_xor(ctx, in_1, in_2), cin);
}

/**
   \brief Create an adder for inputs of size \c num_bits.
   The arguments \c in1 and \c in2 are arrays of bits of size \c num_bits.
   
   \remark \c result must be an array of size \c num_bits + 1.
*/
void mk_adder(Z3_context ctx, unsigned num_bits, Z3_ast * in_1, Z3_ast * in_2, Z3_ast * result) 
{
    Z3_ast cin, cout, out;
    unsigned i;
    cin = Z3_mk_false(ctx);
    for (i = 0; i < num_bits; i++) {
        mk_full_adder(ctx, in_1[i], in_2[i], cin, &out, &cout);
        result[i] = out;
        cin = cout;
    }
    result[num_bits] = cout;
}

/**
   \brief Given \c num_ins "numbers" of size \c num_bits stored in \c in.
   Create floor(num_ins/2) adder circuits. Each circuit is adding two consecutive "numbers".
   The numbers are stored one after the next in the array \c in.
   That is, the array \c in has size num_bits * num_ins.
   Return an array of bits containing \c ceil(num_ins/2) numbers of size \c (num_bits + 1). 
   If num_ins/2 is not an integer, then the last "number" in the output, is the last "number" in \c in with an appended "zero".
*/
void mk_adder_pairs(Z3_context ctx, unsigned num_bits, unsigned num_ins, Z3_ast * in, unsigned * out_num_ins, Z3_ast * out) 
{
    unsigned out_num_bits = num_bits + 1;
    unsigned i            = 0;
    Z3_ast * _in          = in;
    Z3_ast * _out         = out;
    *out_num_ins  = (num_ins % 2 == 0) ? (num_ins / 2) : (num_ins / 2) + 1;
    for (i = 0; i < num_ins / 2; i++) {
        mk_adder(ctx, num_bits, _in, _in + num_bits, _out);
        _in  += num_bits;
        _in  += num_bits;
        _out += out_num_bits;
    }
    if (num_ins % 2 != 0) {
        for (i = 0; i < num_bits; i++) {
            _out[i] = _in[i];
        }
        _out[num_bits] = Z3_mk_false(ctx);
    }
}

/**
   \brief Create a counter circuit to count the number of "ones" in lits.
   The function returns an array of bits (i.e. boolean expressions) containing the output of the circuit.
   The size of the array is stored in out_sz.
*/
Z3_ast * mk_counter_circuit(Z3_context ctx, unsigned n, Z3_ast * lits, unsigned * out_sz) 
{
    unsigned num_ins  = n;
    unsigned num_bits = 1;
    Z3_ast * aux_1;
    Z3_ast * aux_2;
    if (n == 0)
        return 0;
    aux_1    = (Z3_ast *) malloc(sizeof(Z3_ast) * (n + 1)); 
    aux_2    = (Z3_ast *) malloc(sizeof(Z3_ast) * (n + 1)); 
    memcpy(aux_1, lits, sizeof(Z3_ast) * n);
    while (num_ins > 1) {
        unsigned new_num_ins;
        Z3_ast * tmp;
        mk_adder_pairs(ctx, num_bits, num_ins, aux_1, &new_num_ins, aux_2);
        num_ins = new_num_ins;
        num_bits++;
#ifdef MAXSAT_DEBUG
        {
            unsigned i;
            printf("num_bits: %d, num_ins: %d \n", num_bits, num_ins);
            for (i = 0; i < num_ins * num_bits; i++) {
                printf("bit %d:\n%s\n", i, Z3_ast_to_string(ctx, aux_2[i]));
            }
            printf("-----------\n");
        }
#endif
        tmp   = aux_1;
        aux_1 = aux_2;
        aux_2 = tmp;
    }
    *out_sz = num_bits;
    free(aux_2);
    return aux_1;
}

/**
   \brief Return the \c idx bit of \c val.
*/
int get_bit(unsigned val, unsigned idx) 
{
    unsigned mask = 1 << (idx & 31);
    return (val & mask) != 0;
}

/**
   \brief Given an integer val encoded in n bits (boolean variables), assert the constraint that val <= k.
*/
void assert_le_k(Z3_context ctx, Z3_solver s, unsigned n, Z3_ast * val, unsigned k) 
{
    Z3_ast i1, i2, not_val, out;
    unsigned idx;
    not_val = Z3_mk_not(ctx, val[0]);
    if (get_bit(k, 0))
        out = Z3_mk_true(ctx);
    else
        out = not_val;
    for (idx = 1; idx < n; idx++) {
        not_val = Z3_mk_not(ctx, val[idx]);
        if (get_bit(k, idx)) {
            i1 = not_val;
            i2 = out;
        }
        else {
            i1 = Z3_mk_false(ctx);
            i2 = Z3_mk_false(ctx);
        }
        out = mk_ternary_or(ctx, i1, i2, mk_binary_and(ctx, not_val, out));
    }
    // printf("at-most-k:\n%s\n", Z3_ast_to_string(ctx, out));
    Z3_solver_assert(ctx, s, out);
}

/**
   \brief Assert that at most \c k literals in \c lits can be true,
   where \c n is the number of literals in lits.
   
   We use a simple encoding using an adder (counter). 
   An interesting exercise consists in implementing more sophisticated encodings.
*/
void assert_at_most_k(Z3_context ctx, Z3_solver s, unsigned n, Z3_ast * lits, unsigned k)
{
    Z3_ast * counter_bits;
    unsigned counter_bits_sz;
    if (k >= n || n <= 1)
        return; /* nothing to be done */
    counter_bits = mk_counter_circuit(ctx, n, lits, &counter_bits_sz);
    assert_le_k(ctx, s, counter_bits_sz, counter_bits, k);
    del_bool_var_array(counter_bits);
}

/**
   \brief Assert that at most one literal in \c lits can be true,
   where \c n is the number of literals in lits.
*/
void assert_at_most_one(Z3_context ctx, Z3_solver s, unsigned n, Z3_ast * lits) 
{
    assert_at_most_k(ctx, s, n, lits, 1);
}


Z3_solver mk_solver(Z3_context ctx)
{
    Z3_solver r = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, r);
    return r;
}

/**
   \brief Small test for the at-most-one constraint.
*/
void tst_at_most_one() 
{
    Z3_context ctx = mk_context();
    Z3_solver s    = mk_solver(ctx);
    Z3_ast k1      = mk_bool_var(ctx, "k1");
    Z3_ast k2      = mk_bool_var(ctx, "k2");
    Z3_ast k3      = mk_bool_var(ctx, "k3");
    Z3_ast k4      = mk_bool_var(ctx, "k4");
    Z3_ast k5      = mk_bool_var(ctx, "k5");
    Z3_ast k6      = mk_bool_var(ctx, "k6");
    Z3_ast args1[5] = { k1, k2, k3, k4, k5 };
    Z3_ast args2[3] = { k4, k5, k6 };
    Z3_model m      = 0;
    Z3_lbool result;
    printf("testing at-most-one constraint\n");
    assert_at_most_one(ctx, s, 5, args1);
    assert_at_most_one(ctx, s, 3, args2);
    printf("it must be sat...\n");
    result = Z3_solver_check(ctx, s);
    if (result != Z3_L_TRUE)
        error("BUG");
    m = Z3_solver_get_model(ctx, s);
    Z3_model_inc_ref(ctx, m);
    printf("model:\n%s\n", Z3_model_to_string(ctx, m));
    Z3_model_dec_ref(ctx, m);
    Z3_solver_assert(ctx, s, mk_binary_or(ctx, k2, k3));
    Z3_solver_assert(ctx, s, mk_binary_or(ctx, k1, k6));
    printf("it must be sat...\n");
    result = Z3_solver_check(ctx, s);
    if (result != Z3_L_TRUE)
        error("BUG");
    m = Z3_solver_get_model(ctx, s);
    Z3_model_inc_ref(ctx, m);
    printf("model:\n%s\n", Z3_model_to_string(ctx, m));
    Z3_solver_assert(ctx, s, mk_binary_or(ctx, k4, k5));
    printf("it must be unsat...\n");
    result = Z3_solver_check(ctx, s);
    if (result != Z3_L_FALSE)
        error("BUG");
    Z3_model_dec_ref(ctx, m);
    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

/**
   \brief Return the number of soft-constraints that were disable by the given model.
   A soft-constraint was disabled if the associated auxiliary variable was assigned to true.
*/
unsigned get_num_disabled_soft_constraints(Z3_context ctx, Z3_model m, unsigned num_soft_cnstrs, Z3_ast * aux_vars) 
{
    unsigned i;
    unsigned num_disabled = 0;
    Z3_ast t = Z3_mk_true(ctx);
    for (i = 0; i < num_soft_cnstrs; i++) {
        Z3_ast val;
        if (Z3_model_eval(ctx, m, aux_vars[i], 1, &val) == true) {
            // printf("%s", Z3_ast_to_string(ctx, aux_vars[i]));
            // printf(" -> %s\n", Z3_ast_to_string(ctx, val));
            if (Z3_is_eq_ast(ctx, val, t)) {
                num_disabled++;
            }
        }
    }
    return num_disabled;
}

/**
   \brief Naive maxsat procedure based on linear search and at-most-k
   constraint.  Return the number of soft-constraints that can be
   satisfied.  Return -1 if the hard-constraints cannot be
   satisfied. That is, the formula cannot be satisfied even if all
   soft-constraints are ignored.

   Exercise: use binary search to implement MaxSAT.
   Hint: you will need to use an answer literal to retract the at-most-k constraint.
*/
int naive_maxsat(Z3_context ctx, Z3_solver s, unsigned num_hard_cnstrs, Z3_ast * hard_cnstrs, unsigned num_soft_cnstrs, Z3_ast * soft_cnstrs) 
{
    Z3_ast * aux_vars;
    Z3_lbool is_sat;
    unsigned k;
    assert_hard_constraints(ctx, s, num_hard_cnstrs, hard_cnstrs);
    printf("checking whether hard constraints are satisfiable...\n");
    is_sat = Z3_solver_check(ctx, s);
    if (is_sat == Z3_L_FALSE) {
        // It is not possible to make the formula satisfiable even when ignoring all soft constraints.
        return -1; 
    }
    if (num_soft_cnstrs == 0)
        return 0; // nothing to be done...
    aux_vars = assert_soft_constraints(ctx, s, num_soft_cnstrs, soft_cnstrs);
    // Perform linear search.
    k = num_soft_cnstrs - 1;
    for (;;) {
        Z3_model m;
        unsigned num_disabled;
        // at most k soft-constraints can be ignored.
        printf("checking whether at-most %d soft-constraints can be ignored.\n", k);
        assert_at_most_k(ctx, s, num_soft_cnstrs, aux_vars, k);
        is_sat = Z3_solver_check(ctx, s);
        if (is_sat == Z3_L_FALSE) {
            printf("unsat\n");
            return num_soft_cnstrs - k - 1;
        }
    m = Z3_solver_get_model(ctx, s);
        Z3_model_inc_ref(ctx, m);
        num_disabled = get_num_disabled_soft_constraints(ctx, m, num_soft_cnstrs, aux_vars);
        Z3_model_dec_ref(ctx, m);
        if (num_disabled > k) {
            error("BUG");
        }
        printf("sat\n");
        k = num_disabled;
        if (k == 0) {
            // it was possible to satisfy all soft-constraints.
            return num_soft_cnstrs; 
        }
        k--;
    }
}

/**
  \brief Implement one step of the Fu&Malik algorithm.
  See fu_malik_maxsat function for more details.
  
  Input:    soft constraints + aux-vars (aka answer literals) 
  Output:   done/not-done  when not done return updated set of soft-constraints and aux-vars. 
  - if SAT --> terminates
  - if UNSAT 
     * compute unsat core
     * add blocking variable to soft-constraints in the core
         - replace soft-constraint with the one with the blocking variable
         - we should also add an aux-var
         - replace aux-var with a new one
     * add at-most-one constraint with blocking 
*/
int fu_malik_maxsat_step(Z3_context ctx, Z3_solver s, unsigned num_soft_cnstrs, Z3_ast * soft_cnstrs, Z3_ast * aux_vars) 
{
    // create assumptions
    Z3_ast * assumptions = (Z3_ast*) malloc(sizeof(Z3_ast) * num_soft_cnstrs);
    Z3_lbool is_sat;
    Z3_ast_vector core;
    unsigned core_size;
    unsigned i = 0;
    unsigned k = 0;
    Z3_ast * block_vars;
    for (i = 0; i < num_soft_cnstrs; i++) {
        // Recall that we asserted (soft_cnstrs[i] \/ aux_vars[i])
        // So using (NOT aux_vars[i]) as an assumption we are actually forcing the soft_cnstrs[i] to be considered.
        assumptions[i] = Z3_mk_not(ctx, aux_vars[i]);
    }
    
    is_sat = Z3_solver_check_assumptions(ctx, s, num_soft_cnstrs, assumptions);
    if (is_sat != Z3_L_FALSE) {
        return 1; // done
    }
    else {
        core = Z3_solver_get_unsat_core(ctx, s);
        Z3_ast_vector_inc_ref(ctx, core);
	core_size = Z3_ast_vector_size(ctx, core);
        block_vars = (Z3_ast*) malloc(sizeof(Z3_ast) * core_size);
        k = 0;
        // update soft-constraints and aux_vars
        for (i = 0; i < num_soft_cnstrs; i++) {
            unsigned j;
            // check whether assumption[i] is in the core or not
            for (j = 0; j < core_size; j++) {
              if (assumptions[i] == Z3_ast_vector_get(ctx, core, j))
                    break;
            }
            if (j < core_size) {
                // assumption[i] is in the unsat core... so soft_cnstrs[i] is in the unsat core
                Z3_ast block_var   = mk_fresh_bool_var(ctx);
                Z3_ast new_aux_var = mk_fresh_bool_var(ctx);
                soft_cnstrs[i]     = mk_binary_or(ctx, soft_cnstrs[i], block_var);
                aux_vars[i]        = new_aux_var;
                block_vars[k]      = block_var;
                k++;
                // Add new constraint containing the block variable.
                // Note that we are using the new auxiliary variable to be able to use it as an assumption.
                Z3_solver_assert(ctx, s, mk_binary_or(ctx, soft_cnstrs[i], new_aux_var));
            }
        }
        assert_at_most_one(ctx, s, k, block_vars);
        Z3_ast_vector_dec_ref(ctx, core);
        return 0; // not done.
    }
}

/**
   \brief Fu & Malik procedure for MaxSAT. This procedure is based on 
   unsat core extraction and the at-most-one constraint.

   Return the number of soft-constraints that can be
   satisfied.  Return -1 if the hard-constraints cannot be
   satisfied. That is, the formula cannot be satisfied even if all
   soft-constraints are ignored.

   For more information on the Fu & Malik procedure:

   Z. Fu and S. Malik, On solving the partial MAX-SAT problem, in International
   Conference on Theory and Applications of Satisfiability Testing, 2006.
*/
int fu_malik_maxsat(Z3_context ctx, Z3_solver s, unsigned num_hard_cnstrs, Z3_ast * hard_cnstrs, unsigned num_soft_cnstrs, Z3_ast * soft_cnstrs) 
{
    Z3_ast * aux_vars;
    Z3_lbool is_sat;
    unsigned k;
    assert_hard_constraints(ctx, s, num_hard_cnstrs, hard_cnstrs);
    printf("checking whether hard constraints are satisfiable...\n");
    is_sat = Z3_solver_check(ctx, s);
    if (is_sat == Z3_L_FALSE) {
        // It is not possible to make the formula satisfiable even when ignoring all soft constraints.
        return -1; 
    }
    if (num_soft_cnstrs == 0)
        return 0; // nothing to be done...
    /*
      Fu&Malik algorithm is based on UNSAT-core extraction.
      We accomplish that using auxiliary variables (aka answer literals).
    */
    aux_vars = assert_soft_constraints(ctx, s, num_soft_cnstrs, soft_cnstrs);
    k = 0;
    for (;;) {
        printf("iteration %d\n", k);
        if (fu_malik_maxsat_step(ctx, s, num_soft_cnstrs, soft_cnstrs, aux_vars)) {
            return num_soft_cnstrs - k;
        }
        k++;
    }
}

#define NAIVE_MAXSAT 0
#define FU_MALIK_MAXSAT 1

/**
  \brief Finds the maximal number of assumptions that can be satisfied.
  An assumption is any formula preceded with the :assumption keyword.
  "Hard" constraints can be supported by using the :formula keyword.
  
  Input: file in SMT-LIB format, and MaxSAT algorithm to be used: 0 - Naive, 1 - Fu&Malik's algo.
  Output: the maximum number of assumptions that can be satisfied.
*/
int smtlib_maxsat(char * file_name, int approach) 
{
    Z3_context ctx;
    Z3_solver s;
    unsigned i;
    Z3_optimize opt;
    unsigned num_hard_cnstrs, num_soft_cnstrs;
    Z3_ast * hard_cnstrs, * soft_cnstrs;
    Z3_ast_vector  hard, objs;
    Z3_app soft;
    unsigned result = 0;
    ctx = mk_context();
    s = mk_solver(ctx);
    opt = Z3_mk_optimize(ctx);
    Z3_optimize_inc_ref(ctx, opt);
    Z3_optimize_from_file(ctx, opt, file_name);
    hard = Z3_optimize_get_assertions(ctx, opt);
    Z3_ast_vector_inc_ref(ctx, hard);
    num_hard_cnstrs = Z3_ast_vector_size(ctx, hard);
    hard_cnstrs = (Z3_ast *) malloc(sizeof(Z3_ast) * (num_hard_cnstrs));
    for (i = 0; i < num_hard_cnstrs; i++) {
        hard_cnstrs[i] = Z3_ast_vector_get(ctx, hard, i);
    }
    objs = Z3_optimize_get_objectives(ctx, opt);
    Z3_ast_vector_inc_ref(ctx, objs);

    // soft constraints are stored in a single objective which is a sum 
    // of if-then-else expressions.
    soft = Z3_to_app(ctx, Z3_ast_vector_get(ctx, objs, 0));
    num_soft_cnstrs = Z3_get_app_num_args(ctx, soft);
    soft_cnstrs = (Z3_ast *) malloc(sizeof(Z3_ast) * (num_soft_cnstrs));
    for (i = 0; i < num_soft_cnstrs; ++i) {
        soft_cnstrs[i] = Z3_get_app_arg(ctx, Z3_to_app(ctx, Z3_get_app_arg(ctx, soft, i)), 0);
    }
    
    switch (approach) {
    case NAIVE_MAXSAT: 
        result = naive_maxsat(ctx, s, num_hard_cnstrs, hard_cnstrs, num_soft_cnstrs, soft_cnstrs);
        break;
    case FU_MALIK_MAXSAT:
        result = fu_malik_maxsat(ctx, s, num_hard_cnstrs, hard_cnstrs, num_soft_cnstrs, soft_cnstrs);
        break;
    default:
        /* Exercise: implement your own MaxSAT algorithm.*/
        error("Not implemented yet.");
        break;
    }
    free_cnstr_array(hard_cnstrs);
    free_cnstr_array(soft_cnstrs);
    Z3_solver_dec_ref(ctx, s);
    Z3_optimize_dec_ref(ctx, opt);
    return result;
}

int main(int argc, char * argv[]) {
#if 1
    int r;
    if (argc != 2) {
        error("usage: maxsat [filename.smt].");
    }
    r = smtlib_maxsat(argv[1], FU_MALIK_MAXSAT);
    printf("result: %d\n", r);
#else
    tst_at_most_one();
#endif
    return 0;
}

/*@}*/

