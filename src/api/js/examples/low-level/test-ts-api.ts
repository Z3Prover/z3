// Some of the examples from test_capi.c.
// Note that none of the type annotations on variable declarations are necessary:
// TypeScript can infer all of them.
// They're just here so readers can see what types things are.

// @ts-ignore we're not going to bother with types for this
import process from 'process';
import { sprintf } from 'sprintf-js';
import type {
  Z3_app,
  Z3_ast,
  Z3_ast_vector,
  Z3_config,
  Z3_context,
  Z3_func_decl,
  Z3_func_entry,
  Z3_func_interp,
  Z3_model,
  Z3_solver,
  Z3_sort,
  Z3_symbol,
} from '../../build/node';
import { init, Z3_ast_kind, Z3_lbool, Z3_sort_kind, Z3_symbol_kind } from '../../build/node.js';

let printf = (str: string, ...args: unknown[]) => console.log(sprintf(str.replace(/\n$/, ''), ...args));

(async () => {
  let { em, Z3 } = await init();

  function mk_context(): Z3_context {
    let cfg: Z3_config = Z3.mk_config();
    Z3.set_param_value(cfg, 'model', 'true');
    let ctx: Z3_context = Z3.mk_context(cfg);
    Z3.del_config(cfg);
    return ctx;
  }

  function mk_proof_context(): Z3_context {
    let cfg: Z3_config = Z3.mk_config();
    let ctx: Z3_context;
    Z3.set_param_value(cfg, 'proof', 'true');
    ctx = Z3.mk_context(cfg);
    Z3.del_config(cfg);
    return ctx;
  }

  function mk_solver(ctx: Z3_context): Z3_solver {
    let s: Z3_solver = Z3.mk_solver(ctx);
    Z3.solver_inc_ref(ctx, s);
    return s;
  }

  function del_solver(ctx: Z3_context, s: Z3_solver) {
    Z3.solver_dec_ref(ctx, s);
  }

  function mk_var(ctx: Z3_context, name: string, ty: Z3_sort): Z3_ast {
    let s: Z3_symbol = Z3.mk_string_symbol(ctx, name);
    return Z3.mk_const(ctx, s, ty);
  }

  function mk_bool_var(ctx: Z3_context, name: string): Z3_ast {
    let ty: Z3_sort = Z3.mk_bool_sort(ctx);
    return mk_var(ctx, name, ty);
  }

  function exitf(m: string) {
    console.error(`BUG: ${m}`);
    process.exit(1);
  }

  function display_symbol(c: Z3_context, s: Z3_symbol) {
    switch (Z3.get_symbol_kind(c, s)) {
      case Z3_symbol_kind.Z3_INT_SYMBOL:
        process.stdout.write(sprintf('#%d', Z3.get_symbol_int(c, s)));
        break;
      case Z3_symbol_kind.Z3_STRING_SYMBOL:
        process.stdout.write(sprintf('%s', Z3.get_symbol_string(c, s)));
        break;
      default:
        throw new Error('unreachable');
    }
  }

  function display_sort(c: Z3_context, ty: Z3_sort) {
    switch (Z3.get_sort_kind(c, ty)) {
      case Z3_sort_kind.Z3_UNINTERPRETED_SORT:
        display_symbol(c, Z3.get_sort_name(c, ty));
        break;
      case Z3_sort_kind.Z3_BOOL_SORT:
        process.stdout.write('bool');
        break;
      case Z3_sort_kind.Z3_INT_SORT:
        process.stdout.write('int');
        break;
      case Z3_sort_kind.Z3_REAL_SORT:
        process.stdout.write('real');
        break;
      case Z3_sort_kind.Z3_BV_SORT:
        process.stdout.write(sprintf('bv%d', Z3.get_bv_sort_size(c, ty)));
        break;
      case Z3_sort_kind.Z3_ARRAY_SORT:
        process.stdout.write('[');
        display_sort(c, Z3.get_array_sort_domain(c, ty));
        process.stdout.write('->');
        display_sort(c, Z3.get_array_sort_range(c, ty));
        process.stdout.write(']');
        break;
      case Z3_sort_kind.Z3_DATATYPE_SORT:
        if (Z3.get_datatype_sort_num_constructors(c, ty) !== 1) {
          process.stdout.write(sprintf('%s', Z3.sort_to_string(c, ty)));
          break;
        }
        {
          let num_fields: number = Z3.get_tuple_sort_num_fields(c, ty);
          let i: number;
          process.stdout.write('(');
          for (i = 0; i < num_fields; i++) {
            let field: Z3_func_decl = Z3.get_tuple_sort_field_decl(c, ty, i);
            if (i > 0) {
              process.stdout.write(', ');
            }
            display_sort(c, Z3.get_range(c, field));
          }
          process.stdout.write(')');
          break;
        }
      default:
        process.stdout.write('unknown[');
        display_symbol(c, Z3.get_sort_name(c, ty));
        process.stdout.write(']');
        break;
    }
  }

  function display_ast(c: Z3_context, v: Z3_ast) {
    switch (Z3.get_ast_kind(c, v)) {
      case Z3_ast_kind.Z3_NUMERAL_AST: {
        let t: Z3_sort;
        process.stdout.write(sprintf('%s', Z3.get_numeral_string(c, v)));
        t = Z3.get_sort(c, v);
        process.stdout.write(':');
        display_sort(c, t);
        break;
      }
      case Z3_ast_kind.Z3_APP_AST: {
        let i: number;
        let app: Z3_app = Z3.to_app(c, v);
        let num_fields: number = Z3.get_app_num_args(c, app);
        let d: Z3_func_decl = Z3.get_app_decl(c, app);
        process.stdout.write(sprintf('%s', Z3.func_decl_to_string(c, d)));
        if (num_fields > 0) {
          process.stdout.write('[');
          for (i = 0; i < num_fields; i++) {
            if (i > 0) {
              process.stdout.write(', ');
            }
            display_ast(c, Z3.get_app_arg(c, app, i));
          }
          process.stdout.write(']');
        }
        break;
      }
      case Z3_ast_kind.Z3_QUANTIFIER_AST: {
        process.stdout.write('quantifier');
      }
      default:
        process.stdout.write('#unknown');
    }
  }

  function display_function_interpretations(c: Z3_context, m: Z3_model) {
    let num_functions: number;
    let i: number;

    process.stdout.write('function interpretations:\n');

    num_functions = Z3.model_get_num_funcs(c, m);
    for (i = 0; i < num_functions; i++) {
      let fdecl: Z3_func_decl;
      let name: Z3_symbol;
      let func_else: Z3_ast;
      let num_entries = 0;
      let j: number;
      let finterp: Z3_func_interp | null;

      fdecl = Z3.model_get_func_decl(c, m, i);
      finterp = Z3.model_get_func_interp(c, m, fdecl);
      if (finterp) Z3.func_interp_inc_ref(c, finterp);
      name = Z3.get_decl_name(c, fdecl);
      display_symbol(c, name);
      process.stdout.write(' = {');
      if (finterp) num_entries = Z3.func_interp_get_num_entries(c, finterp);
      for (j = 0; j < num_entries; j++) {
        let num_args: number;
        let k: number;
        let fentry: Z3_func_entry = Z3.func_interp_get_entry(c, finterp!, j);
        Z3.func_entry_inc_ref(c, fentry);
        if (j > 0) {
          process.stdout.write(', ');
        }
        num_args = Z3.func_entry_get_num_args(c, fentry);
        process.stdout.write('(');
        for (k = 0; k < num_args; k++) {
          if (k > 0) {
            process.stdout.write(', ');
          }
          display_ast(c, Z3.func_entry_get_arg(c, fentry, k));
        }
        process.stdout.write('|->');
        display_ast(c, Z3.func_entry_get_value(c, fentry));
        process.stdout.write(')');
        Z3.func_entry_dec_ref(c, fentry);
      }
      if (num_entries > 0) {
        process.stdout.write(', ');
      }
      if (finterp) {
        process.stdout.write('(else|->');
        func_else = Z3.func_interp_get_else(c, finterp);
        display_ast(c, func_else);
        Z3.func_interp_dec_ref(c, finterp);
      }
      process.stdout.write(')}\n');
    }
  }
  function display_model(c: Z3_context, m: Z3_model | null) {
    let num_constants: number;
    let i: number;

    if (!m) return;

    num_constants = Z3.model_get_num_consts(c, m);
    for (i = 0; i < num_constants; i++) {
      let name: Z3_symbol;
      let cnst: Z3_func_decl = Z3.model_get_const_decl(c, m, i);
      let a: Z3_ast;
      let v: Z3_ast;
      let ok: boolean;
      name = Z3.get_decl_name(c, cnst);
      display_symbol(c, name);
      process.stdout.write(' = ');
      a = Z3.mk_app(c, cnst, []);
      v = a;
      let result = Z3.model_eval(c, m, a, true);
      ok = result != null;
      if (result != null) {
        v = result;
      }
      display_ast(c, v);
      process.stdout.write('\n');
    }
    display_function_interpretations(c, m);
  }

  async function check(ctx: Z3_context, s: Z3_solver, expected_result: Z3_lbool) {
    let m: Z3_model | null = null;
    let result: Z3_lbool = await Z3.solver_check(ctx, s);
    switch (result) {
      case Z3_lbool.Z3_L_FALSE:
        printf('unsat\n');
        break;
      case Z3_lbool.Z3_L_UNDEF:
        printf('unknown\n');
        m = Z3.solver_get_model(ctx, s);
        if (m) Z3.model_inc_ref(ctx, m);
        printf('potential model:\n%s\n', Z3.model_to_string(ctx, m));
        break;
      case Z3_lbool.Z3_L_TRUE:
        m = Z3.solver_get_model(ctx, s);
        if (m) Z3.model_inc_ref(ctx, m);
        printf('sat\n%s\n', Z3.model_to_string(ctx, m));
        break;
    }
    if (result !== expected_result) {
      exitf('unexpected result');
    }
    if (m) Z3.model_dec_ref(ctx, m);
  }

  // https://github.com/Z3Prover/z3/blob/174889ad5ea8b1e1127aeec8a4121a5687ac9a2b/examples/c/test_capi.c#L1440
  async function bitvector_example2() {
    let ctx: Z3_context = mk_context();
    let s: Z3_solver = mk_solver(ctx);

    /* construct x ^ y - 103 == x * y */
    let bv_sort: Z3_sort = Z3.mk_bv_sort(ctx, 32);
    let x: Z3_ast = mk_var(ctx, 'x', bv_sort);
    let y: Z3_ast = mk_var(ctx, 'y', bv_sort);
    let x_xor_y: Z3_ast = Z3.mk_bvxor(ctx, x, y);
    let c103: Z3_ast = Z3.mk_numeral(ctx, '103', bv_sort);
    let lhs: Z3_ast = Z3.mk_bvsub(ctx, x_xor_y, c103);
    let rhs: Z3_ast = Z3.mk_bvmul(ctx, x, y);
    let ctr: Z3_ast = Z3.mk_eq(ctx, lhs, rhs);

    printf('\nbitvector_example2\n');
    // LOG_MSG("bitvector_example2");
    printf('find values of x and y, such that x ^ y - 103 == x * y\n');

    // /* add the constraint <tt>x ^ y - 103 == x * y<\tt> to the logical context */
    Z3.solver_assert(ctx, s, ctr);

    // /* find a model (i.e., values for x an y that satisfy the constraint */
    await check(ctx, s, Z3_lbool.Z3_L_TRUE);

    del_solver(ctx, s);
    Z3.del_context(ctx);
  }

  // https://github.com/Z3Prover/z3/blob/174889ad5ea8b1e1127aeec8a4121a5687ac9a2b/examples/c/test_capi.c#L2230
  async function unsat_core_and_proof_example() {
    let ctx: Z3_context = mk_proof_context();
    let s: Z3_solver = mk_solver(ctx);
    let pa: Z3_ast = mk_bool_var(ctx, 'PredA');
    let pb: Z3_ast = mk_bool_var(ctx, 'PredB');
    let pc: Z3_ast = mk_bool_var(ctx, 'PredC');
    let pd: Z3_ast = mk_bool_var(ctx, 'PredD');
    let p1: Z3_ast = mk_bool_var(ctx, 'P1');
    let p2: Z3_ast = mk_bool_var(ctx, 'P2');
    let p3: Z3_ast = mk_bool_var(ctx, 'P3');
    let p4: Z3_ast = mk_bool_var(ctx, 'P4');
    let assumptions: Z3_ast[] = [Z3.mk_not(ctx, p1), Z3.mk_not(ctx, p2), Z3.mk_not(ctx, p3), Z3.mk_not(ctx, p4)];
    let args1: Z3_ast[] = [pa, pb, pc];
    let f1 = Z3.mk_and(ctx, args1);
    let args2: Z3_ast[] = [pa, Z3.mk_not(ctx, pb), pc];
    let f2 = Z3.mk_and(ctx, args2);
    let args3: Z3_ast[] = [Z3.mk_not(ctx, pa), Z3.mk_not(ctx, pc)];
    let f3 = Z3.mk_or(ctx, args3);
    let f4 = pd;
    let g1: Z3_ast[] = [f1, p1];
    let g2: Z3_ast[] = [f2, p2];
    let g3: Z3_ast[] = [f3, p3];
    let g4: Z3_ast[] = [f4, p4];
    let result: Z3_lbool;
    let proof: Z3_ast;
    let m: Z3_model | null = null;
    let i: number;
    let core: Z3_ast_vector;

    printf('\nunsat_core_and_proof_example\n');
    // LOG_MSG("unsat_core_and_proof_example");

    Z3.solver_assert(ctx, s, Z3.mk_or(ctx, g1));
    Z3.solver_assert(ctx, s, Z3.mk_or(ctx, g2));
    Z3.solver_assert(ctx, s, Z3.mk_or(ctx, g3));
    Z3.solver_assert(ctx, s, Z3.mk_or(ctx, g4));

    result = await Z3.solver_check_assumptions(ctx, s, assumptions);

    switch (result) {
      case Z3_lbool.Z3_L_FALSE:
        core = Z3.solver_get_unsat_core(ctx, s);
        proof = Z3.solver_get_proof(ctx, s);
        printf('unsat\n');
        printf('proof: %s\n', Z3.ast_to_string(ctx, proof));

        printf('\ncore:\n');
        for (i = 0; i < Z3.ast_vector_size(ctx, core); ++i) {
          printf('%s\n', Z3.ast_to_string(ctx, Z3.ast_vector_get(ctx, core, i)));
        }
        printf('\n');
        break;
      case Z3_lbool.Z3_L_UNDEF:
        printf('unknown\n');
        printf('potential model:\n');
        m = Z3.solver_get_model(ctx, s);
        if (m) Z3.model_inc_ref(ctx, m);
        display_model(ctx, m);
        throw new Error('result was undef, should have been unsat');
      case Z3_lbool.Z3_L_TRUE:
        printf('sat\n');
        m = Z3.solver_get_model(ctx, s);
        if (m) Z3.model_inc_ref(ctx, m);
        display_model(ctx, m);
        throw new Error('result was sat, should have been unsat');
    }

    /* delete logical context */
    if (m) Z3.model_dec_ref(ctx, m);
    del_solver(ctx, s);
    Z3.del_context(ctx);
  }

  await bitvector_example2();
  await unsat_core_and_proof_example();
})().catch(e => {
  console.error('error', e);
  process.exit(1);
});
