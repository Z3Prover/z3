// @ts-ignore we're not going to bother with types for this
import process from 'process';
import { init, Z3_error_code } from '../../build/node.js';

// demonstrates use of the raw API

(async () => {
  let { em, Z3 } = await init();

  Z3.global_param_set('verbose', '10');
  console.log('verbosity:', Z3.global_param_get('verbose'));

  let config = Z3.mk_config();
  let ctx = Z3.mk_context_rc(config);
  Z3.del_config(config);

  let unicodeStr = [...'hello™'].map(x => x.codePointAt(0)!);
  let strAst = Z3.mk_u32string(ctx, unicodeStr);
  Z3.inc_ref(ctx, strAst);

  console.log(Z3.is_string(ctx, strAst));
  console.log(Z3.get_string(ctx, strAst));
  console.log(Z3.get_string_contents(ctx, strAst, unicodeStr.length));

  let bv = Z3.mk_bv_numeral(ctx, [true, true, false]);
  let bs = Z3.mk_ubv_to_str(ctx, bv);
  console.log(Z3.ast_to_string(ctx, bs));

  let intSort = Z3.mk_int_sort(ctx);
  let big = Z3.mk_int64(ctx, 42n, intSort);
  console.log(Z3.get_numeral_string(ctx, big));
  console.log(Z3.get_numeral_int64(ctx, big));

  console.log(Z3.get_version());

  let head_tail = [Z3.mk_string_symbol(ctx, 'car'), Z3.mk_string_symbol(ctx, 'cdr')];

  let nil_con = Z3.mk_constructor(ctx, Z3.mk_string_symbol(ctx, 'nil'), Z3.mk_string_symbol(ctx, 'is_nil'), [], [], []);
  let cons_con = Z3.mk_constructor(
    ctx,
    Z3.mk_string_symbol(ctx, 'cons'),
    Z3.mk_string_symbol(ctx, 'is_cons'),
    head_tail,
    [null, null],
    [0, 0],
  );

  let cell = Z3.mk_datatype(ctx, Z3.mk_string_symbol(ctx, 'cell'), [nil_con, cons_con]);
  console.log(Z3.query_constructor(ctx, nil_con, 0));
  console.log(Z3.query_constructor(ctx, cons_con, 2));

  if (Z3.get_error_code(ctx) !== Z3_error_code.Z3_OK) {
    throw new Error('something failed: ' + Z3.get_error_msg(ctx, Z3.get_error_code(ctx)));
  }
  await Z3.eval_smtlib2_string(ctx, '(simplify)');
  if (Z3.get_error_code(ctx) === Z3_error_code.Z3_OK) {
    throw new Error('expected call to eval_smtlib2_string with invalid argument to fail');
  }
  console.log('confirming error messages work:', Z3.get_error_msg(ctx, Z3.get_error_code(ctx)));

  Z3.global_param_set('verbose', '0');
  let result = await Z3.eval_smtlib2_string(
    ctx,
    `
    (declare-const p Bool)
    (declare-const q Bool)
    (declare-const r Bool)
    (declare-const s Bool)
    (declare-const t Bool)
    (assert ((_ pbeq 5 2 1 3 3 2) p q r s t))
    (check-sat)
    (get-model)
  `,
  );
  console.log('checking string evaluation', result);

  Z3.dec_ref(ctx, strAst);
  Z3.del_context(ctx);
})().catch(e => {
  console.error('error', e);
  process.exit(1);
});
