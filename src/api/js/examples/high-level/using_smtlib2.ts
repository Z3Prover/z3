// @ts-ignore we're not going to bother with types for this
import process from 'process';
import { init } from '../../build/node';
import assert from 'assert';

(async () => {
  let { Context, em } = await init();
  let z3 = Context('main');

  const x = z3.BitVec.const('x', 256);
  const y = z3.BitVec.const('y', 256);
  const z = z3.BitVec.const('z', 256);
  const xPlusY = x.add(y);
  const xPlusZ = x.add(z);
  const expr = xPlusY.mul(xPlusZ);

  const to_check = expr.eq(z3.Const('test', expr.sort));

  const solver = new z3.Solver();
  solver.add(to_check);
  const cr = await solver.check();
  console.log(cr);
  assert(cr === 'sat');

  const model = solver.model();
  let modelStr = model.sexpr();
  modelStr = modelStr.replace(/\n/g, ' ');
  console.log('Model: ', modelStr);

  const exprs = z3.ast_from_string(modelStr);
  console.log(exprs);
})().catch(e => {
  console.error('error', e);
  process.exit(1);
});
