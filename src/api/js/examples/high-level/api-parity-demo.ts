/**
 * Demo of new TypeScript API parity features
 * 
 * This example demonstrates the solver introspection APIs, congruence closure APIs,
 * and model sort universe APIs added for API parity with other Z3 bindings.
 */

import { init } from '../../build/node';

(async () => {
  const { Solver, Bool, Int, Sort, Const } = await init();

  console.log('=== Solver Introspection APIs Demo ===\n');

  // Demo 1: Units API
  console.log('1. Units API - Retrieve unit literals');
  const solver1 = new Solver();
  const x = Bool.const('x');
  solver1.add(x); // x is a unit literal
  await solver1.check();
  const units = solver1.units();
  console.log(`   Found ${units.length()} unit literal(s)`);
  console.log('');

  // Demo 2: Non-Units API
  console.log('2. Non-Units API - Retrieve non-unit literals');
  const solver2 = new Solver();
  const y = Bool.const('y');
  const z = Bool.const('z');
  solver2.add(y.or(z));
  await solver2.check();
  const nonUnits = solver2.nonUnits();
  console.log(`   Found ${nonUnits.length()} non-unit literal(s)`);
  console.log('');

  // Demo 3: Trail API
  console.log('3. Trail API - Retrieve solver decision trail');
  const solver3 = new Solver();
  const a = Bool.const('a');
  const b = Bool.const('b');
  solver3.add(a.implies(b));
  solver3.add(a);
  await solver3.check();
  const trail = solver3.trail();
  console.log(`   Trail contains ${trail.length()} decision(s)`);
  console.log('');

  console.log('=== Congruence Closure APIs Demo ===\n');

  // Demo 4: Congruence Root API
  console.log('4. Congruence Root API - Find root of congruence class');
  const solver4 = new Solver();
  const ix = Int.const('ix');
  const iy = Int.const('iy');
  solver4.add(ix.eq(iy));
  await solver4.check();
  const root = solver4.congruenceRoot(ix);
  console.log(`   Congruence root of ix: ${root.toString()}`);
  console.log('');

  // Demo 5: Congruence Next API
  console.log('5. Congruence Next API - Get next element in congruence class');
  const solver5 = new Solver();
  const m = Int.const('m');
  const n = Int.const('n');
  const o = Int.const('o');
  solver5.add(m.eq(n));
  solver5.add(n.eq(o));
  await solver5.check();
  const next = solver5.congruenceNext(m);
  console.log(`   Next element after m: ${next.toString()}`);
  console.log('');

  // Demo 6: Congruence Explain API
  console.log('6. Congruence Explain API - Explain why terms are congruent');
  const solver6 = new Solver();
  const p = Int.const('p');
  const q = Int.const('q');
  solver6.add(p.eq(q));
  await solver6.check();
  const explanation = solver6.congruenceExplain(p, q);
  console.log(`   Explanation: ${explanation.toString()}`);
  console.log('');

  console.log('=== Model Sort Universe APIs Demo ===\n');

  // Demo 7: Sort Universe APIs
  console.log('7. Sort Universe APIs - Enumerate finite uninterpreted sorts');
  const solver7 = new Solver();
  const A = Sort.declare('A');
  const c1 = Const('c1', A);
  const c2 = Const('c2', A);
  solver7.add(c1.neq(c2));
  await solver7.check();

  const model = solver7.model();
  console.log(`   Number of sorts in model: ${model.numSorts()}`);

  const sorts = model.getSorts();
  for (let i = 0; i < sorts.length; i++) {
    const sort = sorts[i];
    console.log(`   Sort ${i}: ${sort.toString()}`);
    const universe = model.sortUniverse(sort);
    console.log(`      Universe size: ${universe.length()}`);
    for (let j = 0; j < universe.length(); j++) {
      console.log(`      Element ${j}: ${universe.get(j).toString()}`);
    }
  }
  console.log('');

  console.log('=== File Loading API Demo ===\n');

  // Demo 8: From File API
  console.log('8. From File API - Load SMT-LIB2 from file');
  const solver8 = new Solver();
  console.log('   solver.fromFile(filename) method is available');
  console.log('   (Actual file loading not demonstrated in this example)');
  console.log('');

  console.log('All API parity demos completed successfully!');
})();
