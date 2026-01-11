/**
 * Example demonstrating the new Simplifier, Params, and ParamDescrs APIs
 *
 * This example shows how to:
 * 1. Create and configure parameter objects
 * 2. Use simplifiers for preprocessing
 * 3. Compose simplifiers
 * 4. Introspect parameter descriptions
 */

import { init } from '../../build/node';

(async () => {
  const { Context } = await init();
  const { Int, Solver, Simplifier, Params } = Context('main');

  // Example 1: Using Params to configure tactics
  console.log('Example 1: Creating and using Params');
  const params = new Params();
  params.set('elim_and', true);
  params.set('max_steps', 1000);
  params.set('timeout', 5.0);
  console.log('Params:', params.toString());

  // Example 2: Creating and using a Simplifier
  console.log('\nExample 2: Using a Simplifier');
  const simplifier = new Simplifier('solve-eqs');
  console.log('Simplifier help:', simplifier.help());

  // Example 3: Composing simplifiers
  console.log('\nExample 3: Composing simplifiers');
  const s1 = new Simplifier('solve-eqs');
  const s2 = new Simplifier('simplify');
  const composed = s1.andThen(s2);
  console.log('Composed simplifier created');

  // Example 4: Using simplifier with parameters
  console.log('\nExample 4: Configuring simplifier with parameters');
  const configParams = new Params();
  configParams.set('ite_solver', false);
  const configuredSimplifier = simplifier.usingParams(configParams);
  console.log('Configured simplifier created');

  // Example 4b: Configuring tactic with parameters
  console.log('\nExample 4b: Configuring tactic with parameters');
  const { Tactic } = Context('main');
  const tactic = new Tactic('simplify');
  const tacticParams = new Params();
  tacticParams.set('max_steps', 1000);
  const configuredTactic = tactic.usingParams(tacticParams);
  console.log('Configured tactic created');

  // Example 5: Adding simplifier to solver
  console.log('\nExample 5: Using simplifier with solver');
  const solver = new Solver();
  solver.addSimplifier(s1);

  const x = Int.const('x');
  const y = Int.const('y');
  solver.add(x.eq(y.add(1)));
  solver.add(y.eq(5));

  const result = await solver.check();
  console.log('Result:', result);

  if (result === 'sat') {
    const model = solver.model();
    console.log('x =', model.eval(x).toString());
    console.log('y =', model.eval(y).toString());
  }

  // Example 6: Introspecting parameter descriptions
  console.log('\nExample 6: Parameter introspection');
  const paramDescrs = simplifier.paramDescrs();
  console.log('Parameter descriptions:');
  console.log(paramDescrs.toString());

  const size = paramDescrs.size();
  console.log(`Number of parameters: ${size}`);

  if (size > 0) {
    const firstParamName = paramDescrs.getName(0);
    console.log(`First parameter: ${firstParamName}`);
    console.log(`Documentation: ${paramDescrs.getDocumentation(firstParamName)}`);
  }

  console.log('\nAll examples completed successfully!');
})();
