// @ts-ignore no-implicit-any
import initModule = require('./z3-built');

import { createApi, Z3HighLevel } from './high-level';
import { init as initWrapper, Z3LowLevel } from './low-level';
export * from './high-level/types';
export { Z3Core, Z3LowLevel } from './low-level';
export * from './low-level/types.__GENERATED__';

/**
 * The main entry point to the Z3 API
 *
 * ```typescript
 * import { init, sat } from 'z3-solver';
 *
 * const { Context } = await init();
 * const { Solver, Int } = new Context('main');
 *
 * const x = Int.const('x');
 * const y = Int.const('y');
 *
 * const solver = new Solver();
 * solver.add(x.add(2).le(y.sub(10))); // x + 2 <= y - 10
 *
 * if (await solver.check() !== sat) {
 *   throw new Error("couldn't find a solution")
 * }
 * const model = solver.model();
 *
 * console.log(`x=${model.get(x)}, y=${model.get(y)}`);
 * // x=0, y=12
 * ```
 * @category Global */
export async function init(): Promise<Z3HighLevel & Z3LowLevel> {
  const lowLevel = await initWrapper(initModule);
  const highLevel = createApi(lowLevel.Z3);
  return { ...lowLevel, ...highLevel };
}
