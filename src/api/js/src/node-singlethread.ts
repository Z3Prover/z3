// @ts-ignore no-implicit-any
import initModule = require('./z3-built-singlethread');

import { createApi, Z3HighLevel } from './high-level';
import { init as initWrapper, Z3LowLevel, Z3ModuleOverrides } from './low-level';
export * from './high-level/types';
export { Z3Core, Z3LowLevel } from './low-level';
export * from './low-level/types.__GENERATED__';

/**
 * The main entry point to the single-threaded Z3 API.
 *
 * This variant does NOT require SharedArrayBuffer or the COOP/COEP HTTP headers
 * that the default (threaded) build needs.  All Z3 operations run synchronously
 * in the calling thread, so this build should be used inside a Web Worker to
 * avoid blocking the main browser thread.
 *
 * ```typescript
 * import { init } from 'z3-solver/singlethread';
 *
 * const { Context } = await init();
 * const { Solver, Int } = new Context('main');
 *
 * const x = Int.const('x');
 * const solver = new Solver();
 * solver.add(x.ge(0));
 * console.log(await solver.check()); // 'sat'
 * ```
 * @category Global */
export async function init(moduleOverrides: Z3ModuleOverrides = {}): Promise<Z3HighLevel & Z3LowLevel> {
  const lowLevel = await initWrapper(initModule, moduleOverrides);
  const highLevel = createApi(lowLevel.Z3, lowLevel.em);
  return { ...lowLevel, ...highLevel };
}
