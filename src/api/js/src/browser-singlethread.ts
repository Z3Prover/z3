import { createApi, Z3HighLevel } from './high-level';
import { init as initWrapper, Z3LowLevel, Z3ModuleOverrides } from './low-level';
export * from './high-level/types';
export { Z3Core, Z3LowLevel } from './low-level';
export * from './low-level/types.__GENERATED__';

// Name of the global exposed by z3-built-singlethread.js when loaded as a script.
const INIT_GLOBAL = 'initZ3SingleThread';

/**
 * Browser entry point for the single-threaded Z3 build.
 *
 * This variant does NOT require SharedArrayBuffer or the COOP/COEP HTTP headers
 * that the default (threaded) build needs.  All Z3 operations run synchronously
 * in the calling thread, so this build should be used inside a Web Worker to
 * avoid blocking the main browser thread.
 *
 * Before calling `init()`, make sure the `z3-built-singlethread.js` script has
 * been loaded (e.g. via `importScripts('z3-built-singlethread.js')` inside the
 * worker), so that `initZ3SingleThread` is available on the global object.
 * @category Global */
export async function init(moduleOverrides: Z3ModuleOverrides = {}): Promise<Z3LowLevel & Z3HighLevel> {
  const initZ3 = (global as any)[INIT_GLOBAL];
  if (initZ3 === undefined) {
    throw new Error(
      `${INIT_GLOBAL} was not found. ` +
        'Load z3-built-singlethread.js before calling init() ' +
        '(e.g. importScripts("z3-built-singlethread.js") in a Web Worker).',
    );
  }

  const lowLevel = await initWrapper(initZ3, moduleOverrides);
  const highLevel = createApi(lowLevel.Z3, lowLevel.em);
  return { ...lowLevel, ...highLevel };
}
