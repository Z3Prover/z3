// This file is not included in the build

// @ts-ignore no-implicit-any
import { createApi, Z3HighLevel } from './high-level';
import { init as initWrapper, Z3LowLevel } from './low-level';
import initModule = require('../build/z3-built');

export * from './high-level/types';
export { Z3Core, Z3LowLevel } from './low-level';
export * from './low-level/types.__GENERATED__';
export { killThreads } from './kill-threads';

export async function init(): Promise<Z3HighLevel & Z3LowLevel> {
  const lowLevel = await initWrapper(initModule);
  const highLevel = createApi(lowLevel.Z3, lowLevel.em);
  return { ...lowLevel, ...highLevel };
}

