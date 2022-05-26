// @ts-ignore no-implicit-any
import initModule = require('./z3-built.js');

import { createApi, Z3HighLevel } from './high-level';
import { init as initWrapper, Z3LowLevel } from './low-level';
export * from './high-level';
export { Z3Core, Z3LowLevel } from './low-level';
export * from './low-level/types.__GENERATED__';

export async function init(): Promise<Z3HighLevel & Z3LowLevel> {
  const lowLevel = await initWrapper(initModule);
  const highLevel = createApi(lowLevel.Z3);
  return { ...lowLevel, ...highLevel };
}
