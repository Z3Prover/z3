import { createApi, Z3HighLevel } from './high-level';
import { init as initWrapper, Z3LowLevel } from './low-level';
export * from './high-level/types';
export { Z3Core, Z3LowLevel } from './low-level';
export * from './low-level/types.__GENERATED__';

export async function init(): Promise<Z3LowLevel & Z3HighLevel> {
  const initZ3 = (global as any).initZ3;
  if (initZ3 === undefined) {
    throw new Error('initZ3 was not imported correctly. Please consult documentation on how to load Z3 in browser');
  }

  const lowLevel = await initWrapper(initZ3);
  const highLevel = createApi(lowLevel.Z3);
  return { ...lowLevel, ...highLevel };
}
