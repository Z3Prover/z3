// This file is not included in the build

// @ts-ignore no-implicit-any
import { createApi, Z3HighLevel } from './high-level';
import { init as initWrapper, Z3LowLevel } from './low-level';
import initModule = require('../build/z3-built.js');

export * from './high-level';
export { Z3Core, Z3LowLevel } from './low-level';
export * from './low-level/types.__GENERATED__';

export async function init(): Promise<Z3HighLevel & Z3LowLevel> {
  const lowLevel = await initWrapper(initModule);
  const highLevel = createApi(lowLevel.Z3);
  return { ...lowLevel, ...highLevel };
}

export function delay(ms: number): Promise<void> & { cancel(): void };
export function delay(ms: number, result: Error): Promise<never> & { cancel(): void };
export function delay<T>(ms: number, result: T): Promise<T> & { cancel(): void };
export function delay<T>(ms: number, result?: T | Error): Promise<T | void> & { cancel(): void } {
  let handle: any;
  const promise = new Promise<void | T>(
    (resolve, reject) =>
      (handle = setTimeout(() => {
        if (result instanceof Error) {
          reject(result);
        } else if (result !== undefined) {
          resolve(result);
        }
        resolve();
      }, ms)),
  );
  return { ...promise, cancel: () => clearTimeout(handle) };
}

export function killThreads(em: any): Promise<void> {
  em.PThread.terminateAllThreads();

  // Create a spinlock to wait for threads to return
  // TODO(ritave): Threads should be killed automatically, or there should be a better way to wait for them
  let spinlockHandle: any;
  const spinLockPromise = new Promise<void>(resolve => {
    spinlockHandle = setInterval(() => {
      if (em.PThread.unusedWorkers.length === 0 && em.PThread.runningWorkers.length === 0) {
        resolve();
      }
    }, 100);
  });

  const delayPromise = delay(5000, new Error('Waiting for threads to be killed timed out'));

  return Promise.race([spinLockPromise, delayPromise]).finally(() => {
    clearInterval(spinlockHandle);
    delayPromise.cancel();
  });
}
