/**
 * Terminates all Emscripten worker threads spawned by Z3.
 *
 * Long-running Z3 operations (such as `solver.check()`) run on background
 * worker threads. In Node.js these workers keep the process alive even after
 * Z3 has finished. Call this function once you are done using Z3 to allow the
 * Node.js process to exit cleanly.
 *
 * ```typescript
 * import { init, killThreads } from 'z3-solver';
 *
 * const api = await init();
 * // ... use Z3 ...
 * await killThreads(api.em);
 * ```
 * @category Global
 */
export function killThreads(em: any): Promise<void> {
  em.PThread.terminateAllThreads();

  // Poll until all workers have been terminated.
  let intervalHandle: ReturnType<typeof setInterval>;
  let timeoutHandle: ReturnType<typeof setTimeout>;

  const lockPromise = new Promise<void>(resolve => {
    intervalHandle = setInterval(() => {
      if (!em.PThread.unusedWorkers.length && !em.PThread.runningWorkers.length) {
        clearInterval(intervalHandle);
        clearTimeout(timeoutHandle);
        resolve();
      }
    }, 100);
  });

  const delayPromise = new Promise<never>((_, reject) => {
    timeoutHandle = setTimeout(() => {
      clearInterval(intervalHandle);
      reject(new Error('Waiting for threads to be killed timed out'));
    }, 5000);
  });

  return Promise.race([lockPromise, delayPromise]);
}
