import { killThreads } from './kill-threads';

describe('killThreads', () => {
  it('calls terminateAllThreads and resolves when workers are already gone', async () => {
    const unusedWorkers: unknown[] = [];
    const runningWorkers: unknown[] = [];
    const mockEm = {
      PThread: {
        terminateAllThreads: jest.fn(),
        get unusedWorkers() {
          return unusedWorkers;
        },
        get runningWorkers() {
          return runningWorkers;
        },
      },
    };

    await killThreads(mockEm);

    expect(mockEm.PThread.terminateAllThreads).toHaveBeenCalledTimes(1);
  });

  it('resolves once running workers are terminated', async () => {
    const runningWorkers: unknown[] = [{}];
    const mockEm = {
      PThread: {
        terminateAllThreads: jest.fn(),
        unusedWorkers: [] as unknown[],
        get runningWorkers() {
          return runningWorkers;
        },
      },
    };

    // Simulate workers being terminated after a short delay.
    setTimeout(() => {
      runningWorkers.length = 0;
    }, 150);

    await killThreads(mockEm);

    expect(mockEm.PThread.terminateAllThreads).toHaveBeenCalledTimes(1);
  });
});
