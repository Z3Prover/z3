import { readFileSync } from 'fs';
import { runInNewContext } from 'vm';

const asyncWrapperSource = readFileSync(require.resolve('./async-wrapper.js'), 'utf8');

describe('async wrapper', () => {
  it('ignores a completion from a cancelled call after another call starts', async () => {
    const context: any = { Module: {}, setTimeout, clearTimeout };
    runInNewContext(
      `${asyncWrapperSource}
      globalThis.getAsyncCallId = () => current_async_call_id;
      globalThis.resolveAsync = resolve_async;`,
      context,
    );
    const { Module } = context;

    let firstCallId = 0;
    const firstCall = Module.async_call(() => {
      firstCallId = context.getAsyncCallId();
    });
    Module.async_cancel(new Error('cancelled'));
    await expect(firstCall).rejects.toThrow('cancelled');

    let secondCallId = 0;
    let secondCallSettled = false;
    const secondCall = Module.async_call(() => {
      secondCallId = context.getAsyncCallId();
    }).then((value: string) => {
      secondCallSettled = true;
      return value;
    });

    context.resolveAsync(firstCallId, 'stale result');
    await new Promise(resolve => setTimeout(resolve, 0));
    expect(secondCallSettled).toBe(false);

    context.resolveAsync(secondCallId, 'current result');
    await expect(secondCall).resolves.toBe('current result');
  });
});
