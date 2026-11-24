import type { tracer } from 'junco';

type Recorder = tracer.ProfileRecorder<string>;

/** Both sinks see each original event at the same interned path and share one lifecycle. */
export function pairedRecorder(live: Recorder, samples: Recorder): Recorder {
  const views = new Map<string, Recorder>();
  const failures = new Set<unknown>();
  let closing: Promise<void> | undefined;
  async function settle(action: 'flush' | 'close') {
    const results = await Promise.allSettled([live, samples].map(async sink => sink[action]()));
    for (const result of results) if (result.status === 'rejected') failures.add(result.reason);
    if (action === 'close') views.clear();
    if (failures.size) throw new AggregateError([...failures], `Recorder ${action} failed`);
  }
  function context(a: Recorder, b: Recorder): Recorder {
    if (a.path !== b.path) throw new Error(`Recorder path mismatch: ${a.path} / ${b.path}`);
    const view: Recorder = Object.freeze({
      get root() { return root; },
      path: a.path,
      add_context(id: string) {
        if (closing) throw new Error('Recorder closed');
        if (!id) return view;
        const child = a.add_context(id);
        return views.get(child.path) ?? context(child, b.add_context(id));
      },
      record(event: tracer.ProfileEvent<string>) {
        if (closing) return;
        try { a.record(event); } catch (e) { failures.add(e); }
        try { b.record(event); } catch (e) { failures.add(e); }
      },
      flush: () => closing ?? settle('flush'),
      close: () => closing ??= settle('close'),
    });
    views.set(view.path, view);
    return view;
  }
  const root = context(live, samples);
  return root;
}
