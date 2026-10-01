// this wrapper works with async-fns to provide promise-based off-thread versions of some functions
// It's prepended directly by emscripten to the resulting z3-built.js

let threadTimeouts = [];

let capability = null;
function resolve_async(val) {
  // setTimeout is a workaround for https://github.com/emscripten-core/emscripten/issues/15900
  if (capability == null) {
    return;
  }
  let cap = capability;
  capability = null;

  setTimeout(() => {
    cap.resolve(val);
  }, 0);
}

function reject_async(val) {
  if (capability == null) {
    return;
  }
  let cap = capability;
  capability = null;

  setTimeout(() => {
    cap.reject(val);
  }, 0);
}

Module.async_call = function (f, ...args) {
  if (capability !== null) {
    throw new Error(`you can't execute multiple async functions at the same time; let the previous one finish first`);
  }
  let promise = new Promise((resolve, reject) => {
    capability = { resolve, reject };
  });
  f(...args);
  return promise;
};

function clear_thread_timeouts() {
  while (threadTimeouts.length > 0) {
    clearTimeout(threadTimeouts.shift());
  }
}

// Abandons the pending async call (if any): rejects its promise so that callers waiting on it
// (and any mutex guarding it) are released, and clears the keep-alive timers so the process can exit.
// Only call this once the worker threads running the call have been terminated (see killThreads).
Module.async_cancel = function (reason) {
  clear_thread_timeouts();
  reject_async(reason !== undefined ? reason : new Error('async call was cancelled'));
};

// If the module aborts (e.g. a trap on a worker thread), the pending async call can never settle.
{
  const userOnAbort = Module['onAbort'];
  Module['onAbort'] = function (what) {
    Module.async_cancel(new Error('Z3 module aborted: ' + what));
    if (typeof userOnAbort === 'function') {
      userOnAbort(what);
    }
  };
}
