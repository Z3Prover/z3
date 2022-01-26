# TypeScript Bindings

This directory contains JavaScript code to automatically derive TypeScript bindings for the C API, which are published on npm as [z3-solver](https://www.npmjs.com/package/z3-solver).

The readme for the bindings themselves is located in [`PUBLISHED_README.md`](./PUBLISHED_README.md).


## Building

You'll need to have emscripten set up, along with all of its dependencies. The easiest way to do that is with [emsdk](https://github.com/emscripten-core/emsdk).

Then run `npm i` to install dependencies, `npm run build-ts` to build the TypeScript wrapper, and `npm run build-wasm` to build the wasm artifact.


## Tests

Current tests are very minimal: [`test-ts-api.ts`](./test-ts-api.ts) contains a couple real cases translated very mechanically from [this file](https://github.com/Z3Prover/z3/blob/90fd3d82fce20d45ed2eececdf65545bab769503/examples/c/test_capi.c).
