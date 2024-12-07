# TypeScript Bindings

This directory contains JavaScript code to automatically derive TypeScript bindings for the C API, which are published on npm as [z3-solver](https://www.npmjs.com/package/z3-solver).

The readme for the bindings themselves is located in [`PUBLISHED_README.md`](./PUBLISHED_README.md).


## Building

You'll need to have emscripten set up, along with all of its dependencies. The easiest way to do that is with [emsdk](https://github.com/emscripten-core/emsdk). Newer versions of emscripten may break the build; you can find the version used in CI in [this file](https://github.com/Z3Prover/z3/blob/master/.github/workflows/wasm.yml#L13).

Then run `npm i` to install dependencies, `npm run build:ts` to build the TypeScript wrapper, and `npm run build:wasm` to build the wasm artifact.

### Build on your own

Consult the file [build-wasm.ts](https://github.com/Z3Prover/z3/blob/master/src/api/js/scripts/build-wasm.ts) for configurations used for building wasm.

## Tests

Run `npm test` after building to run tests.
