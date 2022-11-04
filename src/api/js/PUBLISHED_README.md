# Z3 TypeScript Bindings

This project provides high-level and low-level TypeScript bindings for the [Z3 theorem prover](https://github.com/Z3Prover/z3). It is available on npm as [z3-solver](https://www.npmjs.com/package/z3-solver).

Z3 itself is distributed as a wasm artifact as part of this package.

## Using

```javascript
const { init } = require('z3-solver');
const {
  Z3, // Low-level C-like API
  Context, // High-level Z3Py-like API
} = await init();
```

This package has different initialization for browser and node. Your bundler and node should choose good version automatically, but you can import the one you need manually - `const { init } = require('z3-solver/node');` or `const { init } = require('z3-solver/browser');`.

### Limitations

The package requires threads, which means you'll need to be running in an environment which supports `SharedArrayBuffer`. In browsers, in addition to ensuring the browser has implemented `SharedArrayBuffer`, you'll need to serve your page with [special headers](https://web.dev/coop-coep/). There's a [neat trick](https://github.com/gzuidhof/coi-serviceworker) for doing that client-side on e.g. Github Pages, though you shouldn't use that trick in more complex applications.

The Emscripten worker model will spawn multiple instances of `z3-built.js` for long-running operations. When building for the web, you should include that file as its own script on the page - using a bundler like webpack will prevent it from loading correctly.

## High-level

You can find the documentation for the high-level Z3 API [here](https://z3prover.github.io/api/html/js/index.html). There are some usage examples in `src/high-level/high-level.test.ts`

Most of the API requires a context to run, and so you need to initialize one to access most functionality.

```javascript
const { init } = require('z3-solver');
const { Context } = await init();
const { Solver, Int, And } = new Context('main');

const x = Int.const('x');

const solver = new Solver();
solver.add(And(x.ge(0), x.le(9)));
console.log(await solver.check());
// sat
```

Typescript types try to catch errors concerning mixing of Contexts during compile time. Objects returned from `new Context('name')` have a type narrowed by the provided Context name and will fail to compile if you try to mix them.

```typescript
const { Int: Int1 } = new Context('context1');
const { Int: Int2 } = new Context('context2');

const x = Int1.const('x');
const y = Int2.const('y');

// The below will fail to compile in Typescript
x.ge(y);
```

```typescript
// Use templated functions to propagate narrowed types
function add<Name extends string>(a: Arith<Name>, b: Arith<Name>): Arith<Name> {
  return a.add(b).add(5);
}
```

Some long-running functions are promises and will run in a separate thread.
Currently Z3-solver is not thread safe, and so, high-level APIs ensures that only one long-running function can run at a time, and all other long-running requests will queue up and be run one after another.

## Low-level

You can find the documentation for the low-level Z3 API [here](https://z3prover.github.io/api/html/z3__api_8h.html), though note the differences below. `examples/low-level/` contains a couple real cases translated very mechanically from [this file](https://github.com/Z3Prover/z3/blob/90fd3d82fce20d45ed2eececdf65545bab769503/examples/c/test_capi.c).

The bindings can be used exactly as you'd use the C library. Because this is a wrapper around a C library, most of the values you'll use are just numbers representing pointers. For this reason you are strongly encouraged to make use of the TypeScript types to differentiate among the different kinds of value.

The module exports an `init` function, which is an async function which initializes the library and returns `{ em, Z3 }` - `em` contains the underlying emscripten module, which you can use to e.g. kill stray threads, and `Z3` contains the actual bindings. The other module exports are the enums defined in the Z3 API.

### Differences from the C API

#### Integers

JavaScript numbers are IEEE double-precisions floats. These can be used wherever the C API expects an `int`, `unsigned int`, `float`, or `double`.

`int64_t` and `uint64_t` cannot be precisely represented by JS numbers, so in the TS bindings they are represented by [BigInts](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Data_structures#bigint_type).

#### Out parameters

In C, to return multiple values a function will take an address to write to, conventionally referred to as an "out parameter". Sometimes the function returns a boolean to indicate success; other times it may return nothing or some other value.

In JS the convention when returning multiple values is to return records containing the values of interest.

The wrapper translates between the two conventions. For example, the C declaration

```c
void Z3_rcf_get_numerator_denominator(Z3_context c, Z3_rcf_num a, Z3_rcf_num * n, Z3_rcf_num * d);
```

is represented in the TS bindings as

```ts
function rcf_get_numerator_denominator(c: Z3_context, a: Z3_rcf_num): { n: Z3_rcf_num; d: Z3_rcf_num } {
  // ...
}
```

When there is only a single out parameter, and the return value is not otherwise of interest, the parameter is not wrapped. For example, the C declaration

```c
bool Z3_model_eval(Z3_context c, Z3_model m, Z3_ast t, bool model_completion, Z3_ast * v);
```

is represented in the TS bindings as

```ts
function model_eval(c: Z3_context, m: Z3_model, t: Z3_ast, model_completion: boolean): Z3_ast | null {
  // ...
}
```

Note that the boolean return type of the C function is translated into a nullable return type for the TS binding.

When the return value is of interest it is included in the returned record under the key `rv`.

#### Arrays

The when the C API takes an array as an argument it will also require a parameter which specifies the length of the array (since arrays do not carry their own lengths in C). In the TS bindings this is automatically inferred.

For example, the C declaration

```js
unsigned Z3_rcf_mk_roots(Z3_context c, unsigned n, Z3_rcf_num const a[], Z3_rcf_num roots[]);
```

is represented in the TS bindings as

```ts
function rcf_mk_roots(c: Z3_context, a: Z3_rcf_num[]): { rv: number; roots: Z3_rcf_num[] } {
  // ...
}
```

When there are multiple arrays which the C API expects to be of the same length, the TS bindings will enforce that this is the case.

#### Null pointers

Some of the C APIs accept or return null pointers (represented by types whose name end in `_opt`). These are represented in the TS bindings as `| null`. For example, the C declaration

```js
Z3_ast_opt Z3_model_get_const_interp(Z3_context c, Z3_model m, Z3_func_decl a);
```

is represented in the TS bindings as

```ts
function model_get_const_interp(c: Z3_context, m: Z3_model, a: Z3_func_decl): Z3_ast | null {
  // ...
}
```

#### Async functions

Certain long-running APIs are not appropriate to call on the main thread. In the TS bindings those APIs are marked as `async` and are automatically called on a different thread. This includes the following APIs:

- `Z3_simplify`
- `Z3_simplify_ex`
- `Z3_solver_check`
- `Z3_solver_check_assumptions`
- `Z3_solver_cube`
- `Z3_solver_get_consequences`
- `Z3_tactic_apply`
- `Z3_tactic_apply_ex`
- `Z3_optimize_check`
- `Z3_algebraic_roots`
- `Z3_algebraic_eval`
- `Z3_fixedpoint_query`
- `Z3_fixedpoint_query_relations`
- `Z3_fixedpoint_query_from_lvl`
- `Z3_polynomial_subresultants`

Note that these are not thread-safe, and so only one call can be running at a time. In contrast to high-level APIs, trying to call a second async API before the first completes will throw.
