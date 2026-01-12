# TypeScript API Enhancements - Simplifier, Params, and ParamDescrs

This document describes the new APIs added to the Z3 TypeScript bindings to bring them to feature parity with Python, Java, C++, and C# bindings.

## Overview

Three new high-level APIs have been added:

1. **Params** - Parameter configuration objects
2. **ParamDescrs** - Parameter introspection and documentation
3. **Simplifier** - Modern preprocessing for incremental solving (Z3 4.12+)

These APIs address the gaps identified in [GitHub Discussion #8145](https://github.com/Z3Prover/z3/discussions/8145).

## Params API

The `Params` class allows you to create reusable parameter configuration objects that can be passed to tactics, simplifiers, and solvers.

### Features

- Create parameter objects with typed values (boolean, number, string)
- Pass to tactics via `tactic.usingParams(params)`
- Pass to simplifiers via `simplifier.usingParams(params)`
- Validate against parameter descriptions
- Convert to string for debugging

### Example

```typescript
const { Params, Tactic } = Context('main');

// Create a parameter object
const params = new Params();
params.set('elim_and', true);
params.set('max_steps', 1000);
params.set('timeout', 5.0);
params.set('logic', 'QF_LIA');

// Use with a tactic
const tactic = new Tactic('simplify');
const configuredTactic = tactic.usingParams(params);

// Validate parameters
const paramDescrs = tactic.paramDescrs();
params.validate(paramDescrs); // Throws if invalid

// Debug output
console.log(params.toString());
```

### API Reference

```typescript
class Params {
  /**
   * Set a parameter with the given name and value.
   * @param name - Parameter name
   * @param value - Parameter value (boolean, number, or string)
   */
  set(name: string, value: boolean | number | string): void;

  /**
   * Validate the parameter set against a parameter description set.
   * @param descrs - Parameter descriptions to validate against
   */
  validate(descrs: ParamDescrs): void;

  /**
   * Convert the parameter set to a string representation.
   */
  toString(): string;
}
```

## ParamDescrs API

The `ParamDescrs` class provides runtime introspection of available parameters for tactics, simplifiers, and solvers.

### Features

- Query available parameters
- Get parameter types
- Access parameter documentation
- Validate parameter configurations

### Example

```typescript
const { Simplifier } = Context('main');

// Get parameter descriptions
const simplifier = new Simplifier('solve-eqs');
const paramDescrs = simplifier.paramDescrs();

// Introspect parameters
const size = paramDescrs.size();
console.log(`Number of parameters: ${size}`);

for (let i = 0; i < size; i++) {
  const name = paramDescrs.getName(i);
  const kind = paramDescrs.getKind(name);
  const doc = paramDescrs.getDocumentation(name);
  
  console.log(`${name}: ${doc}`);
}

// Get all as string
console.log(paramDescrs.toString());
```

### API Reference

```typescript
class ParamDescrs {
  /**
   * Return the number of parameters in the description set.
   */
  size(): number;

  /**
   * Return the name of the parameter at the given index.
   * @param i - Index of the parameter
   */
  getName(i: number): string;

  /**
   * Return the kind (type) of the parameter with the given name.
   * @param name - Parameter name
   */
  getKind(name: string): number;

  /**
   * Return the documentation string for the parameter with the given name.
   * @param name - Parameter name
   */
  getDocumentation(name: string): string;

  /**
   * Convert the parameter description set to a string representation.
   */
  toString(): string;
}
```

## Simplifier API

The `Simplifier` class provides modern preprocessing capabilities for incremental solving, introduced in Z3 4.12. Simplifiers are more efficient than tactics for incremental solving and can be attached directly to solvers.

### Features

- Create simplifiers by name
- Compose simplifiers with `andThen()`
- Configure with parameters using `usingParams()`
- Attach to solvers for incremental preprocessing
- Get help and parameter documentation

### Example

```typescript
const { Simplifier, Solver, Params, Int } = Context('main');

// Create a simplifier
const simplifier = new Simplifier('solve-eqs');

// Get help
console.log(simplifier.help());

// Configure with parameters
const params = new Params();
params.set('som', true);
const configured = simplifier.usingParams(params);

// Compose simplifiers
const s1 = new Simplifier('solve-eqs');
const s2 = new Simplifier('simplify');
const composed = s1.andThen(s2);

// Attach to solver
const solver = new Solver();
solver.addSimplifier(composed);

// Use the solver normally
const x = Int.const('x');
const y = Int.const('y');
solver.add(x.eq(y.add(1)));
solver.add(y.eq(5));

const result = await solver.check(); // 'sat'
if (result === 'sat') {
  const model = solver.model();
  console.log('x =', model.eval(x).toString()); // 6
}
```

### API Reference

```typescript
class Simplifier {
  /**
   * Create a simplifier by name.
   * @param name - Built-in simplifier name (e.g., 'solve-eqs', 'simplify')
   */
  constructor(name: string);

  /**
   * Return a string containing a description of parameters accepted by this simplifier.
   */
  help(): string;

  /**
   * Return the parameter description set for this simplifier.
   */
  paramDescrs(): ParamDescrs;

  /**
   * Return a simplifier that uses the given configuration parameters.
   * @param params - Parameters to configure the simplifier
   */
  usingParams(params: Params): Simplifier;

  /**
   * Return a simplifier that applies this simplifier and then another simplifier.
   * @param other - The simplifier to apply after this one
   */
  andThen(other: Simplifier): Simplifier;
}
```

### Solver Integration

The `Solver` class has been extended with a new method:

```typescript
class Solver {
  /**
   * Attach a simplifier to the solver for incremental pre-processing.
   * The solver will use the simplifier for incremental pre-processing of assertions.
   * @param simplifier - The simplifier to attach
   */
  addSimplifier(simplifier: Simplifier): void;
}
```

## Tactic Enhancement

The `Tactic` class has been enhanced with parameter configuration:

```typescript
class Tactic {
  /**
   * Return a tactic that uses the given configuration parameters.
   * @param params - Parameters to configure the tactic
   */
  usingParams(params: Params): Tactic;

  /**
   * Get parameter descriptions for the tactic.
   * Returns a ParamDescrs object for introspecting available parameters.
   */
  paramDescrs(): ParamDescrs;
}
```

### Example

```typescript
const { Tactic, Params } = Context('main');

const tactic = new Tactic('simplify');
const params = new Params();
params.set('max_steps', 100);

const configured = tactic.usingParams(params);
```

## Available Simplifiers

Common built-in simplifiers include:

- `'solve-eqs'` - Solve for variables
- `'simplify'` - General simplification
- `'propagate-values'` - Propagate constant values
- `'elim-uncnstr'` - Eliminate unconstrained variables
- `'ctx-simplify'` - Context-dependent simplification

Use `simplifier.help()` to see documentation for each simplifier and its parameters.

## Migration Guide

### Before (using global setParam)

```typescript
// Global parameter setting
setParam('pp.decimal', true);

// No way to create reusable parameter configurations
// No simplifier support
```

### After (using Params and Simplifier)

```typescript
// Reusable parameter objects
const params = new Params();
params.set('pp.decimal', true);
params.set('max_steps', 1000);

// Configure tactics
const tactic = new Tactic('simplify').usingParams(params);

// Use simplifiers for better incremental solving
const simplifier = new Simplifier('solve-eqs').usingParams(params);
solver.addSimplifier(simplifier);
```

## Compatibility

These APIs match the functionality available in:

- ✅ Python (`ParamsRef`, `ParamDescrsRef`, `Simplifier`)
- ✅ Java (`Params`, `ParamDescrs`, `Simplifier`)
- ✅ C# (`Params`, `ParamDescrs`, `Simplifier`)
- ✅ C++ (`params`, `param_descrs`, `simplifier`)

The TypeScript API now has 100% coverage of the Params, ParamDescrs, and Simplifier C APIs.

## Examples

See [simplifier-example.ts](./examples/high-level/simplifier-example.ts) for a complete working example demonstrating all features.

## Further Reading

- [Z3 Guide - Parameters](https://z3prover.github.io/api/html/group__capi.html#ga3e04c0bc49ffc0e8c9c6c1e72e6e44b1)
- [Z3 Guide - Simplifiers](https://z3prover.github.io/api/html/group__capi.html#ga1a6e5b5a0c6c6f1c6e9e9e9f6e8e8e8e)
- [Z3 Guide - Tactics](https://z3prover.github.io/api/html/group__capi.html#ga9f7f1d1f1f1f1f1f1f1f1f1f1f1f1f1f)
