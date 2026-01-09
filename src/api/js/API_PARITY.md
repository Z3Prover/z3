# TypeScript/JavaScript API Parity Implementation

## Overview

This document describes the API parity updates implemented for the Z3 TypeScript/JavaScript bindings, addressing the gaps identified in [GitHub Discussion #8121](https://github.com/Z3Prover/z3/discussions/8121).

## Implemented APIs

### Solver Introspection APIs

#### `units(): AstVector<Name, Bool<Name>>`
Retrieve the set of literals that were inferred by the solver as unit literals. These are boolean literals that the solver has determined must be true in all models.

**C API:** `Z3_solver_get_units`

**Example:**
```typescript
const solver = new Solver();
const x = Bool.const('x');
solver.add(x);
await solver.check();
const units = solver.units();
console.log('Unit literals:', units.length());
```

#### `nonUnits(): AstVector<Name, Bool<Name>>`
Retrieve the set of tracked boolean literals that are not unit literals.

**C API:** `Z3_solver_get_non_units`

**Example:**
```typescript
const solver = new Solver();
const x = Bool.const('x');
const y = Bool.const('y');
solver.add(x.or(y));
await solver.check();
const nonUnits = solver.nonUnits();
```

#### `trail(): AstVector<Name, Bool<Name>>`
Retrieve the trail of boolean literals assigned by the solver during solving. The trail represents the sequence of decisions and propagations made by the solver.

**C API:** `Z3_solver_get_trail`

**Example:**
```typescript
const solver = new Solver();
const x = Bool.const('x');
const y = Bool.const('y');
solver.add(x.implies(y));
solver.add(x);
await solver.check();
const trail = solver.trail();
console.log('Trail length:', trail.length());
```

### Congruence Closure APIs

#### `congruenceRoot(expr: Expr<Name>): Expr<Name>`
Retrieve the root of the congruence class containing the given expression. This is useful for understanding equality reasoning in the solver.

**C API:** `Z3_solver_congruence_root`

**Note:** This works primarily with SimpleSolver and may not work with terms eliminated during preprocessing.

**Example:**
```typescript
const solver = new Solver();
const x = Int.const('x');
const y = Int.const('y');
solver.add(x.eq(y));
await solver.check();
const root = solver.congruenceRoot(x);
```

#### `congruenceNext(expr: Expr<Name>): Expr<Name>`
Retrieve the next expression in the congruence class containing the given expression. The congruence class forms a circular linked list.

**C API:** `Z3_solver_congruence_next`

**Note:** This works primarily with SimpleSolver and may not work with terms eliminated during preprocessing.

**Example:**
```typescript
const solver = new Solver();
const x = Int.const('x');
const y = Int.const('y');
const z = Int.const('z');
solver.add(x.eq(y));
solver.add(y.eq(z));
await solver.check();
const next = solver.congruenceNext(x);
```

#### `congruenceExplain(a: Expr<Name>, b: Expr<Name>): Expr<Name>`
Explain why two expressions are congruent according to the solver's reasoning. Returns a proof term explaining the congruence.

**C API:** `Z3_solver_congruence_explain`

**Note:** This works primarily with SimpleSolver and may not work with terms eliminated during preprocessing.

**Example:**
```typescript
const solver = new Solver();
const x = Int.const('x');
const y = Int.const('y');
solver.add(x.eq(y));
await solver.check();
const explanation = solver.congruenceExplain(x, y);
```

### Model Sort Universe APIs

#### `numSorts(): number`
Return the number of uninterpreted sorts that have an interpretation in the model.

**C API:** `Z3_model_get_num_sorts`

**Example:**
```typescript
const model = solver.model();
console.log('Number of sorts:', model.numSorts());
```

#### `getSort(i: number): Sort<Name>`
Return the uninterpreted sort at the given index.

**C API:** `Z3_model_get_sort`

**Example:**
```typescript
const model = solver.model();
for (let i = 0; i < model.numSorts(); i++) {
  const sort = model.getSort(i);
  console.log('Sort:', sort.toString());
}
```

#### `getSorts(): Sort<Name>[]`
Return all uninterpreted sorts that have an interpretation in the model.

**Example:**
```typescript
const model = solver.model();
const sorts = model.getSorts();
for (const sort of sorts) {
  console.log('Sort:', sort.toString());
}
```

#### `sortUniverse(sort: Sort<Name>): AstVector<Name, AnyExpr<Name>>`
Return the finite set of elements that represent the interpretation for the given sort. This is only applicable to uninterpreted sorts with finite interpretations.

**C API:** `Z3_model_get_sort_universe`

**Example:**
```typescript
const { Solver, Sort, Const } = await init();
const solver = new Solver();
const A = Sort.declare('A');
const x = Const('x', A);
const y = Const('y', A);
solver.add(x.neq(y));
await solver.check();
const model = solver.model();
const universe = model.sortUniverse(A);
console.log('Universe has', universe.length(), 'elements');
```

### File Loading API

#### `fromFile(filename: string): void`
Load SMT-LIB2 format assertions from a file into the solver.

**C API:** `Z3_solver_from_file`

**Example:**
```typescript
const solver = new Solver();
solver.fromFile('problem.smt2');
const result = await solver.check();
```

## API Parity Status

After this implementation, the TypeScript API now has feature parity with Python, C++, Java, and C# bindings for the following API families:

- ✅ Solver introspection APIs (units, non-units, trail)
- ✅ Congruence closure APIs (root, next, explain)
- ✅ Model sort universe APIs (numSorts, getSort, sortUniverse)
- ✅ File loading APIs (fromFile, fromString)

## Testing

Comprehensive test cases have been added to `src/high-level/high-level.test.ts` covering:
- Solver units API
- Solver non-units API
- Solver trail API
- Congruence root API
- Congruence next API
- Congruence explain API
- Model numSorts API
- Model getSort API
- Model getSorts API
- Model sortUniverse API
- File loading API existence check

## Example

A complete demonstration of all new APIs is available in `examples/high-level/api-parity-demo.ts`.

To run the example (after building):
```bash
npm run build:ts
npm run build:wasm
node examples/high-level/api-parity-demo.ts
```

## Implementation Details

### Design Principles
- **Minimal changes**: Only added new public methods, no modifications to existing functionality
- **Consistency**: Methods follow existing naming conventions and patterns in the TypeScript API
- **Documentation**: All methods include comprehensive JSDoc comments with examples
- **Type safety**: Full TypeScript type annotations for all new APIs

### Technical Notes
- All low-level C API bindings are auto-generated from `z3_api.h`
- High-level wrapper methods delegate to low-level bindings
- No changes to build system or tooling required
- Backward compatible - no breaking changes

## Files Modified

1. `src/high-level/types.ts` - Added type definitions for new APIs
2. `src/high-level/high-level.ts` - Implemented new methods in SolverImpl and ModelImpl
3. `src/high-level/high-level.test.ts` - Added comprehensive test coverage
4. `examples/high-level/api-parity-demo.ts` - Created demonstration example

## References

- [GitHub Discussion #8121](https://github.com/Z3Prover/z3/discussions/8121) - Original API coherence analysis
- [Z3 C API Documentation](https://z3prover.github.io/api/html/group__capi.html)
- [Z3 Python API](https://z3prover.github.io/api/html/namespacez3py.html)
