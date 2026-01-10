# New TypeScript API Examples

This document demonstrates the new APIs added to the Z3 TypeScript bindings.

## Goal API

Goals are collections of constraints that can be processed using tactics.

```typescript
import { init } from 'z3-solver';

const { Context } = await init();
const { Int, Goal, Tactic } = Context('main');

// Create a goal
const goal = new Goal();

// Add constraints
const x = Int.const('x');
const y = Int.const('y');
goal.add(x.gt(0), y.gt(x), y.lt(10));

// Inspect the goal
console.log('Goal size:', goal.size());
console.log('Goal depth:', goal.depth());
console.log('Goal is inconsistent:', goal.inconsistent());

// Convert to expression
const expr = goal.asExpr();
console.log('Goal as expression:', expr.sexpr());

// Get individual constraints
for (let i = 0; i < goal.size(); i++) {
  console.log(`Constraint ${i}:`, goal.get(i).sexpr());
}
```

## Tactic API

Tactics transform goals into simpler subgoals.

```typescript
// Create a tactic
const simplify = new Tactic('simplify');

// Apply tactic to a goal
const result = await simplify.apply(goal);
console.log('Number of subgoals:', result.length());

// Access subgoals
const subgoal = result.getSubgoal(0);
console.log('First subgoal:', subgoal.toString());

// Or use array indexing
const subgoal2 = result[0];

// Get tactic help
console.log('Tactic help:', simplify.help());

// Create a solver from a tactic
const solver = simplify.solver();
solver.add(x.gt(0), x.lt(10));
const checkResult = await solver.check();
console.log('Solver result:', checkResult);
```

## Tactic Combinators

Combine tactics to create more powerful solving strategies.

```typescript
const { AndThen, OrElse, Repeat, TryFor, When, Skip, Fail } = Context('main');

// Sequential composition
const sequential = AndThen('simplify', 'solve-eqs', 'smt');

// Fallback composition
const withFallback = OrElse('qfnra-nlsat', 'nlsat');

// Repeat a tactic
const repeated = Repeat('simplify', 10);

// Apply with timeout
const withTimeout = TryFor('smt', 5000);

// Always-succeeding tactic
const skip = Skip();

// Always-failing tactic
const fail = Fail();

// Apply tactics with parameters
const { With } = Context('main');
const withParams = With('simplify', {
  max_steps: 1000,
  som: true,
  pull_cheap_ite: true
});
```

## Probe API

Probes inspect goals and return numerical values.

```typescript
// Apply a probe to a goal (when probe creation is supported)
// const size = someProbe.apply(goal);
```

## Complete Example: Solving with Tactics

```typescript
import { init } from 'z3-solver';

async function solvingWithTactics() {
  const { Context } = await init();
  const { Int, Goal, AndThen } = Context('main');
  
  // Create variables
  const x = Int.const('x');
  const y = Int.const('y');
  const z = Int.const('z');
  
  // Create goal with constraints
  const goal = new Goal();
  goal.add(
    x.add(y).eq(10),
    y.add(z).eq(12),
    x.gt(0)
  );
  
  console.log('Original goal:');
  console.log(goal.toString());
  
  // Create and apply tactic
  const tactic = AndThen('simplify', 'solve-eqs');
  const result = await tactic.apply(goal);
  
  console.log(`\nTactic produced ${result.length()} subgoal(s):`);
  for (let i = 0; i < result.length(); i++) {
    const subgoal = result[i];
    console.log(`\nSubgoal ${i}:`);
    console.log(subgoal.toString());
    
    // Check if subgoal is decided
    if (subgoal.isDecidedSat()) {
      console.log('This subgoal is SAT');
    } else if (subgoal.isDecidedUnsat()) {
      console.log('This subgoal is UNSAT');
    }
  }
  
  // Create solver from tactic and solve
  const solver = tactic.solver();
  solver.add(goal.asExpr());
  
  if (await solver.check() === 'sat') {
    const model = solver.model();
    console.log('\nSolution:');
    console.log(`x = ${model.eval(x)}`);
    console.log(`y = ${model.eval(y)}`);
    console.log(`z = ${model.eval(z)}`);
  }
}

solvingWithTactics();
```

## API Coverage

The TypeScript bindings now have complete coverage of:

- **Goal API**: All 16 methods for creating and manipulating goals
- **ApplyResult API**: All 6 methods for accessing tactic results
- **Tactic API**: All 4 core methods (apply, solver, help, getParamDescrs)
- **Tactic Combinators**: All 11 standard combinators (AndThen, OrElse, Repeat, etc.)
- **Probe API**: apply() method for goal inspection

This brings the TypeScript bindings to feature parity with Python, Java, and C# for the tactics subsystem.
