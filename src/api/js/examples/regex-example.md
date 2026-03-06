# Regular Expression Support in Z3 TypeScript API

This document demonstrates the new regular expression support added to the Z3 TypeScript API.

## Basic Usage

### Creating Regular Expressions

```typescript
const { Re, String: Str, InRe, Solver } = Context('main');

// Create a regex from a string
const hello = Re.toRe('hello');

// Check if a string matches
const solver = new Solver();
solver.add(InRe('hello', hello));
await solver.check(); // sat
```

### Star Operator (Zero or More)

```typescript
const { Re, InRe, Star } = Context('main');

const a = Re.toRe('a');
const aStar = Star(a);

// Empty string matches a*
InRe('', aStar);     // true

// Multiple 'a's match
InRe('aaa', aStar);  // true
```

### Plus Operator (One or More)

```typescript
const { Re, InRe, Plus } = Context('main');

const a = Re.toRe('a');
const aPlus = Plus(a);

// Empty string does NOT match a+
InRe('', aPlus);     // false

// One or more 'a's match
InRe('aa', aPlus);   // true
```

### Option Operator (Zero or One)

```typescript
const { Re, InRe, Option } = Context('main');

const a = Re.toRe('a');
const aOpt = Option(a);

// Both empty and 'a' match a?
InRe('', aOpt);      // true
InRe('a', aOpt);     // true
InRe('aa', aOpt);    // false
```

### Union (Or)

```typescript
const { Re, InRe, Union } = Context('main');

const a = Re.toRe('a');
const b = Re.toRe('b');
const aOrB = Union(a, b);

// Either 'a' or 'b' match
InRe('a', aOrB);     // true
InRe('b', aOrB);     // true
InRe('c', aOrB);     // false
```

### Intersect (And)

```typescript
const { Re, InRe, Intersect, Star } = Context('main');

const a = Re.toRe('a');
const b = Re.toRe('b');
const both = Intersect(Star(a), Star(b));

// Only empty string matches both a* and b*
InRe('', both);      // true
InRe('a', both);     // false
```

### Range

```typescript
const { Range, InRe } = Context('main');

const azRange = Range('a', 'z');

// Lowercase letters match
InRe('m', azRange);  // true

// Others don't
InRe('1', azRange);  // false
InRe('Z', azRange);  // false
```

### Loop (Bounded Repetition)

```typescript
const { Re, InRe, Loop } = Context('main');

const a = Re.toRe('a');

// Between 2 and 3 repetitions
const a2to3 = Loop(a, 2, 3);
InRe('aa', a2to3);   // true
InRe('aaa', a2to3);  // true
InRe('a', a2to3);    // false
InRe('aaaa', a2to3); // false

// At least 2 repetitions (hi=0 or omitted means unbounded)
const a2Plus = Loop(a, 2, 0);  // or Loop(a, 2)
InRe('aa', a2Plus);   // true
InRe('aaa', a2Plus);  // true
InRe('aaaa', a2Plus); // true
InRe('a', a2Plus);    // false
```

### Power (Exact Repetition)

```typescript
const { Re, InRe, Power } = Context('main');

const a = Re.toRe('a');
const a3 = Power(a, 3);

// Exactly 3 repetitions match
InRe('aaa', a3);     // true

// Others don't
InRe('aa', a3);      // false
InRe('aaaa', a3);    // false
```

### Complement (Negation)

```typescript
const { Re, InRe, Complement } = Context('main');

const a = Re.toRe('a');
const notA = Complement(a);

// Everything except 'a' matches
InRe('a', notA);     // false
InRe('b', notA);     // true
InRe('', notA);      // true
```

### Diff (Set Difference)

```typescript
const { Re, InRe, Diff, Star } = Context('main');

const a = Re.toRe('a');
const b = Re.toRe('b');
const diff = Diff(Star(a), b);

// a* except 'b'
InRe('aaa', diff);   // true
InRe('b', diff);     // false
```

### ReConcat (Concatenation)

```typescript
const { Re, InRe, ReConcat } = Context('main');

const hello = Re.toRe('hello');
const world = Re.toRe('world');
const helloworld = ReConcat(hello, world);

// Concatenated strings match
InRe('helloworld', helloworld);  // true
InRe('hello', helloworld);       // false
```

## Method Chaining

Regular expression objects support method chaining:

```typescript
const { Re, InRe } = Context('main');

const a = Re.toRe('a');

// Using methods
const aStar = a.star();
const aPlus = a.plus();
const aOpt = a.option();
const notA = a.complement();

// Chaining
const complex = a.plus().union(Re.toRe('b').star());
```

## Complex Example: Pattern Matching

```typescript
const { Re, String: Str, InRe, Union, Star, Solver } = Context('main');

const x = Str.const('x');
const a = Re.toRe('a');
const b = Re.toRe('b');

// Pattern: any combination of 'a' and 'b'
const pattern = Star(Union(a, b));

const solver = new Solver();
solver.add(InRe(x, pattern));
solver.add(x.length().eq(5));

if (await solver.check() === 'sat') {
  const model = solver.model();
  const result = model.eval(x);
  // Result will be a 5-character string containing only 'a' and 'b'
  console.log(result.asString()); // e.g., "aabba"
}
```

## API Reference

### Factory Methods

- `Re.sort(seqSort)` - Create a regex sort
- `Re.toRe(seq)` - Convert sequence/string to regex

### Operators

- `Star(re)` - Zero or more repetitions (*)
- `Plus(re)` - One or more repetitions (+)
- `Option(re)` - Zero or one repetition (?)
- `Union(...res)` - Or operation (|)
- `Intersect(...res)` - And operation (&)
- `ReConcat(...res)` - Concatenation
- `Complement(re)` - Negation (~)
- `Diff(a, b)` - Set difference (a \ b)
- `Range(lo, hi)` - Character range
- `Loop(re, lo, hi?)` - Bounded repetition {lo,hi} or at least lo if hi=0 or omitted
- `Power(re, n)` - Exact repetition {n}

### Special Patterns

- `AllChar(reSort)` - Match any single character
- `Empty(reSort)` - Empty language
- `Full(reSort)` - Match all strings

### Membership Test

- `InRe(seq, re)` - Test if sequence matches regex

## Notes

- All regex operations are symbolic - they create constraints rather than executing pattern matching
- The solver finds strings that satisfy the regex constraints
- Regular expressions can be combined with other Z3 constraints (length, containment, etc.)
- This implementation follows the SMT-LIB2 regular expression theory
