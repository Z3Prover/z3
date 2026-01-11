# API Coherence Fixes - Implementation Summary

This PR addresses the API coherence issues outlined in [GitHub Discussion #8151](https://github.com/Z3Prover/z3/discussions/8151).

## Changes Implemented

### 1. C++ Bindings (`src/api/c++/z3++.h`)

Added the following missing functions:

#### Version and Trace APIs (4 functions)
- `get_version(unsigned& major, unsigned& minor, unsigned& build_number, unsigned& revision_number)` - Returns Z3 version components
- `get_full_version()` - Returns full version string
- `enable_trace(char const* tag)` - Enables debug tracing for a tag
- `disable_trace(char const* tag)` - Disables debug tracing for a tag

#### Polynomial API (1 function)
- `polynomial_subresultants(expr const& p, expr const& q, expr const& x)` - Returns nonzero subresultants of two polynomials with respect to variable x

**Example usage:**
```cpp
#include <z3++.h>

// Version functions
unsigned major, minor, build, revision;
z3::get_version(major, minor, build, revision);
std::string version = z3::get_full_version();

// Polynomial subresultants
z3::context ctx;
z3::expr x = ctx.real_const("x");
z3::expr y = ctx.real_const("y");
z3::expr p = 2*x + y;
z3::expr q = 3*x - 2*y + 2;
z3::expr_vector result = z3::polynomial_subresultants(p, q, x);
```

### 2. Java Bindings (`src/api/java/Context.java`)

Added the following missing methods:

#### Special Relations API (1 method)
- `mkTransitiveClosure(FuncDecl<BoolSort> f)` - Creates transitive closure of a binary relation

#### Polynomial API (1 method)
- `polynomialSubresultants(Expr p, Expr q, Expr x)` - Returns nonzero subresultants of two polynomials

**Example usage:**
```java
Context ctx = new Context();

// Transitive closure
Sort intSort = ctx.getIntSort();
FuncDecl partialOrder = ctx.mkPartialOrder(intSort, 0);
FuncDecl transitiveClosure = ctx.mkTransitiveClosure(partialOrder);

// Polynomial subresultants
RealExpr x = ctx.mkRealConst("x");
RealExpr y = ctx.mkRealConst("y");
ArithExpr p = ctx.mkAdd(ctx.mkMul(ctx.mkReal(2), x), y);
ArithExpr q = ctx.mkAdd(ctx.mkSub(ctx.mkMul(ctx.mkReal(3), x), ctx.mkMul(ctx.mkReal(2), y)), ctx.mkReal(2));
ASTVector result = ctx.polynomialSubresultants(p, q, x);
```

### 3. C# Bindings (`src/api/dotnet/Context.cs`)

Added the following missing methods:

#### Special Relations API (2 methods)
- `MkPartialOrder(Sort a, uint index)` - Creates a partial order relation over a sort
- `MkTransitiveClosure(FuncDecl f)` - Creates transitive closure of a binary relation

#### Polynomial API (1 method)
- `PolynomialSubresultants(Expr p, Expr q, Expr x)` - Returns nonzero subresultants of two polynomials

**Example usage:**
```csharp
using (Context ctx = new Context())
{
    // Partial order and transitive closure
    Sort intSort = ctx.IntSort;
    FuncDecl partialOrder = ctx.MkPartialOrder(intSort, 0);
    FuncDecl transitiveClosure = ctx.MkTransitiveClosure(partialOrder);
    
    // Polynomial subresultants
    RealExpr x = ctx.MkRealConst("x");
    RealExpr y = ctx.MkRealConst("y");
    ArithExpr p = ctx.MkAdd(ctx.MkMul(ctx.MkReal(2), x), y);
    ArithExpr q = ctx.MkAdd(ctx.MkSub(ctx.MkMul(ctx.MkReal(3), x), ctx.MkMul(ctx.MkReal(2), y)), ctx.MkReal(2));
    ASTVector result = ctx.PolynomialSubresultants(p, q, x);
}
```

### 4. TypeScript Bindings (`src/api/js/src/high-level/`)

Added the following missing functions:

#### Special Relations API (2 functions)
- `mkPartialOrder(sort: Sort, index: number)` - Creates a partial order relation
- `mkTransitiveClosure(f: FuncDecl)` - Creates transitive closure of a binary relation

#### Polynomial API (1 function)
- `polynomialSubresultants(p: Arith, q: Arith, x: Arith)` - Returns nonzero subresultants of two polynomials

**Example usage:**
```typescript
import { init } from 'z3-solver';

const { Context } = await init();
const ctx = new Context('main');

// Partial order and transitive closure
const intSort = ctx.Int.sort();
const partialOrder = ctx.mkPartialOrder(intSort, 0);
const transitiveClosure = ctx.mkTransitiveClosure(partialOrder);

// Polynomial subresultants
const x = ctx.Real.const('x');
const y = ctx.Real.const('y');
const p = x.mul(2).add(y);
const q = x.mul(3).sub(y.mul(2)).add(2);
const result = ctx.polynomialSubresultants(p, q, x);
```

## Testing

All changes have been validated:

1. **C++ Changes**: Compiled successfully and tested with a test program that exercises all new functions
2. **Java Bindings**: Built successfully via CMake, Native.java generated correctly with new methods
3. **C# Bindings**: Built successfully via CMake, NuGet package generated without errors
4. **TypeScript Bindings**: Type definitions updated, all new functions properly typed

## Impact Analysis

These changes address the following gaps from Discussion #8151:

| Language | Functions Added | Gap Closed |
|----------|----------------|------------|
| C++ | 5 | Version/Trace APIs + Polynomial subresultants |
| Java | 2 | Transitive closure + Polynomial subresultants |
| C# | 3 | Partial order + Transitive closure + Polynomial subresultants |
| TypeScript | 3 | Partial order + Transitive closure + Polynomial subresultants |

## Notes on RCF API

The Real Closed Field (RCF) API consisting of 38 functions is intentionally **not included** in this PR because:

1. It requires creating complete new classes (`RCFNum` in Java/C#, `rcf_num` in C++, similar in TypeScript)
2. It involves extensive operator overloading and complex number handling
3. Adding 38 functions × 4 languages = 152 function instances is a substantial undertaking
4. The RCF API is relatively specialized and has lower priority than the core missing functions

The RCF API will be addressed in a separate, focused PR to keep changes minimal and reviewable.

## Breaking Changes

None. All changes are additive only - no existing APIs were modified or removed.

## Backwards Compatibility

Fully backwards compatible. All existing code will continue to work without changes.
