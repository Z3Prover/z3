# Finite Set API Examples

This document provides usage examples for the finite set API in Java and C#.

## Java Example

```java
import com.microsoft.z3.*;

public class FiniteSetExample {
    public static void main(String[] args) {
        try (Context ctx = new Context()) {
            // Create finite set sort over integers
            Sort intSort = ctx.getIntSort();
            FiniteSetSort intSetSort = ctx.mkFiniteSetSort(intSort);
            
            // Check if it's a finite set sort
            boolean isFiniteSet = ctx.isFiniteSetSort(intSetSort);
            System.out.println("Is finite set sort: " + isFiniteSet);
            
            // Get the element sort (basis)
            Sort basis = ctx.getFiniteSetSortBasis(intSetSort);
            System.out.println("Element sort: " + basis);
            
            // Create sets
            Expr emptySet = ctx.mkFiniteSetEmpty(intSetSort);
            IntExpr one = ctx.mkInt(1);
            IntExpr two = ctx.mkInt(2);
            Expr singleton1 = ctx.mkFiniteSetSingleton(one);
            Expr singleton2 = ctx.mkFiniteSetSingleton(two);
            
            // Set operations
            Expr union = ctx.mkFiniteSetUnion(singleton1, singleton2);
            Expr intersect = ctx.mkFiniteSetIntersect(union, singleton1);
            Expr difference = ctx.mkFiniteSetDifference(union, singleton1);
            
            // Set queries
            BoolExpr member = ctx.mkFiniteSetMember(one, union);
            Expr size = ctx.mkFiniteSetSize(union);
            BoolExpr subset = ctx.mkFiniteSetSubset(singleton1, union);
            
            // Create integer range [1..10]
            Expr range = ctx.mkFiniteSetRange(ctx.mkInt(1), ctx.mkInt(10));
            
            // Solve with finite sets
            Solver solver = ctx.mkSolver();
            solver.add(ctx.mkFiniteSetMember(one, union));
            solver.add(ctx.mkEq(ctx.mkFiniteSetSize(union), ctx.mkInt(2)));
            Status status = solver.check();
            System.out.println("Solver result: " + status);
        }
    }
}
```

## C# Example

```csharp
using System;
using Microsoft.Z3;

class FiniteSetExample
{
    static void Main(string[] args)
    {
        using (Context ctx = new Context())
        {
            // Create finite set sort over integers
            Sort intSort = ctx.IntSort;
            FiniteSetSort intSetSort = ctx.MkFiniteSetSort(intSort);
            
            // Check if it's a finite set sort
            bool isFiniteSet = ctx.IsFiniteSetSort(intSetSort);
            Console.WriteLine($"Is finite set sort: {isFiniteSet}");
            
            // Get the element sort (basis)
            Sort basis = ctx.GetFiniteSetSortBasis(intSetSort);
            // Or use the property:
            Sort basis2 = intSetSort.Basis;
            Console.WriteLine($"Element sort: {basis}");
            
            // Create sets
            Expr emptySet = ctx.MkFiniteSetEmpty(intSetSort);
            IntExpr one = ctx.MkInt(1);
            IntExpr two = ctx.MkInt(2);
            Expr singleton1 = ctx.MkFiniteSetSingleton(one);
            Expr singleton2 = ctx.MkFiniteSetSingleton(two);
            
            // Set operations
            Expr union = ctx.MkFiniteSetUnion(singleton1, singleton2);
            Expr intersect = ctx.MkFiniteSetIntersect(union, singleton1);
            Expr difference = ctx.MkFiniteSetDifference(union, singleton1);
            
            // Set queries
            BoolExpr member = ctx.MkFiniteSetMember(one, union);
            Expr size = ctx.MkFiniteSetSize(union);
            BoolExpr subset = ctx.MkFiniteSetSubset(singleton1, union);
            
            // Create integer range [1..10]
            Expr range = ctx.MkFiniteSetRange(ctx.MkInt(1), ctx.MkInt(10));
            
            // Solve with finite sets
            Solver solver = ctx.MkSolver();
            solver.Add(ctx.MkFiniteSetMember(one, union));
            solver.Add(ctx.MkEq(ctx.MkFiniteSetSize(union), ctx.MkInt(2)));
            Status status = solver.Check();
            Console.WriteLine($"Solver result: {status}");
        }
    }
}
```

## API Methods

### Sort Operations
- **Java**: `mkFiniteSetSort(Sort elemSort)`, `isFiniteSetSort(Sort s)`, `getFiniteSetSortBasis(Sort s)`
- **C#**: `MkFiniteSetSort(Sort elemSort)`, `IsFiniteSetSort(Sort s)`, `GetFiniteSetSortBasis(Sort s)`

### Set Constructors
- **Java**: `mkFiniteSetEmpty(Sort setSort)`, `mkFiniteSetSingleton(Expr elem)`, `mkFiniteSetRange(Expr low, Expr high)`
- **C#**: `MkFiniteSetEmpty(Sort setSort)`, `MkFiniteSetSingleton(Expr elem)`, `MkFiniteSetRange(Expr low, Expr high)`

### Set Operations
- **Java**: `mkFiniteSetUnion(Expr s1, Expr s2)`, `mkFiniteSetIntersect(Expr s1, Expr s2)`, `mkFiniteSetDifference(Expr s1, Expr s2)`
- **C#**: `MkFiniteSetUnion(Expr s1, Expr s2)`, `MkFiniteSetIntersect(Expr s1, Expr s2)`, `MkFiniteSetDifference(Expr s1, Expr s2)`

### Set Queries
- **Java**: `mkFiniteSetMember(Expr elem, Expr set)`, `mkFiniteSetSize(Expr set)`, `mkFiniteSetSubset(Expr s1, Expr s2)`
- **C#**: `MkFiniteSetMember(Expr elem, Expr set)`, `MkFiniteSetSize(Expr set)`, `MkFiniteSetSubset(Expr s1, Expr s2)`

### Set Transformations
- **Java**: `mkFiniteSetMap(Expr f, Expr set)`, `mkFiniteSetFilter(Expr f, Expr set)`
- **C#**: `MkFiniteSetMap(Expr f, Expr set)`, `MkFiniteSetFilter(Expr f, Expr set)`

## Notes

- Finite sets are distinct from array-based sets and provide a more direct representation
- The finite set sort extends `Sort` directly (not `ArraySort`)
- All operations follow the SMT-LIB2 finite set theory syntax
- Native bindings are auto-generated from the C API during build
