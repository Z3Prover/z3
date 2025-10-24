# Finite Set API Documentation

This document describes the finite set API added to Z3.

## Overview

The finite set API provides term constructors for finite sets as defined in `finite_set_decl_plugin.h`. 
These are distinct from the existing array-based sets and provide a more direct representation for finite sets.

## C API

All functions are declared in `src/api/z3_api.h` and implemented in `src/api/api_finite_set.cpp`.

### Sort Constructor

- `Z3_sort Z3_mk_finite_set_sort(Z3_context c, Z3_sort elem_sort)` - Create a finite set sort over element sort

### Sort Queries

- `bool Z3_is_finite_set_sort(Z3_context c, Z3_sort s)` - Check if a sort is a finite set sort
- `Z3_sort Z3_get_finite_set_sort_basis(Z3_context c, Z3_sort s)` - Get the element sort of a finite set sort

### Term Constructors

- `Z3_ast Z3_mk_finite_set_empty(Z3_context c, Z3_sort set_sort)` - Create an empty finite set
- `Z3_ast Z3_mk_finite_set_singleton(Z3_context c, Z3_ast elem)` - Create a singleton set
- `Z3_ast Z3_mk_finite_set_union(Z3_context c, Z3_ast s1, Z3_ast s2)` - Create the union of two sets
- `Z3_ast Z3_mk_finite_set_intersect(Z3_context c, Z3_ast s1, Z3_ast s2)` - Create the intersection
- `Z3_ast Z3_mk_finite_set_difference(Z3_context c, Z3_ast s1, Z3_ast s2)` - Create the set difference
- `Z3_ast Z3_mk_finite_set_member(Z3_context c, Z3_ast elem, Z3_ast set)` - Check membership
- `Z3_ast Z3_mk_finite_set_size(Z3_context c, Z3_ast set)` - Get the cardinality
- `Z3_ast Z3_mk_finite_set_subset(Z3_context c, Z3_ast s1, Z3_ast s2)` - Check subset relation
- `Z3_ast Z3_mk_finite_set_map(Z3_context c, Z3_ast f, Z3_ast set)` - Apply function to all elements
- `Z3_ast Z3_mk_finite_set_filter(Z3_context c, Z3_ast f, Z3_ast set)` - Filter set with predicate
- `Z3_ast Z3_mk_finite_set_range(Z3_context c, Z3_ast low, Z3_ast high)` - Create range [low .. high]

## Python API

All functions are available in `z3.py`:

### Classes

- `FiniteSetSortRef` - Finite set sort reference
- `FiniteSetRef` - Finite set expression reference

### Functions

- `FiniteSetSort(elem_sort)` - Create finite set sort
- `FiniteSetEmpty(set_sort)` - Create empty set
- `FiniteSetSingleton(elem)` - Create singleton set
- `FiniteSetUnion(s1, s2)` - Union (also `s1 | s2`)
- `FiniteSetIntersect(s1, s2)` - Intersection (also `s1 & s2`)
- `FiniteSetDifference(s1, s2)` - Difference (also `s1 - s2`)
- `FiniteSetMember(elem, set)` - Membership test
- `FiniteSetSize(set)` - Cardinality
- `FiniteSetSubset(s1, s2)` - Subset test
- `FiniteSetMap(f, set)` - Map function over set
- `FiniteSetFilter(f, set)` - Filter set
- `FiniteSetRange(low, high)` - Create range [low..high]
- `is_finite_set(expr)` - Check if expression is a finite set
- `is_finite_set_sort(sort)` - Check if sort is a finite set sort

### Example

```python
from z3 import *

# Create a finite set sort over integers
int_set = FiniteSetSort(IntSort())

# Create sets
a = Const('a', int_set)
b = Const('b', int_set)
s1 = FiniteSetSingleton(IntVal(1))

# Use operators
union = a | b
intersect = a & b
diff = a - b

# Use with solver
solver = Solver()
solver.add(FiniteSetSize(a) == 2)
solver.add(FiniteSetMember(IntVal(1), a))
print(solver.check())
print(solver.model())
```

## C++ API

All functions are declared and implemented inline in `src/api/c++/z3++.h`:

### Context Methods

- `sort context::finite_set_sort(sort& s)` - Create finite set sort

### Free Functions

- `expr finite_set_empty(sort const& s)` - Create empty set
- `expr finite_set_singleton(expr const& e)` - Create singleton
- `expr finite_set_union(expr const& a, expr const& b)` - Union
- `expr finite_set_intersect(expr const& a, expr const& b)` - Intersection
- `expr finite_set_difference(expr const& a, expr const& b)` - Difference
- `expr finite_set_member(expr const& e, expr const& s)` - Membership
- `expr finite_set_size(expr const& s)` - Size
- `expr finite_set_subset(expr const& a, expr const& b)` - Subset
- `expr finite_set_map(expr const& f, expr const& s)` - Map
- `expr finite_set_filter(expr const& f, expr const& s)` - Filter
- `expr finite_set_range(expr const& low, expr const& high)` - Range

### Example

```cpp
#include <z3++.h>

z3::context c;
z3::sort int_sort = c.int_sort();
z3::sort fs_sort = c.finite_set_sort(int_sort);

z3::expr a = c.constant("a", fs_sort);
z3::expr b = c.constant("b", fs_sort);
z3::expr union_ab = finite_set_union(a, b);

z3::solver s(c);
s.add(finite_set_size(a) == 2);
std::cout << s.check() << std::endl;
```

## Other Language Bindings

The C#, Java, JavaScript, OCaml, and Julia bindings are auto-generated from the C API through 
the `scripts/update_api.py` script during the build process. The `def_API` macros in `z3_api.h`
provide the metadata needed for auto-generation.

## Implementation Details

- The finite set plugin is registered in `src/ast/reg_decl_plugins.cpp`
- The `finite_set_util` is added to the API context in `src/api/api_context.h`
- Core implementation is in `src/ast/finite_set_decl_plugin.h/cpp`

## SMT-LIB2 Syntax

The finite set operations map to SMT-LIB2 symbols:
- `set.empty` - empty set
- `set.singleton` - singleton set
- `set.union` - union
- `set.intersect` - intersection
- `set.difference` - difference
- `set.in` - membership
- `set.size` - cardinality
- `set.subset` - subset
- `set.map` - map operation
- `set.filter` - filter operation
- `set.range` - integer range
