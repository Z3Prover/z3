# UserPropagator Quantifier Instantiation Callback in Z3

This document describes the UserPropagator callback for quantifier instantiations feature added in Z3 version 4.15.3.

## Overview

The quantifier instantiation callback allows user propagators to intercept and control quantifier instantiations. When Z3 attempts to instantiate a quantifier, the callback is invoked with the quantifier and its proposed instantiation. The callback can return `false` to discard the instantiation, providing fine-grained control over the quantifier instantiation process.

This feature enables:
1. **Inspection and logging** of instantiation patterns
2. **Filtering** of undesired instantiations
3. **Custom instantiation strategies**
4. **Performance optimization** by delaying certain instantiations

## API Reference

### Python API

```python
from z3 import *

class MyUserPropagator(UserPropagateBase):
    def __init__(self, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)
        # Register the quantifier instantiation callback
        self.add_on_binding(self.my_callback)
    
    def my_callback(self, quantifier, instantiation):
        """
        Callback for quantifier instantiation control.
        
        Args:
            quantifier: The quantifier being instantiated (Z3 AST)
            instantiation: The proposed instantiation (Z3 AST)
            
        Returns:
            bool: True to allow the instantiation, False to discard it
        """
        # Your logic here
        return True  # or False to block
    
    # Required methods
    def push(self): pass
    def pop(self, num_scopes): pass  
    def fresh(self, new_ctx): return MyUserPropagator(ctx=new_ctx)
```

### C API

```c
#include <z3.h>

// Callback function signature
Z3_bool my_callback(void* ctx, Z3_solver_callback cb, Z3_ast q, Z3_ast inst) {
    // ctx: user context data
    // cb: solver callback handle (internal use)
    // q: quantifier being instantiated
    // inst: proposed instantiation
    
    // Your logic here
    return Z3_TRUE;  // or Z3_FALSE to block
}

// Register the callback
Z3_context ctx = Z3_mk_context(Z3_mk_config());
Z3_solver s = Z3_mk_solver(ctx);
Z3_solver_propagate_on_binding(ctx, s, my_callback);
```

### C++ API

The C++ API follows the same pattern as the C API, using the same `Z3_solver_propagate_on_binding` function.

## Examples

### Basic Example: Limiting Instantiations

```python
class InstantiationLimiter(UserPropagateBase):
    def __init__(self, max_instantiations=5, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)
        self.max_instantiations = max_instantiations
        self.count = 0
        self.add_on_binding(self.limit_instantiations)
    
    def limit_instantiations(self, quantifier, instantiation):
        self.count += 1
        print(f"Instantiation #{self.count}: {instantiation}")
        
        # Allow only the first max_instantiations
        if self.count <= self.max_instantiations:
            print("  -> ALLOWED")
            return True
        else:
            print("  -> BLOCKED")
            return False
    
    def push(self): pass
    def pop(self, num_scopes): pass
    def fresh(self, new_ctx): return InstantiationLimiter(self.max_instantiations, ctx=new_ctx)

# Usage
s = Solver()
limiter = InstantiationLimiter(max_instantiations=3, s=s)

x = Int('x')
f = Function('f', IntSort(), IntSort())
s.add(ForAll([x], f(x) >= 0))
s.add(f(1) < 10, f(2) < 20, f(3) < 30)

result = s.check()
```

### Advanced Example: Pattern-Based Filtering

```python
class PatternFilter(UserPropagateBase):
    def __init__(self, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)
        self.pattern_counts = {}
        self.max_per_pattern = 2
        self.add_on_binding(self.filter_by_pattern)
    
    def filter_by_pattern(self, quantifier, instantiation):
        # Convert to string for pattern matching
        pattern = str(instantiation)
        
        # Count occurrences of this pattern
        self.pattern_counts[pattern] = self.pattern_counts.get(pattern, 0) + 1
        count = self.pattern_counts[pattern]
        
        # Allow only max_per_pattern instantiations of each pattern
        allow = count <= self.max_per_pattern
        
        print(f"Pattern: {pattern} (#{count}) -> {'ALLOWED' if allow else 'BLOCKED'}")
        return allow
    
    def push(self): pass
    def pop(self, num_scopes): pass
    def fresh(self, new_ctx): return PatternFilter(ctx=new_ctx)
```

### Logging Example: Analyzing Instantiation Patterns

```python
class InstantiationLogger(UserPropagateBase):
    def __init__(self, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)
        self.log = []
        self.add_on_binding(self.log_instantiation)
    
    def log_instantiation(self, quantifier, instantiation):
        entry = {
            'quantifier': str(quantifier),
            'instantiation': str(instantiation),
            'count': len(self.log) + 1
        }
        self.log.append(entry)
        
        print(f"#{entry['count']}: {entry['instantiation']}")
        
        # Allow all instantiations (just log them)
        return True
    
    def get_statistics(self):
        # Group by quantifier
        by_quantifier = {}
        for entry in self.log:
            q = entry['quantifier']
            if q not in by_quantifier:
                by_quantifier[q] = []
            by_quantifier[q].append(entry['instantiation'])
        
        return {
            'total': len(self.log),
            'by_quantifier': by_quantifier
        }
    
    def push(self): pass
    def pop(self, num_scopes): pass
    def fresh(self, new_ctx): return InstantiationLogger(ctx=new_ctx)
```

## Use Cases

### 1. Performance Optimization
- **Problem**: Some quantifier instantiations are expensive but rarely useful
- **Solution**: Use callback to block certain patterns or limit instantiation count
- **Benefit**: Reduced solving time, better resource utilization

### 2. Custom Instantiation Strategies
- **Problem**: Default instantiation heuristics don't work well for your domain
- **Solution**: Implement domain-specific filtering logic
- **Benefit**: Better solution quality, faster convergence

### 3. Debugging and Analysis
- **Problem**: Understanding why a formula is UNSAT or takes long to solve
- **Solution**: Log all instantiation attempts to analyze patterns
- **Benefit**: Better insight into solver behavior

### 4. Interactive Solving
- **Problem**: Need to control solving process interactively
- **Solution**: Use callback to selectively enable/disable instantiations
- **Benefit**: Fine-grained control over solver behavior

## Technical Details

### Callback Invocation
- Called **before** the instantiation is added to the solver
- Blocking an instantiation prevents it from being used in the current search
- The same instantiation may be proposed again in different search branches

### Return Value Semantics
- `True` (Python) / `Z3_TRUE` (C): Allow the instantiation
- `False` (Python) / `Z3_FALSE` (C): Block the instantiation
- Blocked instantiations are discarded and won't be used in current search

### Thread Safety
- Callbacks are invoked on the same thread as the solver
- No additional synchronization is needed
- Context switching during callback execution is safe

### Performance Considerations
- Callbacks are invoked frequently during solving
- Keep callback logic lightweight to avoid performance overhead
- String conversions (`str(ast)`) can be expensive; cache when possible
- Consider using AST structure inspection instead of string matching

## Limitations

### C/C++ API Limitations
- The C/C++ callback receives AST handles but no direct Z3 context
- Converting ASTs to strings for inspection requires careful context management
- Recommend using Python API for complex logic, C/C++ for simple filtering

### Scope and Lifetime
- Callback registrations are tied to solver instances
- User propagator instances must remain alive during solving
- AST handles in callbacks are valid only during callback execution

### Interaction with Other Features
- Works with all quantifier instantiation strategies (E-matching, MBQI, etc.)
- Compatible with other user propagator callbacks
- May affect solver completeness if too many instantiations are blocked

## Best Practices

1. **Start Simple**: Begin with logging to understand instantiation patterns
2. **Be Conservative**: Blocking too many instantiations can make formulas unsolvable
3. **Test Thoroughly**: Verify that your filtering doesn't break correctness
4. **Profile Performance**: Measure impact of callback overhead
5. **Use Appropriate Data Structures**: Hash maps for pattern counting, etc.
6. **Handle Edge Cases**: Empty instantiations, malformed ASTs, etc.

## Complete Working Example

See the accompanying files:
- `examples/python/quantifier_instantiation_callback.py` - Complete Python examples
- `examples/c++/quantifier_instantiation_callback.cpp` - C++ examples  
- `examples/c/quantifier_instantiation_callback.c` - C examples

These examples demonstrate all the concepts above with runnable code.

## Troubleshooting

### Common Issues

1. **Callback Not Called**
   - Ensure user propagator is properly registered with solver
   - Check that problem actually triggers quantifier instantiations
   - Verify quantifier syntax is correct

2. **Performance Degradation**
   - Simplify callback logic
   - Avoid expensive string operations
   - Consider sampling (only process every Nth callback)

3. **Unexpected UNSAT Results**
   - Review blocking criteria - may be too aggressive
   - Test with callback disabled to verify baseline behavior
   - Use logging to understand what's being blocked

4. **Memory Issues**
   - Don't store AST handles beyond callback lifetime
   - Clear large data structures periodically
   - Monitor memory usage in long-running processes

## Version History

- **Z3 4.15.3**: Initial implementation of quantifier instantiation callbacks
- **Z3 4.15.4**: Improved performance and stability

For more information, see the Z3 documentation and source code in the Z3Prover repository.