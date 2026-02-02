# Additional High-Priority Optimization Targets

## Overview

Beyond the primary target (euf::enode), here are other data structures worth investigating. Focusing on:
- Frequently instantiated (many copies)
- Accessed in hot paths
- NOT configuration structs (singletons)

## Ranking by Priority

### Priority 1: euf::enode (HIGHEST)
**Location**: `src/ast/euf/euf_enode.h`
**Issue**: 9 bool fields + 2 lbool fields scattered with padding
**Instance count**: Thousands to millions per SMT problem
**Hot path**: Yes - core equality reasoning structure
**Savings potential**: 86 bytes × instance count = **8-86 MB per typical problem**

### Priority 2: SAT Clause (Already Optimized)
**Location**: `src/sat/sat_clause.h`
**Status**: Already uses bitfields efficiently
**Note**: Good example of proper optimization

### Priority 3: Investigation Needed

The following have multiple bool fields but need investigation to determine:
1. How frequently are they instantiated?
2. Are they on hot paths?
3. Are they worth optimizing?

**Candidates for investigation:**

#### src/sat/smt/pb_constraint.h - constraint class
- 3 bool fields scattered
- Used in PB (pseudo-boolean) constraints
- Need to check: How many constraints in typical problems?

#### src/sat/smt/array_solver.h - var_data struct
- 2 bool fields
- Used per array variable
- Need to check: How many array variables in typical problems?

#### src/sat/sat_watched.h - watched class
- Already optimized with bit packing
- 2 bytes per watched literal
- Many instances but already efficient

## Investigation Strategy

For each candidate:

1. **Count instances** - Add instrumentation to count allocations
2. **Profile access** - Use profiler to see if on hot path
3. **Measure layout** - Check sizeof and field offsets
4. **Estimate savings** - Calculate potential memory reduction

Example instrumentation:
```cpp
static std::atomic<size_t> instance_count{0};
MyStruct() { instance_count++; }
~MyStruct() { instance_count--; }
static void report() { 
    std::cout << "MyStruct instances: " << instance_count << "\n"; 
}
```

## Focus Recommendation

**Start with euf::enode** - It's clearly the highest value target:
- Definitely many instances (one per term)
- Definitely on hot path (equality reasoning)
- Clear optimization opportunity (86 bytes per instance)
- No reference access issues (can use bitfields)

After enode is optimized and measured, investigate others based on profiling data.

## Avoid

Do NOT optimize:
- Config structs (sat::config, theory_bv_params, etc.) - already confirmed no impact
- Singleton classes (solver, context, etc.) - only one instance
- Classes with few instances (< 100 per typical problem)

## Measurement Approach

For any optimization:
1. Measure sizeof before and after
2. Count instances in real problems
3. Calculate theoretical savings
4. Profile to ensure no performance regression
5. Test on SMT-LIB benchmarks
6. Report actual memory reduction

Only claim benefits that can be measured, not guessed.
