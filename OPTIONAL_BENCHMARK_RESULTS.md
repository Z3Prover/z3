# std::optional vs Custom optional Benchmark Results

## Overview

This document summarizes the performance comparison between C++17's `std::optional` and Z3's custom `optional` implementation.

## Test Environment

- Platform: Linux x86_64
- Compiler: GCC with C++20 support
- Build Type: Release (optimized)
- Iterations: 1,000,000 for construction/copy/move, 10,000,000 for access operations

## Benchmark Results

### Memory Footprint

| Type | Custom optional | std::optional |
|------|----------------|---------------|
| `optional<int>` | 8 bytes | 8 bytes |
| `optional<BenchData>` (struct with 3 ints) | 8 bytes | 16 bytes |
| `optional<int*>` | 8 bytes | 16 bytes |

**Observation**: Custom optional uses pointer-based storage, always taking 8 bytes (pointer size) regardless of the contained type. `std::optional` uses in-place storage, resulting in `sizeof(T) + alignment_padding + 1_byte_flag`.

### Construction Performance

| Operation | Custom optional | std::optional | Ratio |
|-----------|----------------|---------------|-------|
| Default construction (int) | 0.34 ms | 0.35 ms | 0.96x |
| Value construction (int) | 14.66 ms | 0.35 ms | **42.11x** |
| Value construction (struct) | 13.93 ms | 0.60 ms | **23.04x** |

**Observation**: Default construction is roughly equal. However, value construction with custom optional is significantly slower due to heap allocation overhead.

### Copy Performance

| Operation | Custom optional | std::optional | Ratio |
|-----------|----------------|---------------|-------|
| Copy construction (int) | 14.30 ms | 0.57 ms | **24.94x** |
| Copy assignment (int) | 14.39 ms | 0.29 ms | **50.23x** |

**Observation**: Copy operations are 25-50x slower for custom optional due to heap allocation and pointer management.

### Move Performance

| Operation | Custom optional | std::optional | Ratio |
|-----------|----------------|---------------|-------|
| Move construction (int) | 13.72 ms | 0.32 ms | **43.48x** |
| Move assignment (int) | 13.86 ms | 5.76 ms | **2.41x** |

**Observation**: Move construction is significantly slower for custom optional. Move assignment shows less difference, but custom optional is still 2.4x slower.

### Access Performance

| Operation | Custom optional | std::optional | Ratio |
|-----------|----------------|---------------|-------|
| Dereference operator (int) | 21.60 ms | 21.62 ms | 1.00x |
| Arrow operator (struct) | 21.55 ms | 21.59 ms | 1.00x |
| Boolean conversion | 21.59 ms | 21.53 ms | 1.00x |

**Observation**: Once constructed, access performance is virtually identical. The pointer indirection in custom optional adds negligible overhead in practice.

## Analysis

### Custom optional (Heap-based)

**Advantages:**
1. **Smaller memory footprint** for large objects (always 8 bytes)
2. **Predictable size** regardless of contained type
3. **Can be used before C++17**

**Disadvantages:**
1. **Heap allocation overhead** on construction/copy/move (20-50x slower)
2. **Memory fragmentation** potential
3. **Cache unfriendly** - data is not co-located with the optional object
4. **Additional pointer indirection** (though minimal runtime impact)

### std::optional (Stack-based)

**Advantages:**
1. **No heap allocation** - extremely fast construction/copy/move
2. **Cache friendly** - data is co-located with the optional object
3. **Standard C++17 feature** - well-tested and widely supported
4. **No memory fragmentation**

**Disadvantages:**
1. **Larger memory footprint** for objects (size depends on contained type)
2. **Requires C++17 or later**

## Recommendations

Based on these benchmark results:

1. **For new code**: Use `std::optional` unless there's a specific requirement for the smaller memory footprint of the custom implementation.

2. **When to use custom optional**:
   - When targeting pre-C++17 compilers
   - When working with very large objects where the 8-byte overhead is significant
   - When optional objects are created rarely but accessed frequently

3. **When to use std::optional**:
   - For most modern C++17+ codebases
   - When construction/copy/move performance is critical
   - When working with small to medium-sized objects
   - When cache locality matters

## Running the Benchmark

To run the benchmark yourself:

```bash
cd build
./test-z3 optional_benchmark
```

The benchmark is integrated into Z3's test suite and will display detailed timing results for each operation category.

## Implementation Details

The benchmark is located in `src/test/optional_benchmark.cpp` and measures:
- Default construction
- Value construction (int and struct)
- Copy construction and assignment
- Move construction and assignment
- Dereference, arrow, and boolean conversion operators
- Memory footprint

The benchmark uses compiler barriers (`asm volatile`) to prevent optimizations from eliminating the measured operations.
