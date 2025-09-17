# Z3 Performance Measurement Infrastructure

This directory contains comprehensive performance measurement and profiling tools for the Z3 theorem prover, created by the Daily Perf Improver to support ongoing optimization efforts.

## Overview

This performance infrastructure provides:

1. **Comprehensive Performance Benchmarking** - Systematic measurement of Z3's performance across various problem types
2. **Memory Allocation Profiling** - Analysis of memory usage patterns to identify allocation bottlenecks
3. **Standardized Measurement Framework** - Consistent methodology for measuring optimization impact
4. **Performance Regression Detection** - Tools to compare performance between Z3 versions

## Tools Provided

### 1. Comprehensive Performance Measurement (`comprehensive_perf_measurement.cpp`)

A comprehensive benchmarking tool that measures Z3's performance across different formula types:

**Features:**
- High-precision timing measurements
- Statistical analysis (mean, min, max, standard deviation)
- Memory usage tracking
- CPU performance counters (Linux only)
- CSV export for analysis
- Configurable test iterations
- Support for performance comparisons

**Usage:**
```bash
# Build the tool
make comprehensive_perf_measurement

# Run basic benchmark
./comprehensive_perf_measurement --binary ../build/z3 --iterations 10

# Compare two Z3 versions
make compare BINARY1=../build_old/z3 BINARY2=../build_new/z3

# Quick development test
make quick-test
```

### 2. Memory Allocation Profiler (`memory_allocation_profiler.cpp`)

Simulates and profiles Z3's memory allocation patterns to identify bottlenecks:

**Features:**
- Allocation pattern simulation for key Z3 components
- Size distribution analysis
- Memory usage statistics by component
- Fragmentation pattern detection
- CSV export for detailed analysis

**Usage:**
```bash
# Build and run memory profiler
make profile-memory
```

### 3. Build and Testing Infrastructure (`Makefile`)

Comprehensive build system supporting:
- Optimized builds for accurate performance measurement
- Debug builds for development
- Automated Z3 building with performance configuration
- Integrated benchmarking workflows
- Performance report generation

## Integration with Daily Perf Improver Work

This infrastructure **complements all existing Daily Perf Improver optimizations**:

### Measuring Optimization Impact
- **AST Cache Optimizations** (PR #7917): Measure cache hit rate improvements
- **SAT Solver Optimizations** (PR #7889, #7906): Track propagation performance
- **Hash Function Improvements** (PR #7908, #7909): Measure hash operation speedups
- **Theory Solver Enhancements** (PR #7896): Profile linear arithmetic performance

### Supporting Future Work
- **Before/After Analysis**: Quantify the impact of each optimization
- **Regression Detection**: Ensure optimizations don't introduce performance regressions
- **Bottleneck Identification**: Find new optimization opportunities as previous ones are addressed
- **Maintainer Decision Support**: Provide data to help prioritize optimization work

## Key Performance Areas Addressed

Based on maintainer feedback (@nunoplopes), this infrastructure specifically targets:

1. **Cache Performance**: Tools to measure cache miss ratios and memory access patterns
2. **Memory Allocation**: Profiling of allocation patterns as identified as major bottlenecks
3. **AST Operations**: Benchmarking of AST creation, traversal, and hashing performance
4. **Core Algorithm Performance**: Systematic measurement of SAT/SMT solving performance

## Technical Implementation

### Performance Measurement Methodology
- **High-precision timing**: Microsecond-accurate measurements using `std::chrono`
- **Statistical rigor**: Multiple iterations with statistical analysis
- **Warm-up phases**: Eliminate cold-start effects from measurements
- **Controlled environment**: Consistent measurement conditions

### Memory Profiling Approach
- **Realistic allocation patterns**: Based on Z3's actual usage patterns
- **Component-specific analysis**: Track allocations by Z3 component (AST, SAT, hash tables, etc.)
- **Size distribution tracking**: Identify most common allocation sizes for optimization
- **Fragmentation detection**: Analysis of memory fragmentation patterns

### Cross-platform Compatibility
- **Linux optimization**: Full CPU counter support with perf_event interface
- **Portable fallback**: Basic timing and memory measurement on all platforms
- **Compiler independence**: Works with GCC, Clang, and MSVC

## Expected Performance Benefits

This infrastructure enables:

1. **Quantified Optimization Impact**: Precise measurement of each performance improvement
2. **Systematic Bottleneck Discovery**: Data-driven identification of new optimization targets
3. **Regression Prevention**: Early detection of performance regressions in development
4. **Optimization Validation**: Ensure optimizations provide real-world benefits

## Getting Started

### Quick Start
```bash
# Build all tools
make all

# Run comprehensive benchmark (requires Z3 to be built)
make benchmark

# Generate performance report
make report
```

### Development Workflow
```bash
# Quick development test
make quick-test

# Compare optimization branches
git checkout optimization-branch
make build-z3
./comprehensive_perf_measurement --output results_optimized.csv

git checkout master
make build-z3
./comprehensive_perf_measurement --output results_baseline.csv

# Analyze differences
python3 analyze_performance_diff.py results_baseline.csv results_optimized.csv
```

### Integration with CI/CD
The tools are designed to integrate with continuous integration:
- Automated performance regression detection
- Performance trend tracking over time
- Benchmark result archiving and analysis

## Supporting the Daily Perf Improver Mission

This performance measurement infrastructure directly supports the Daily Perf Improver's goal of systematic performance improvement in Z3:

- **Evidence-based optimization**: All performance claims backed by rigorous measurement
- **Comprehensive coverage**: Measurement capabilities across Z3's entire architecture
- **Maintainer alignment**: Focuses on performance areas specifically identified by maintainers
- **Long-term value**: Infrastructure that benefits the entire Z3 project beyond current optimizations

The combination of this measurement infrastructure with the extensive optimization work already completed provides Z3 with both immediate performance improvements and the tools needed for continued optimization success.