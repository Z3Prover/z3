#!/bin/bash
# Actual cache performance measurement script
# This measures real cache behavior using perf

set -e

echo "============================================================"
echo "Z3 Struct Packing - ACTUAL Cache Performance Measurement"
echo "============================================================"
echo ""

# Check if perf is available
if ! command -v perf &> /dev/null; then
    echo "ERROR: 'perf' command not available."
    echo "Install with: sudo apt-get install linux-tools-common linux-tools-generic"
    echo ""
    echo "Alternative: Running without perf..."
    USE_PERF=0
else
    echo "✓ perf command available"
    USE_PERF=1
fi

echo ""

# Find SMT2 benchmarks
SMT2_FILES=$(find /home/runner/work/z3/z3/examples -name "*.smt2" 2>/dev/null | head -5)

if [ -z "$SMT2_FILES" ]; then
    echo "No SMT2 benchmark files found."
    exit 1
fi

echo "Found benchmark files:"
echo "$SMT2_FILES" | while read f; do echo "  - $f"; done
echo ""

Z3_BIN="/home/runner/work/z3/z3/build/z3-optimized"

if [ ! -f "$Z3_BIN" ]; then
    echo "ERROR: Z3 binary not found at $Z3_BIN"
    exit 1
fi

echo "Testing Z3 binary: $Z3_BIN"
echo "============================================================"
echo ""

# Warm up
echo "Warming up cache..."
echo "$SMT2_FILES" | head -1 | while read BENCH; do
    $Z3_BIN "$BENCH" > /dev/null 2>&1 || true
done
echo ""

# Run benchmarks with perf
if [ $USE_PERF -eq 1 ]; then
    echo "Running with perf to measure cache performance..."
    echo "------------------------------------------------------------"
    
    echo "$SMT2_FILES" | while read BENCH; do
        BENCH_NAME=$(basename "$BENCH")
        echo ""
        echo "Benchmark: $BENCH_NAME"
        echo "Command: perf stat -e cache-references,cache-misses,instructions,cycles $Z3_BIN $BENCH"
        
        # Run with perf stat
        perf stat -e cache-references,cache-misses,instructions,cycles \
            $Z3_BIN "$BENCH" > /dev/null 2>&1 || true
            
        echo "------------------------------------------------------------"
    done
else
    echo "Running WITHOUT perf (basic timing only)..."
    echo "------------------------------------------------------------"
    
    echo "$SMT2_FILES" | while read BENCH; do
        BENCH_NAME=$(basename "$BENCH")
        echo ""
        echo "Benchmark: $BENCH_NAME"
        
        # Run with time
        /usr/bin/time -v $Z3_BIN "$BENCH" 2>&1 | grep -E "(User time|Maximum resident|Page faults)"
        
        echo "------------------------------------------------------------"
    done
fi

echo ""
echo "============================================================"
echo "Measurement Complete"
echo "============================================================"
echo ""
echo "IMPORTANT NOTES:"
echo "----------------"
echo ""
echo "1. This measures the OPTIMIZED version only"
echo "   - To compare, we need a baseline (unoptimized) version"
echo "   - Cannot create baseline without reverting struct changes"
echo ""
echo "2. Single instance issue:"
echo "   - As user noted: typically only ONE instance of these structs"
echo "   - Memory savings: minimal (92 bytes total)"
echo "   - Cache impact: depends on access patterns"
echo ""
echo "3. Cache hit rate impact:"
echo "   - Would need BOTH versions to compare"
echo "   - Should measure: cache-misses / cache-references"
echo "   - Lower ratio = better cache performance"
echo ""
echo "4. Realistic assessment:"
echo "   - For single instance: impact likely < 0.1%"
echo "   - 92 bytes = ~1.4 cache lines (64 bytes each)"
echo "   - Unless these structs are on critical hot path"
echo "   - Actual benefit may be negligible"
echo ""
echo "RECOMMENDATION:"
echo "---------------"
echo "Given that there's typically only ONE instance of each struct,"
echo "the performance impact is likely NEGLIGIBLE unless:"
echo "  a) These structs are accessed in a tight loop"
echo "  b) They're on a critical hot path"
echo "  c) Other data competes for the same cache lines"
echo ""
echo "Without comparative measurements, we CANNOT claim performance"
echo "improvement. The change is primarily a code quality improvement."
echo ""
