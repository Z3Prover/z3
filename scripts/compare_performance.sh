#!/bin/bash
# Compare performance between baseline and optimized Z3 versions
# Measures ACTUAL runtime and peak memory usage

set -e

Z3_DIR="/home/runner/work/z3/z3"
BENCH_DIR="$Z3_DIR/benchmarks"
BUILD_DIR="$Z3_DIR/build"
RESULTS_DIR="$Z3_DIR/benchmark_results"

mkdir -p "$RESULTS_DIR"

echo "============================================================"
echo "Z3 Performance Comparison: Baseline vs Optimized"
echo "============================================================"
echo ""
echo "This script will:"
echo "  1. Build baseline Z3 (unoptimized struct layout)"
echo "  2. Build optimized Z3 (optimized struct layout)"
echo "  3. Run benchmarks on both versions"
echo "  4. Measure runtime and peak memory (RSS)"
echo "  5. Compare results"
echo ""

# Function to build Z3
build_z3() {
    local version=$1
    echo "------------------------------------------------------------"
    echo "Building Z3 ($version version)..."
    echo "------------------------------------------------------------"
    
    cd "$Z3_DIR"
    
    # Copy appropriate header files
    if [ "$version" = "baseline" ]; then
        cp src/sat/sat_config.h.baseline src/sat/sat_config.h
        cp src/params/theory_bv_params.h.baseline src/params/theory_bv_params.h
    else
        cp src/sat/sat_config.h.optimized src/sat/sat_config.h
        cp src/params/theory_bv_params.h.optimized src/params/theory_bv_params.h
    fi
    
    # Clean and rebuild
    rm -rf build
    python scripts/mk_make.py > /dev/null 2>&1
    cd build
    
    echo "Compiling... (this takes ~10-15 minutes)"
    make z3 -j$(nproc) > /dev/null 2>&1
    
    if [ ! -f z3 ]; then
        echo "ERROR: Build failed for $version version"
        exit 1
    fi
    
    # Copy binary
    cp z3 "$RESULTS_DIR/z3-$version"
    echo "✓ Build complete: z3-$version"
    
    # Show struct sizes
    echo ""
    echo "Struct sizes ($version):"
    echo "#include <iostream>" > /tmp/test_size.cpp
    echo "#include \"$Z3_DIR/src/sat/sat_config.h\"" >> /tmp/test_size.cpp
    echo "#include \"$Z3_DIR/src/params/theory_bv_params.h\"" >> /tmp/test_size.cpp
    echo "int main() {" >> /tmp/test_size.cpp
    echo "  std::cout << \"sat::config: \" << sizeof(sat::config) << \" bytes\\n\";" >> /tmp/test_size.cpp
    echo "  std::cout << \"theory_bv_params: \" << sizeof(theory_bv_params) << \" bytes\\n\";" >> /tmp/test_size.cpp
    echo "  return 0;" >> /tmp/test_size.cpp
    echo "}" >> /tmp/test_size.cpp
    
    g++ -std=c++20 -I"$Z3_DIR/src" -I"$Z3_DIR/build" /tmp/test_size.cpp -o /tmp/test_size 2>/dev/null || echo "  (size check skipped)"
    /tmp/test_size 2>/dev/null || echo "  (size check skipped)"
    echo ""
}

# Function to run benchmark
run_benchmark() {
    local z3_bin=$1
    local bench_file=$2
    local output_file=$3
    
    # Run with timeout and memory measurement
    /usr/bin/time -v timeout 10s "$z3_bin" "$bench_file" > /dev/null 2> "$output_file" || true
}

# Function to extract metrics
extract_metrics() {
    local time_output=$1
    local runtime=$(grep "User time" "$time_output" | awk '{print $4}' || echo "0")
    local memory=$(grep "Maximum resident set size" "$time_output" | awk '{print $6}' || echo "0")
    echo "$runtime $memory"
}

# Build both versions
build_z3 "baseline"
build_z3 "optimized"

echo ""
echo "============================================================"
echo "Running Benchmarks"
echo "============================================================"
echo ""

# Run benchmarks
BENCHMARKS=$(ls "$BENCH_DIR"/*.smt2)

echo "Benchmark results:" > "$RESULTS_DIR/results.txt"
echo "" >> "$RESULTS_DIR/results.txt"
printf "%-25s %15s %15s %15s %15s\n" "Benchmark" "Base Time(s)" "Opt Time(s)" "Base Mem(KB)" "Opt Mem(KB)" | tee -a "$RESULTS_DIR/results.txt"
printf "%-25s %15s %15s %15s %15s\n" "-------------------------" "---------------" "---------------" "---------------" "---------------" | tee -a "$RESULTS_DIR/results.txt"

for bench in $BENCHMARKS; do
    bench_name=$(basename "$bench")
    
    # Run baseline
    run_benchmark "$RESULTS_DIR/z3-baseline" "$bench" "$RESULTS_DIR/baseline_${bench_name}.time"
    baseline_metrics=$(extract_metrics "$RESULTS_DIR/baseline_${bench_name}.time")
    baseline_time=$(echo $baseline_metrics | awk '{print $1}')
    baseline_mem=$(echo $baseline_metrics | awk '{print $2}')
    
    # Run optimized
    run_benchmark "$RESULTS_DIR/z3-optimized" "$bench" "$RESULTS_DIR/optimized_${bench_name}.time"
    optimized_metrics=$(extract_metrics "$RESULTS_DIR/optimized_${bench_name}.time")
    optimized_time=$(echo $optimized_metrics | awk '{print $1}')
    optimized_mem=$(echo $optimized_metrics | awk '{print $2}')
    
    printf "%-25s %15s %15s %15s %15s\n" "$bench_name" "$baseline_time" "$optimized_time" "$baseline_mem" "$optimized_mem" | tee -a "$RESULTS_DIR/results.txt"
done

echo "" | tee -a "$RESULTS_DIR/results.txt"
echo "============================================================" | tee -a "$RESULTS_DIR/results.txt"
echo "Summary" | tee -a "$RESULTS_DIR/results.txt"
echo "============================================================" | tee -a "$RESULTS_DIR/results.txt"
echo "" | tee -a "$RESULTS_DIR/results.txt"
echo "Results saved to: $RESULTS_DIR/results.txt" | tee -a "$RESULTS_DIR/results.txt"
echo "" | tee -a "$RESULTS_DIR/results.txt"
echo "CONCLUSION:" | tee -a "$RESULTS_DIR/results.txt"
echo "These are ACTUAL measurements comparing baseline vs optimized." | tee -a "$RESULTS_DIR/results.txt"
echo "Any difference < 5% is likely within measurement noise." | tee -a "$RESULTS_DIR/results.txt"
echo "" | tee -a "$RESULTS_DIR/results.txt"

# Restore optimized versions
cd "$Z3_DIR"
cp src/sat/sat_config.h.optimized src/sat/sat_config.h
cp src/params/theory_bv_params.h.optimized src/params/theory_bv_params.h

echo "Binaries available at:"
echo "  $RESULTS_DIR/z3-baseline"
echo "  $RESULTS_DIR/z3-optimized"
