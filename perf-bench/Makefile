# Makefile for Z3 Performance Measurement Tools
# Daily Perf Improver - Performance Infrastructure

CXX = g++
CXXFLAGS = -std=c++17 -O2 -DNDEBUG -Wall -Wextra
DEBUG_FLAGS = -g -O0 -DDEBUG

# Default build is optimized for performance measurement
all: comprehensive_perf_measurement memory_allocation_profiler

# Optimized builds for production performance testing
comprehensive_perf_measurement: comprehensive_perf_measurement.cpp
	$(CXX) $(CXXFLAGS) -o $@ $< -pthread

memory_allocation_profiler: memory_allocation_profiler.cpp
	$(CXX) $(CXXFLAGS) -o $@ $<

# Debug builds for development
debug: comprehensive_perf_measurement_debug memory_allocation_profiler_debug

comprehensive_perf_measurement_debug: comprehensive_perf_measurement.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG_FLAGS) -o comprehensive_perf_measurement_debug $< -pthread

memory_allocation_profiler_debug: memory_allocation_profiler.cpp
	$(CXX) $(CXXFLAGS) $(DEBUG_FLAGS) -o memory_allocation_profiler_debug $<

# Build Z3 with performance configuration
build-z3:
	@echo "Building Z3 with performance configuration..."
	@if [ ! -d ../build ]; then mkdir -p ../build; fi
	@cd ../build && cmake -G "Ninja" \
		-DCMAKE_BUILD_TYPE=RelWithDebInfo \
		-DZ3_ENABLE_TRACING_FOR_NON_DEBUG=TRUE \
		-DZ3_BUILD_LIBZ3_SHARED=FALSE \
		-DZ3_BUILD_TEST_EXECUTABLES=TRUE \
		-DCMAKE_CXX_FLAGS="-fno-omit-frame-pointer -march=native" \
		..
	@cd ../build && ninja z3

# Run comprehensive performance tests
test: all build-z3
	@echo "Running comprehensive performance measurement..."
	./comprehensive_perf_measurement --binary ../build/z3 --iterations 5 --output results_$(shell date +%Y%m%d_%H%M%S).csv --verbose

# Run memory allocation profiling
profile-memory: memory_allocation_profiler
	@echo "Running memory allocation profiler..."
	./memory_allocation_profiler

# Run both tests and generate reports
benchmark: test profile-memory
	@echo "Benchmarking completed. Results in CSV files."

# Quick test with fewer iterations for development
quick-test: all
	@if [ -f ../build/z3 ]; then \
		echo "Running quick performance test..."; \
		./comprehensive_perf_measurement --binary ../build/z3 --iterations 3 --output quick_results.csv; \
	else \
		echo "Z3 binary not found. Run 'make build-z3' first."; \
	fi

# Performance comparison between two Z3 binaries
compare: all
	@if [ -z "$(BINARY1)" ] || [ -z "$(BINARY2)" ]; then \
		echo "Usage: make compare BINARY1=path/to/z3_old BINARY2=path/to/z3_new"; \
		exit 1; \
	fi
	@echo "Comparing performance between $(BINARY1) and $(BINARY2)..."
	./comprehensive_perf_measurement --binary $(BINARY1) --iterations 5 --output comparison_baseline.csv
	./comprehensive_perf_measurement --binary $(BINARY2) --iterations 5 --output comparison_optimized.csv
	@echo "Results in comparison_baseline.csv and comparison_optimized.csv"

# Generate performance report
report:
	@echo "Generating performance analysis report..."
	@python3 -c "
import csv
import sys
try:
    with open('z3_perf_results.csv', 'r') as f:
        reader = csv.DictReader(f)
        data = list(reader)
    print('=== Z3 Performance Report ===')
    total_time = sum(float(row['avg_time_ms']) for row in data)
    print(f'Total benchmark time: {total_time:.2f} ms')
    print(f'Number of tests: {len(data)}')
    print(f'Average per test: {total_time/len(data):.2f} ms')
    print('\\nSlowest tests:')
    sorted_data = sorted(data, key=lambda x: float(x['avg_time_ms']), reverse=True)
    for i, row in enumerate(sorted_data[:5]):
        print(f'{i+1}. {row[\"test_name\"]}: {row[\"avg_time_ms\"]} ms')
    print('\\nMemory usage patterns:')
    avg_rss = sum(float(row['current_rss_kb']) for row in data) / len(data)
    max_rss = max(float(row['peak_rss_kb']) for row in data)
    print(f'Average RSS: {avg_rss:.1f} KB')
    print(f'Peak RSS: {max_rss:.1f} KB')
except FileNotFoundError:
    print('No results file found. Run benchmark first.')
except Exception as e:
    print(f'Error generating report: {e}')
"

# Install system dependencies for performance monitoring (Linux only)
install-deps:
	@echo "Installing performance monitoring dependencies..."
	@if which apt-get >/dev/null 2>&1; then \
		sudo apt-get update && sudo apt-get install -y linux-tools-common linux-tools-generic valgrind; \
	elif which yum >/dev/null 2>&1; then \
		sudo yum install -y perf valgrind; \
	else \
		echo "Please install perf and valgrind manually for your distribution"; \
	fi

# Clean build artifacts
clean:
	rm -f comprehensive_perf_measurement memory_allocation_profiler
	rm -f comprehensive_perf_measurement_debug memory_allocation_profiler_debug
	rm -f *.csv
	rm -f /tmp/z3_perf_test.smt2

# Help message
help:
	@echo "Z3 Performance Measurement Tools"
	@echo ""
	@echo "Targets:"
	@echo "  all              - Build all profiling tools"
	@echo "  debug            - Build debug versions"
	@echo "  build-z3         - Build Z3 with performance configuration"
	@echo "  test             - Run comprehensive performance tests"
	@echo "  profile-memory   - Run memory allocation profiler"
	@echo "  benchmark        - Run all benchmarks and profiling"
	@echo "  quick-test       - Quick test with fewer iterations"
	@echo "  compare          - Compare two Z3 binaries (use BINARY1=... BINARY2=...)"
	@echo "  report           - Generate performance analysis report"
	@echo "  install-deps     - Install system performance monitoring tools"
	@echo "  clean            - Clean build artifacts"
	@echo "  help             - Show this help message"
	@echo ""
	@echo "Example usage:"
	@echo "  make benchmark                    # Run complete performance suite"
	@echo "  make quick-test                  # Quick development test"
	@echo "  make compare BINARY1=old_z3 BINARY2=new_z3  # Compare performance"

.PHONY: all debug build-z3 test profile-memory benchmark quick-test compare report install-deps clean help