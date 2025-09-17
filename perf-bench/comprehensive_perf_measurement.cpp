/*++
Performance measurement infrastructure for Z3
Simplified version for testing core functionality
--*/

#include <iostream>
#include <chrono>
#include <vector>
#include <string>
#include <fstream>
#include <cstdlib>
#include <algorithm>
#include <iomanip>
#include <cmath>
#include <unistd.h>

class PerfTimer {
private:
    std::chrono::high_resolution_clock::time_point start_time;

public:
    void start() {
        start_time = std::chrono::high_resolution_clock::now();
    }

    double elapsed_ms() const {
        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time);
        return duration.count() / 1000.0;
    }
};

class Z3PerformanceSuite {
private:
    std::vector<std::string> test_formulas;
    std::string z3_binary_path;

    void generate_test_formulas() {
        test_formulas = {
            "(assert (and (> x 0) (< x 10)))",
            "(assert (or (= a true) (= b false)))",
            "(assert (and (> x 1) (< x 100) (= (* x x) 49)))",
            "(assert (= (bvadd #b1010 #b0101) #b1111))",
            "(assert (forall ((x Int)) (=> (> x 0) (> (* x 2) x))))"
        };
    }

    double run_z3_formula(const std::string& formula) {
        std::string temp_file = "/tmp/z3_perf_test.smt2";
        std::ofstream file(temp_file);
        file << "(set-logic ALL)\n";
        file << "(declare-const x Int)\n";
        file << "(declare-const a Bool)\n";
        file << "(declare-const b Bool)\n";
        file << formula << "\n";
        file << "(check-sat)\n";
        file.close();

        PerfTimer timer;
        timer.start();

        std::string command = z3_binary_path + " " + temp_file + " > /dev/null 2>&1";
        int result = system(command.c_str());
        (void)result;

        double elapsed = timer.elapsed_ms();
        unlink(temp_file.c_str());
        return elapsed;
    }

public:
    Z3PerformanceSuite(const std::string& z3_binary = "build/z3")
        : z3_binary_path(z3_binary) {
        generate_test_formulas();
    }

    struct BenchmarkResult {
        std::string test_name;
        double avg_time_ms;
        double min_time_ms;
        double max_time_ms;
        double stddev_ms;
    };

    std::vector<BenchmarkResult> run_benchmark(int iterations = 5) {
        std::vector<BenchmarkResult> results;

        std::cout << "=== Z3 Performance Benchmark ===" << std::endl;
        std::cout << "Running " << iterations << " iterations per test..." << std::endl;
        std::cout << "Z3 binary: " << z3_binary_path << std::endl << std::endl;

        for (size_t i = 0; i < test_formulas.size(); i++) {
            const std::string& formula = test_formulas[i];
            std::string test_name = "formula_" + std::to_string(i + 1);

            std::vector<double> times;
            std::cout << "Running " << test_name << "..." << std::flush;

            // Warm-up run
            run_z3_formula(formula);

            // Actual benchmark runs
            for (int iter = 0; iter < iterations; iter++) {
                double time = run_z3_formula(formula);
                times.push_back(time);
            }

            // Calculate statistics
            double sum = 0.0;
            double min_time = times[0];
            double max_time = times[0];

            for (double time : times) {
                sum += time;
                min_time = std::min(min_time, time);
                max_time = std::max(max_time, time);
            }

            double avg_time = sum / times.size();
            double variance = 0.0;
            for (double time : times) {
                variance += (time - avg_time) * (time - avg_time);
            }
            double stddev = std::sqrt(variance / times.size());

            BenchmarkResult result;
            result.test_name = test_name;
            result.avg_time_ms = avg_time;
            result.min_time_ms = min_time;
            result.max_time_ms = max_time;
            result.stddev_ms = stddev;

            results.push_back(result);
            std::cout << " " << avg_time << "ms ± " << stddev << "ms" << std::endl;
        }

        return results;
    }

    void export_csv(const std::vector<BenchmarkResult>& results, const std::string& filename) {
        std::ofstream file(filename);
        file << "test_name,avg_time_ms,min_time_ms,max_time_ms,stddev_ms" << std::endl;

        for (const auto& result : results) {
            file << result.test_name << ","
                 << result.avg_time_ms << ","
                 << result.min_time_ms << ","
                 << result.max_time_ms << ","
                 << result.stddev_ms << std::endl;
        }

        std::cout << "Results exported to " << filename << std::endl;
    }
};

int main(int argc, char* argv[]) {
    std::string z3_binary = "build/z3";
    int iterations = 5;
    std::string output_file = "z3_perf_results.csv";

    // Simple argument parsing
    for (int i = 1; i < argc; i++) {
        std::string arg = argv[i];
        if (arg == "--binary" && i + 1 < argc) {
            z3_binary = argv[++i];
        } else if (arg == "--iterations" && i + 1 < argc) {
            iterations = std::atoi(argv[++i]);
        } else if (arg == "--output" && i + 1 < argc) {
            output_file = argv[++i];
        } else if (arg == "--help") {
            std::cout << "Usage: " << argv[0] << " [options]" << std::endl;
            std::cout << "Options:" << std::endl;
            std::cout << "  --binary PATH    Path to Z3 binary (default: build/z3)" << std::endl;
            std::cout << "  --iterations N   Number of iterations per test (default: 5)" << std::endl;
            std::cout << "  --output FILE    Output CSV file (default: z3_perf_results.csv)" << std::endl;
            return 0;
        }
    }

    // Check if Z3 binary exists
    if (system(("test -f " + z3_binary).c_str()) != 0) {
        std::cerr << "Error: Z3 binary not found at " << z3_binary << std::endl;
        std::cerr << "Please build Z3 first or specify correct path with --binary" << std::endl;
        return 1;
    }

    Z3PerformanceSuite suite(z3_binary);
    auto results = suite.run_benchmark(iterations);
    suite.export_csv(results, output_file);

    // Summary
    double total_time = 0.0;
    for (const auto& result : results) {
        total_time += result.avg_time_ms;
    }

    std::cout << std::endl << "=== Summary ===" << std::endl;
    std::cout << "Total tests: " << results.size() << std::endl;
    std::cout << "Total time: " << total_time << " ms" << std::endl;
    std::cout << "Average per test: " << (total_time / results.size()) << " ms" << std::endl;

    return 0;
}