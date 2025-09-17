#include <iostream>
#include <chrono>
#include <vector>
#include <memory>
#include <unordered_map>
#include <unordered_set>

// Mock implementation to benchmark the DAG optimization concept
// This simulates the performance improvement from DAG-aware traversal vs tree traversal

struct MockExpr {
    int id;
    std::vector<std::shared_ptr<MockExpr>> children;
    mutable int visit_count = 0;

    MockExpr(int _id) : id(_id) {}

    void add_child(std::shared_ptr<MockExpr> child) {
        children.push_back(child);
    }
};

class MockTreeChecker {
public:
    int tree_visits = 0;

    bool check_tree(std::shared_ptr<MockExpr> expr) {
        tree_visits++;
        expr->visit_count++;

        // Simulate some computation
        bool result = (expr->id % 2 == 0);

        // Tree-style traversal: always visits all children
        for (auto& child : expr->children) {
            result = result && check_tree(child);
        }

        return result;
    }
};

class MockDAGChecker {
public:
    std::unordered_map<int, bool> cache;
    int dag_visits = 0;

    bool check_dag(std::shared_ptr<MockExpr> expr) {
        dag_visits++;

        // DAG-aware: check cache first
        if (cache.find(expr->id) != cache.end()) {
            return cache[expr->id];
        }

        expr->visit_count++;

        // Simulate some computation
        bool result = (expr->id % 2 == 0);

        // DAG-style traversal: cache results to avoid redundant work
        for (auto& child : expr->children) {
            result = result && check_dag(child);
        }

        // Cache the result
        cache[expr->id] = result;
        return result;
    }
};

std::shared_ptr<MockExpr> create_dag_expression() {
    // Create a more complex DAG structure with heavy sharing
    // This simulates quantifier instantiation patterns with shared subexpressions

    std::vector<std::shared_ptr<MockExpr>> leaves;
    for (int i = 1; i <= 5; i++) {
        leaves.push_back(std::make_shared<MockExpr>(i));
    }

    std::vector<std::shared_ptr<MockExpr>> level1;
    // Create combinations at level 1 - each node uses multiple leaves
    for (int i = 0; i < 8; i++) {
        auto node = std::make_shared<MockExpr>(10 + i);
        // Each level1 node shares multiple leaves (creating DAG sharing)
        node->add_child(leaves[i % 5]);
        node->add_child(leaves[(i + 1) % 5]);
        node->add_child(leaves[(i + 2) % 5]);
        level1.push_back(node);
    }

    std::vector<std::shared_ptr<MockExpr>> level2;
    // Level 2 nodes heavily reuse level1 nodes
    for (int i = 0; i < 6; i++) {
        auto node = std::make_shared<MockExpr>(20 + i);
        node->add_child(level1[i % 8]);
        node->add_child(level1[(i + 2) % 8]);
        node->add_child(level1[(i + 4) % 8]);
        level2.push_back(node);
    }

    // Root level combines multiple level2 nodes
    auto root = std::make_shared<MockExpr>(100);
    for (int i = 0; i < 6; i++) {
        root->add_child(level2[i]);
    }

    return root;
}

void reset_visit_counts(std::shared_ptr<MockExpr> expr, std::unordered_set<int>& visited) {
    if (visited.find(expr->id) != visited.end())
        return;

    visited.insert(expr->id);
    expr->visit_count = 0;

    for (auto& child : expr->children) {
        reset_visit_counts(child, visited);
    }
}

int main() {
    std::cout << "=== SMT Checker DAG vs Tree Traversal Benchmark ===" << std::endl;

    // Create a complex DAG expression with many shared subexpressions
    auto expr = create_dag_expression();

    const int iterations = 1000;

    // Benchmark tree-style traversal (original implementation) - single check
    MockTreeChecker tree_checker;
    std::unordered_set<int> visited;

    auto start = std::chrono::high_resolution_clock::now();

    for (int i = 0; i < iterations; i++) {
        // Reset visit counts but keep the checker state
        visited.clear();
        reset_visit_counts(expr, visited);
        tree_checker.tree_visits = 0; // Reset counter for each iteration
        tree_checker.check_tree(expr);
    }

    auto tree_end = std::chrono::high_resolution_clock::now();
    auto tree_duration = std::chrono::duration_cast<std::chrono::microseconds>(tree_end - start);

    // Benchmark DAG-aware traversal (optimized implementation) - single check with caching
    MockDAGChecker dag_checker;

    start = std::chrono::high_resolution_clock::now();

    for (int i = 0; i < iterations; i++) {
        // Reset visit counts and cache for each iteration (simulates separate SMT check calls)
        visited.clear();
        reset_visit_counts(expr, visited);
        dag_checker.cache.clear();
        dag_checker.dag_visits = 0; // Reset counter for each iteration
        dag_checker.check_dag(expr);
    }

    auto dag_end = std::chrono::high_resolution_clock::now();
    auto dag_duration = std::chrono::duration_cast<std::chrono::microseconds>(dag_end - start);

    // For single expression analysis, let's also show the work difference
    visited.clear();
    reset_visit_counts(expr, visited);
    MockTreeChecker single_tree_checker;
    single_tree_checker.check_tree(expr);

    visited.clear();
    reset_visit_counts(expr, visited);
    MockDAGChecker single_dag_checker;
    single_dag_checker.check_dag(expr);

    // Results
    double speedup = (double)tree_duration.count() / dag_duration.count();
    double improvement = ((double)tree_duration.count() - dag_duration.count()) / tree_duration.count() * 100;

    std::cout << "Iterations: " << iterations << std::endl;
    std::cout << "Tree traversal time: " << tree_duration.count() << " μs" << std::endl;
    std::cout << "DAG traversal time: " << dag_duration.count() << " μs" << std::endl;
    std::cout << "Speedup: " << speedup << "x" << std::endl;
    std::cout << "Improvement: " << improvement << "%" << std::endl;

    // Show work reduction for single expression check
    std::cout << "\nWork reduction analysis (single expression check):" << std::endl;
    std::cout << "Tree checker visits: " << single_tree_checker.tree_visits << std::endl;
    std::cout << "DAG checker visits: " << single_dag_checker.dag_visits << std::endl;
    std::cout << "Visit reduction: " << (100.0 * (single_tree_checker.tree_visits - single_dag_checker.dag_visits) / single_tree_checker.tree_visits) << "%" << std::endl;

    return 0;
}