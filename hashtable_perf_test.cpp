#include "src/util/hashtable.h"
#include "src/util/hash.h"
#include <iostream>
#include <chrono>
#include <vector>
#include <random>

struct int_hash {
    unsigned operator()(int k) const { return static_cast<unsigned>(k) * 2654435761U; }
};

struct int_eq {
    bool operator()(int a, int b) const { return a == b; }
};

typedef hashtable<int, int_hash, int_eq> int_hashtable;

void test_hashtable_performance() {
    std::cout << "Testing hashtable performance optimization..." << std::endl;

    const int num_operations = 100000;
    int_hashtable table;

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<> dis(1, 1000000);

    std::vector<int> test_data;
    for (int i = 0; i < num_operations; ++i) {
        test_data.push_back(dis(gen));
    }

    // Test insertion performance
    auto start = std::chrono::high_resolution_clock::now();

    for (int i = 0; i < num_operations; ++i) {
        table.insert(test_data[i]);
    }

    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

    std::cout << "Inserted " << num_operations << " elements in " << duration.count() << " microseconds" << std::endl;
    std::cout << "Table size: " << table.size() << std::endl;
    std::cout << "Table capacity: " << table.capacity() << std::endl;
    std::cout << "Load factor: " << table.get_load_factor() << std::endl;
    std::cout << "Effective load factor: " << table.get_effective_load_factor() << std::endl;

    // Test lookup performance
    start = std::chrono::high_resolution_clock::now();

    int found = 0;
    for (int i = 0; i < num_operations; ++i) {
        if (table.contains(test_data[i])) {
            found++;
        }
    }

    end = std::chrono::high_resolution_clock::now();
    duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

    std::cout << "Looked up " << num_operations << " elements (" << found << " found) in " << duration.count() << " microseconds" << std::endl;
    std::cout << "Performance test completed." << std::endl;
}

int main() {
    test_hashtable_performance();
    return 0;
}