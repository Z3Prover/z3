#include <iostream>
#include <chrono>
#include <vector>
#include <string>
#include <random>
#include <cassert>
#include <iomanip>

// Test both hash implementations directly
#include <cstring>
#include <cstdint>

// Bob Jenkins hash (original Z3)
#define mix(a,b,c)              \
{                               \
  a -= b; a -= c; a ^= (c>>13); \
  b -= c; b -= a; b ^= (a<<8);  \
  c -= a; c -= b; c ^= (b>>13); \
  a -= b; a -= c; a ^= (c>>12); \
  b -= c; b -= a; b ^= (a<<16); \
  c -= a; c -= b; c ^= (b>>5);  \
  a -= b; a -= c; a ^= (c>>3);  \
  b -= c; b -= a; b ^= (a<<10); \
  c -= a; c -= b; c ^= (b>>15); \
}

static unsigned read_unsigned(const char *s) {
  unsigned n;
  memcpy(&n, s, sizeof(unsigned));
  return n;
}

unsigned jenkins_hash(const char * str, unsigned length, unsigned init_value) {
    unsigned a, b, c, len;
    len = length;
    a = b = 0x9e3779b9;
    c = init_value;

    while (len >= 12) {
        a += read_unsigned(str);
        b += read_unsigned(str+4);
        c += read_unsigned(str+8);
        mix(a,b,c);
        str += 12; len -= 12;
    }

    c += length;
    switch(len) {
    case 11: c+=((unsigned)str[10]<<24);
    case 10: c+=((unsigned)str[9]<<16);
    case 9 : c+=((unsigned)str[8]<<8);
    case 8 : b+=((unsigned)str[7]<<24);
    case 7 : b+=((unsigned)str[6]<<16);
    case 6 : b+=((unsigned)str[5]<<8);
    case 5 : b+=str[4];
    case 4 : a+=((unsigned)str[3]<<24);
    case 3 : a+=((unsigned)str[2]<<16);
    case 2 : a+=((unsigned)str[1]<<8);
    case 1 : a+=str[0];
        break;
    }
    mix(a,b,c);
    return c;
}

// xxHash32 implementation
static const uint32_t XXHASH_PRIME1 = 0x9E3779B1U;
static const uint32_t XXHASH_PRIME2 = 0x85EBCA77U;
static const uint32_t XXHASH_PRIME3 = 0xC2B2AE3DU;
static const uint32_t XXHASH_PRIME4 = 0x27D4EB2FU;
static const uint32_t XXHASH_PRIME5 = 0x165667B1U;

static inline uint32_t xxhash_rotl32(uint32_t x, int r) {
    return (x << r) | (x >> (32 - r));
}

static inline uint32_t xxhash_read32le(const void* ptr) {
    uint32_t val;
    memcpy(&val, ptr, sizeof(val));
    return val;
}

unsigned xxhash32(const char* data, unsigned len, unsigned seed) {
    const uint8_t* p = (const uint8_t*)data;
    const uint8_t* const bEnd = p + len;
    uint32_t h32;

    if (len >= 16) {
        const uint8_t* const limit = bEnd - 16;
        uint32_t v1 = seed + XXHASH_PRIME1 + XXHASH_PRIME2;
        uint32_t v2 = seed + XXHASH_PRIME2;
        uint32_t v3 = seed + 0;
        uint32_t v4 = seed - XXHASH_PRIME1;

        do {
            v1 = xxhash_rotl32(v1 + xxhash_read32le(p) * XXHASH_PRIME2, 13) * XXHASH_PRIME1;
            p += 4;
            v2 = xxhash_rotl32(v2 + xxhash_read32le(p) * XXHASH_PRIME2, 13) * XXHASH_PRIME1;
            p += 4;
            v3 = xxhash_rotl32(v3 + xxhash_read32le(p) * XXHASH_PRIME2, 13) * XXHASH_PRIME1;
            p += 4;
            v4 = xxhash_rotl32(v4 + xxhash_read32le(p) * XXHASH_PRIME2, 13) * XXHASH_PRIME1;
            p += 4;
        } while (p <= limit);

        h32 = xxhash_rotl32(v1, 1) + xxhash_rotl32(v2, 7) + xxhash_rotl32(v3, 12) + xxhash_rotl32(v4, 18);
    } else {
        h32 = seed + XXHASH_PRIME5;
    }

    h32 += (uint32_t) len;

    while (p + 4 <= bEnd) {
        h32 += xxhash_read32le(p) * XXHASH_PRIME3;
        h32  = xxhash_rotl32(h32, 17) * XXHASH_PRIME4;
        p += 4;
    }

    while (p < bEnd) {
        h32 += (*p) * XXHASH_PRIME5;
        h32 = xxhash_rotl32(h32, 11) * XXHASH_PRIME1;
        p++;
    }

    h32 ^= h32 >> 15;
    h32 *= XXHASH_PRIME2;
    h32 ^= h32 >> 13;
    h32 *= XXHASH_PRIME3;
    h32 ^= h32 >> 16;

    return h32;
}

// Generate test data with different size categories
std::vector<std::string> generate_test_data() {
    std::vector<std::string> data;
    std::mt19937 rng(42);

    // Small strings (typical variable names, operators)
    std::uniform_int_distribution<> small_len(4, 16);
    for (int i = 0; i < 10000; ++i) {
        int len = small_len(rng);
        std::string s = "var_" + std::to_string(i);
        while (s.length() < len) s += "_x";
        s.resize(len);
        data.push_back(s);
    }

    // Medium strings (expressions, terms)
    std::uniform_int_distribution<> med_len(32, 128);
    for (int i = 0; i < 5000; ++i) {
        int len = med_len(rng);
        std::string s = "(assert (and ";
        while (s.length() < len) {
            s += "(> x_" + std::to_string(i % 100) + " " + std::to_string(i % 10) + ") ";
        }
        s.resize(len - 2);
        s += "))";
        data.push_back(s);
    }

    // Large strings (complex formulas)
    std::uniform_int_distribution<> large_len(256, 1024);
    for (int i = 0; i < 1000; ++i) {
        int len = large_len(rng);
        std::string s = "(assert (or ";
        while (s.length() < len) {
            s += "(and (= term_" + std::to_string(i) + "_" + std::to_string(s.length() % 50);
            s += " value_" + std::to_string(i % 20) + ") ";
            s += "(> expr_" + std::to_string(i % 30) + " 0)) ";
        }
        s.resize(len - 2);
        s += "))";
        data.push_back(s);
    }

    // Very large strings (where xxHash should excel)
    std::uniform_int_distribution<> xl_len(1024, 4096);
    for (int i = 0; i < 500; ++i) {
        int len = xl_len(rng);
        std::string s;
        s.reserve(len);
        while (s.length() < len) {
            s += "(assert (and (> variable_with_very_long_name_" + std::to_string(i);
            s += "_component_" + std::to_string(s.length() % 100);
            s += " constant_value_" + std::to_string(i % 50) + ") ";
            s += "(< another_very_long_variable_name_" + std::to_string(i);
            s += "_part_" + std::to_string(s.length() % 200);
            s += " upper_bound_" + std::to_string(i % 25) + "))) ";
        }
        s.resize(len);
        data.push_back(s);
    }

    return data;
}

template<typename HashFunc>
double benchmark_hash(const std::vector<std::string>& data, HashFunc hash_func, const std::string& name) {
    const int iterations = 10000;

    auto start = std::chrono::high_resolution_clock::now();
    volatile unsigned result = 0;

    for (int iter = 0; iter < iterations; ++iter) {
        for (const auto& str : data) {
            result += hash_func(str.c_str(), str.length(), 0);
        }
    }

    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

    if (result == 0xDEADBEEF) std::cout << "Impossible";

    double ms = duration.count() / 1000.0;

    // Calculate throughput
    size_t total_bytes = 0;
    for (const auto& str : data) total_bytes += str.length();
    double mb_per_sec = (total_bytes * iterations) / (ms * 1024.0);

    std::cout << name << ": " << std::fixed << std::setprecision(3)
              << ms << " ms (" << mb_per_sec << " MB/sec)" << std::endl;

    return ms;
}

int main() {
    std::cout << "=== Extended Hash Function Performance Benchmark ===" << std::endl;
    std::cout << "Testing with comprehensive Z3-realistic workloads" << std::endl;

    auto test_data = generate_test_data();
    std::cout << "\nGenerated " << test_data.size() << " test strings" << std::endl;

    // Calculate size distribution
    size_t total_bytes = 0;
    size_t small_count = 0, med_count = 0, large_count = 0, xl_count = 0;

    for (const auto& str : test_data) {
        total_bytes += str.length();
        if (str.length() <= 16) small_count++;
        else if (str.length() <= 128) med_count++;
        else if (str.length() <= 1024) large_count++;
        else xl_count++;
    }

    std::cout << "Distribution:" << std::endl;
    std::cout << "  Small (≤16):     " << small_count << " strings" << std::endl;
    std::cout << "  Medium (≤128):   " << med_count << " strings" << std::endl;
    std::cout << "  Large (≤1024):   " << large_count << " strings" << std::endl;
    std::cout << "  XL (>1024):      " << xl_count << " strings" << std::endl;
    std::cout << "  Total data:      " << (total_bytes / 1024) << " KB" << std::endl;

    std::cout << "\n--- Performance Comparison (100 iterations) ---" << std::endl;

    double jenkins_time = benchmark_hash(test_data, jenkins_hash, "Bob Jenkins Hash");
    double xxhash_time = benchmark_hash(test_data, xxhash32, "xxHash32        ");

    std::cout << "\n=== Performance Summary ===" << std::endl;
    std::cout << std::fixed << std::setprecision(3);
    std::cout << "Jenkins time:  " << jenkins_time << " ms" << std::endl;
    std::cout << "xxHash time:   " << xxhash_time << " ms" << std::endl;

    if (xxhash_time < jenkins_time) {
        double speedup = jenkins_time / xxhash_time;
        double improvement = ((jenkins_time - xxhash_time) / jenkins_time) * 100;
        std::cout << "Speedup:       " << speedup << "x (" << improvement << "% faster)" << std::endl;
    } else {
        double slowdown = xxhash_time / jenkins_time;
        double regression = ((xxhash_time - jenkins_time) / jenkins_time) * 100;
        std::cout << "Slowdown:      " << slowdown << "x (" << regression << "% slower)" << std::endl;
    }

    return 0;
}