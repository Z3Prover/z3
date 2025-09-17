#include <iostream>
#include <chrono>
#include <vector>
#include <string>
#include <cstring>
#include <random>

// Include Z3's original hash functions
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

// Original Z3 string_hash (Bob Jenkins)
unsigned string_hash_original(const char * str, unsigned length, unsigned init_value) {
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

// Compact xxHash32 implementation optimized for Z3
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

// xxHash32 optimized for Z3's usage patterns
unsigned string_hash_xxhash(const char* data, unsigned len, unsigned seed) {
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

// Test data generation
std::vector<std::string> generate_test_data(size_t count, size_t min_len, size_t max_len) {
    std::vector<std::string> data;
    data.reserve(count);

    std::random_device rd;
    std::mt19937 gen(42); // Fixed seed for reproducibility
    std::uniform_int_distribution<> len_dist(min_len, max_len);
    std::uniform_int_distribution<> char_dist(32, 126); // Printable ASCII

    for (size_t i = 0; i < count; ++i) {
        size_t len = len_dist(gen);
        std::string s;
        s.reserve(len);
        for (size_t j = 0; j < len; ++j) {
            s.push_back(static_cast<char>(char_dist(gen)));
        }
        data.push_back(std::move(s));
    }
    return data;
}

// Benchmark function
template<typename HashFunc>
double benchmark_hash_function(const std::vector<std::string>& test_data, HashFunc hash_func, int iterations = 100) {
    auto start = std::chrono::high_resolution_clock::now();

    volatile unsigned result = 0; // Prevent optimization
    for (int iter = 0; iter < iterations; ++iter) {
        for (const auto& str : test_data) {
            result += hash_func(str.c_str(), str.length(), 0);
        }
    }

    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

    // Prevent dead code elimination
    if (result == 0xDEADBEEF) std::cout << "Impossible";

    return duration.count() / 1000.0; // Return milliseconds
}

int main() {
    std::cout << "=== Z3 Hash Function Performance Benchmark ===" << std::endl;

    // Generate test data that represents typical Z3 usage
    std::vector<std::string> short_strings = generate_test_data(50000, 4, 32);    // Symbols, variables
    std::vector<std::string> medium_strings = generate_test_data(10000, 32, 128); // Terms, expressions
    std::vector<std::string> long_strings = generate_test_data(1000, 128, 512);   // Large expressions

    std::cout << "\n--- Short Strings (4-32 chars, 50K strings, 100 iterations) ---" << std::endl;
    double orig_short = benchmark_hash_function(short_strings, string_hash_original);
    double xxh_short = benchmark_hash_function(short_strings, string_hash_xxhash);

    std::cout << "Original (Bob Jenkins): " << orig_short << " ms" << std::endl;
    std::cout << "xxHash32:              " << xxh_short << " ms" << std::endl;
    std::cout << "Speedup:               " << (orig_short / xxh_short) << "x" << std::endl;

    std::cout << "\n--- Medium Strings (32-128 chars, 10K strings, 100 iterations) ---" << std::endl;
    double orig_medium = benchmark_hash_function(medium_strings, string_hash_original);
    double xxh_medium = benchmark_hash_function(medium_strings, string_hash_xxhash);

    std::cout << "Original (Bob Jenkins): " << orig_medium << " ms" << std::endl;
    std::cout << "xxHash32:              " << xxh_medium << " ms" << std::endl;
    std::cout << "Speedup:               " << (orig_medium / xxh_medium) << "x" << std::endl;

    std::cout << "\n--- Long Strings (128-512 chars, 1K strings, 100 iterations) ---" << std::endl;
    double orig_long = benchmark_hash_function(long_strings, string_hash_original);
    double xxh_long = benchmark_hash_function(long_strings, string_hash_xxhash);

    std::cout << "Original (Bob Jenkins): " << orig_long << " ms" << std::endl;
    std::cout << "xxHash32:              " << xxh_long << " ms" << std::endl;
    std::cout << "Speedup:               " << (orig_long / xxh_long) << "x" << std::endl;

    // Overall performance metrics
    double total_orig = orig_short + orig_medium + orig_long;
    double total_xxh = xxh_short + xxh_medium + xxh_long;

    std::cout << "\n=== Overall Performance Summary ===" << std::endl;
    std::cout << "Total Original: " << total_orig << " ms" << std::endl;
    std::cout << "Total xxHash:   " << total_xxh << " ms" << std::endl;
    std::cout << "Overall Speedup: " << (total_orig / total_xxh) << "x" << std::endl;

    return 0;
}