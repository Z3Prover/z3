/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bitvector.cpp

Abstract:

    Simple bitvector implementation

Author:

    Leonardo de Moura (leonardo) 2006-10-03.

Revision History:

--*/
#include<climits>
#include "util/bit_vector.h"
#include "util/trace.h"
#ifdef __SSE2__
#include <emmintrin.h>
#endif

#define DEFAULT_CAPACITY 2

#define MK_MASK(_num_bits_) ((1U << _num_bits_) - 1)

// SIMD optimization helpers
#ifdef __SSE2__
namespace {
    // SIMD-optimized bitwise operations for aligned memory
    inline void simd_or_aligned(unsigned* dst, const unsigned* src, size_t num_words) {
        const size_t simd_words = (num_words / 4) * 4;
        const __m128i* src_simd = reinterpret_cast<const __m128i*>(src);
        __m128i* dst_simd = reinterpret_cast<__m128i*>(dst);

        for (size_t i = 0; i < simd_words / 4; ++i) {
            __m128i a = _mm_load_si128(&dst_simd[i]);
            __m128i b = _mm_load_si128(&src_simd[i]);
            _mm_store_si128(&dst_simd[i], _mm_or_si128(a, b));
        }

        // Handle remaining words with scalar operations
        for (size_t i = simd_words; i < num_words; ++i) {
            dst[i] |= src[i];
        }
    }

    inline void simd_and_aligned(unsigned* dst, const unsigned* src, size_t num_words) {
        const size_t simd_words = (num_words / 4) * 4;
        const __m128i* src_simd = reinterpret_cast<const __m128i*>(src);
        __m128i* dst_simd = reinterpret_cast<__m128i*>(dst);

        for (size_t i = 0; i < simd_words / 4; ++i) {
            __m128i a = _mm_load_si128(&dst_simd[i]);
            __m128i b = _mm_load_si128(&src_simd[i]);
            _mm_store_si128(&dst_simd[i], _mm_and_si128(a, b));
        }

        // Handle remaining words with scalar operations
        for (size_t i = simd_words; i < num_words; ++i) {
            dst[i] &= src[i];
        }
    }

    inline bool simd_equals_aligned(const unsigned* a, const unsigned* b, size_t num_words) {
        const size_t simd_words = (num_words / 4) * 4;
        const __m128i* a_simd = reinterpret_cast<const __m128i*>(a);
        const __m128i* b_simd = reinterpret_cast<const __m128i*>(b);

        for (size_t i = 0; i < simd_words / 4; ++i) {
            __m128i vec_a = _mm_load_si128(&a_simd[i]);
            __m128i vec_b = _mm_load_si128(&b_simd[i]);
            __m128i cmp = _mm_cmpeq_epi32(vec_a, vec_b);

            if (_mm_movemask_epi8(cmp) != 0xFFFF) {
                return false;
            }
        }

        // Handle remaining words with scalar operations
        for (size_t i = simd_words; i < num_words; ++i) {
            if (a[i] != b[i]) return false;
        }

        return true;
    }

    inline void simd_negate_aligned(unsigned* data, size_t num_words) {
        const size_t simd_words = (num_words / 4) * 4;
        __m128i* data_simd = reinterpret_cast<__m128i*>(data);
        const __m128i ones = _mm_set1_epi32(~0);

        for (size_t i = 0; i < simd_words / 4; ++i) {
            __m128i vec = _mm_load_si128(&data_simd[i]);
            _mm_store_si128(&data_simd[i], _mm_xor_si128(vec, ones));
        }

        // Handle remaining words with scalar operations
        for (size_t i = simd_words; i < num_words; ++i) {
            data[i] = ~data[i];
        }
    }

    // Check if pointer is 16-byte aligned for SSE2
    inline bool is_aligned_16(const void* ptr) {
        return (reinterpret_cast<uintptr_t>(ptr) & 15) == 0;
    }
}
#endif

void bit_vector::expand_to(unsigned new_capacity) {
    if (m_data) {
        m_data = (unsigned*)memory::reallocate(m_data, new_capacity * sizeof(unsigned));
    } else {
        m_data = alloc_svect(unsigned, new_capacity);
    }
    memset(m_data + m_capacity, 0, (new_capacity - m_capacity) * sizeof(unsigned));
    m_capacity = new_capacity;
}

void bit_vector::resize(unsigned new_size, bool val) {
    if (new_size <= m_num_bits) {
        m_num_bits = new_size;
        return;
    }
 
    TRACE(bit_vector, tout << "expanding: " << new_size << " capacity: " << m_capacity << " num words: " 
          << num_words(new_size) << "\n";);

    if (num_words(new_size) > m_capacity) {
        expand_to((num_words(new_size) * 3 + 1) >> 1);
    }


    unsigned bwidx   = m_num_bits/32;
    unsigned ewidx   = num_words(new_size);
    unsigned * begin = m_data + bwidx;
    unsigned pos     = m_num_bits % 32;
    unsigned mask    = MK_MASK(pos);
    int      cval;

    if (val) {
        *begin |= ~mask;
        cval    = ~0;
    }
    else {
        *begin &= mask;
        cval    = 0;
    }

    TRACE(bit_vector,
          tout << "num_bits: " << m_num_bits << "\n";
          tout << "bwidx:    " << bwidx << "\n";
          tout << "ewidx:    " << ewidx << "\n";
          tout << "pos:      " << pos << "\n";
          tout << "mask:     " << std::hex << mask << "\n" << std::dec;
          tout << "cval:     " << cval << "\n";);

    if (bwidx < ewidx) {
        memset(begin + 1, cval, (ewidx - bwidx - 1) * sizeof(unsigned));
    }
    
    m_num_bits = new_size;
}

void bit_vector::shift_right(unsigned k) {
    if (k == 0)
        return;
    unsigned new_num_bits  = m_num_bits + k;
    unsigned old_num_words = num_words(m_num_bits);
    unsigned new_num_words = num_words(new_num_bits);
    resize(m_num_bits + k, false);
    unsigned bit_shift  = k % (8 * sizeof(unsigned));
    unsigned word_shift = k / (8 * sizeof(unsigned));
    if (word_shift > 0) {
        unsigned j = old_num_words;
        unsigned i = old_num_words + word_shift;
        while (j > 0) {
            --j; --i;
            m_data[i] = m_data[j];
        }
        while (i > 0) {
            --i;
            m_data[i] = 0;
        }
    }
    if (bit_shift > 0) {
        DEBUG_CODE({
            for (unsigned i = 0; i < word_shift; i++) {
                SASSERT(m_data[i] == 0);
            }
        });
        unsigned comp_shift = (8 * sizeof(unsigned)) - bit_shift;
        unsigned prev = 0;
        for (unsigned i = word_shift; i < new_num_words; i++) {
            unsigned new_prev = (m_data[i] >> comp_shift);
            m_data[i] <<= bit_shift;
            m_data[i] |= prev;
            prev = new_prev;
        }
    }
}

bool bit_vector::operator==(bit_vector const & source) const {
    if (m_num_bits != source.m_num_bits)
        return false;
    unsigned n = num_words();
    if (n == 0)
        return true;

#ifdef __SSE2__
    // Use SIMD optimization for aligned memory and sufficient size
    if (n >= 4 && is_aligned_16(m_data) && is_aligned_16(source.m_data)) {
        if (n > 1) {
            // Compare all but the last word with SIMD
            if (!simd_equals_aligned(m_data, source.m_data, n - 1))
                return false;
        }

        // Handle the last word with potential mask
        unsigned bit_rest = source.m_num_bits % 32;
        unsigned mask = MK_MASK(bit_rest);
        if (mask == 0) mask = UINT_MAX;
        return (m_data[n-1] & mask) == (source.m_data[n-1] & mask);
    }
#endif

    // Fallback to scalar implementation
    unsigned i;
    for (i = 0; i < n - 1; i++) {
        if (m_data[i] != source.m_data[i])
            return false;
    }
    unsigned bit_rest = source.m_num_bits % 32;
    unsigned mask = MK_MASK(bit_rest);
    if (mask == 0) mask = UINT_MAX;
    return (m_data[i] & mask) == (source.m_data[i] & mask);
}

bit_vector & bit_vector::operator|=(bit_vector const & source) {
    if (size() < source.size())
        resize(source.size(), false);
    unsigned n2 = source.num_words();
    SASSERT(n2 <= num_words());
    unsigned bit_rest = source.m_num_bits % 32;

#ifdef __SSE2__
    // Use SIMD optimization for aligned memory and sufficient size
    if (n2 >= 4 && is_aligned_16(m_data) && is_aligned_16(source.m_data)) {
        if (bit_rest == 0) {
            simd_or_aligned(m_data, source.m_data, n2);
        } else {
            simd_or_aligned(m_data, source.m_data, n2 - 1);
            // Handle the last word with mask manually
            unsigned mask = MK_MASK(bit_rest);
            m_data[n2 - 1] |= source.m_data[n2 - 1] & mask;
        }
        return *this;
    }
#endif

    // Fallback to scalar implementation
    if (bit_rest == 0) {
        unsigned i = 0;
        for (i = 0; i < n2; i++)
            m_data[i] |= source.m_data[i];
    }
    else {
        unsigned i = 0;
        for (i = 0; i < n2 - 1; i++)
            m_data[i] |= source.m_data[i];
        unsigned mask = MK_MASK(bit_rest);
        m_data[i] |= source.m_data[i] & mask;
    }
    return *this;
}

bit_vector & bit_vector::operator&=(bit_vector const & source) {
    unsigned n1 = num_words();
    unsigned n2 = source.num_words();
    if (n1 == 0)
        return *this;

#ifdef __SSE2__
    // Use SIMD optimization for aligned memory and sufficient size
    if (n2 >= 4 && is_aligned_16(m_data) && is_aligned_16(source.m_data)) {
        if (n2 > n1) {
            simd_and_aligned(m_data, source.m_data, n1);
        } else {
            unsigned bit_rest = source.m_num_bits % 32;
            if (bit_rest == 0) {
                simd_and_aligned(m_data, source.m_data, n2);
                // Clear remaining words
                for (unsigned i = n2; i < n1; i++)
                    m_data[i] = 0;
            } else {
                simd_and_aligned(m_data, source.m_data, n2 - 1);
                // Handle the last word with mask manually
                unsigned mask = MK_MASK(bit_rest);
                m_data[n2 - 1] &= (source.m_data[n2 - 1] & mask);
                // Clear remaining words
                for (unsigned i = n2; i < n1; i++)
                    m_data[i] = 0;
            }
        }
        return *this;
    }
#endif

    // Fallback to scalar implementation
    if (n2 > n1) {
        for (unsigned i = 0; i < n1; i++)
            m_data[i] &= source.m_data[i];
    }
    else {
        SASSERT(n2 <= n1);
        unsigned bit_rest = source.m_num_bits % 32;
        unsigned i = 0;
        if (bit_rest == 0) {
            for (i = 0; i < n2; i++)
                m_data[i] &= source.m_data[i];
        }
        else {
            for (i = 0; i < n2 - 1; i++)
                m_data[i] &= source.m_data[i];
            unsigned mask = MK_MASK(bit_rest);
            m_data[i] &= (source.m_data[i] & mask);

        }
        for (i = n2; i < n1; i++)
            m_data[i] = 0;
    }
    return *this;
}

void bit_vector::display(std::ostream & out) const {
#if 1
    unsigned i = m_num_bits;
    while (i > 0) {
        --i;
        if (get(i))
            out << "1";
        else
            out << "0";
    }
#else
    for (unsigned i = 0; i < m_num_bits; i++) {
        if (get(i))
            out << "1";
        else
            out << "0";
        if ((i + 1) % 32 == 0) out << "\n";
    } 
#endif
}

bool bit_vector::contains(bit_vector const& other) const {
    unsigned n = num_words();
    if (n == 0)
        return true;
    
    for (unsigned i = 0; i < n - 1; ++i) {
        if ((m_data[i] & other.m_data[i]) != other.m_data[i])
            return false;
    }
    unsigned bit_rest = m_num_bits % 32;
    unsigned mask = (1U << bit_rest) - 1;
    if (mask == 0) mask = UINT_MAX;
    unsigned other_data = other.m_data[n-1] & mask;
    return (m_data[n-1] & other_data) == other_data;
}

unsigned bit_vector::get_hash() const {
    return string_hash(reinterpret_cast<char const* const>(m_data), size()/8,  0);
}

bit_vector& bit_vector::neg() {
    unsigned n = num_words();

#ifdef __SSE2__
    // Use SIMD optimization for aligned memory and sufficient size
    if (n >= 4 && is_aligned_16(m_data)) {
        simd_negate_aligned(m_data, n);
        return *this;
    }
#endif

    // Fallback to scalar implementation
    for (unsigned i = 0; i < n; ++i) {
        m_data[i] = ~m_data[i];
    }
    return *this;
}

void fr_bit_vector::reset() {
    unsigned sz = size();
    unsigned_vector::const_iterator it  = m_one_idxs.begin();
    unsigned_vector::const_iterator end = m_one_idxs.end();
    for (; it != end; ++it) {
        unsigned idx = *it;
        if (idx < sz)
            unset(idx);
    }
    m_one_idxs.reset();
}
