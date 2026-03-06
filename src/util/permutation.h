/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    permutation.h

Abstract:

    Simple abstraction for managing permutations.

Author:

    Leonardo de Moura (leonardo) 2011-06-10.

Revision History:

--*/
#pragma once

#include <ostream>
#include <span>
#include "util/vector.h"

class permutation {
    unsigned_vector m_p;
    unsigned_vector m_inv_p;
public:
    permutation(unsigned size = 0);
    void reset(unsigned size = 0);

    unsigned operator()(unsigned i) const { return m_p[i]; }
    unsigned inv(unsigned i_prime) const { return m_inv_p[i_prime]; }

    void swap(unsigned i, unsigned j) noexcept;
    void move_after(unsigned i, unsigned j);
    
    void display(std::ostream & out) const;
    bool check_invariant() const;
};

void swap(unsigned i, unsigned j) noexcept;

inline std::ostream & operator<<(std::ostream & out, permutation const & p) {
    p.display(out);
    return out;
}

/**
   \brief Apply permutation p to data.
   The algorithm does not use any extra memory.
   
   Requirement: swap(T, T) must be available.

   This version will perform destructive updates to p.
   Use apply_permutation if p must not be preserved
*/
template<typename T>
void apply_permutation_core(std::span<T> data, std::span<unsigned> p) {
    SASSERT(data.size() == p.size());
    int * p1 = reinterpret_cast<int*>(p.data());
    int sz = static_cast<int>(data.size());
    for (int i = 0; i < sz; ++i) {
        if (p1[i] < 0)
            continue; // already processed
        int j = i;
        while (true) {
            SASSERT(j >= 0);
            int p_j = p1[j];
            SASSERT(p_j >= 0);
            SASSERT(p_j < sz);
            p1[j]   = - p1[j] - 1; // mark as done
            if (p_j == i)
                break; // cycle starting at i is done
            swap(data[j], data[p_j]);
            j = p_j;
        }
    }
}

// Backward compatibility overload
template<typename T>
void apply_permutation_core(unsigned sz, T * data, unsigned * p) {
    apply_permutation_core(std::span<T>(data, sz), std::span<unsigned>(p, sz));
}

/**
   \brief Apply permutation p to data.
   The algorithm does not use any extra memory.
   
   Requirement: swap(T, T) must be available.
*/
template<typename T>
void apply_permutation(std::span<T> data, std::span<unsigned const> p) {
    SASSERT(data.size() == p.size());
    apply_permutation_core(data, std::span<unsigned>(const_cast<unsigned*>(p.data()), p.size()));
    // restore p
    int * p1 = reinterpret_cast<int*>(const_cast<unsigned*>(p.data()));
    int sz = static_cast<int>(p.size());
    for (int i = 0; i < sz; ++i) { 
        p1[i] = - p1[i] - 1;
    }
}

// Backward compatibility overload
template<typename T>
void apply_permutation(unsigned sz, T * data, unsigned const * p) {
    apply_permutation(std::span<T>(data, sz), std::span<unsigned const>(p, sz));
}

