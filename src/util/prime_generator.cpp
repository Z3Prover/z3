/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    prime_generator.cpp

Abstract:

    Prime generator

Author:

    Leonardo (leonardo) 2011-12-23

Notes:

--*/
#include "util/prime_generator.h"

#define PRIME_LIST_MAX_SIZE 1<<20

prime_generator::prime_generator() {
    m_primes.push_back(2);
    m_primes.push_back(3);
    process_next_k_numbers(128);
}

void prime_generator::process_next_k_numbers(uint64_t k) {
    svector<uint64_t> todo;
    uint64_t begin = m_primes.back() + 2;
    uint64_t end   = begin + k;
    for (uint64_t i = begin; i < end; i+=2) {
        todo.push_back(i);
    }
    unsigned j = 1;
    SASSERT(m_primes[j] == 3);
    while (!todo.empty()) {
        unsigned sz = m_primes.size();
        for (; j < sz; j++) {
            uint64_t p = m_primes[j];
            unsigned todo_sz = todo.size();
            unsigned k1 = 0;
            unsigned k2 = 0;
            for (; k1 < todo_sz; k1++) {
                if (todo[k1] % p == 0)
                    continue;
                todo[k2] = todo[k1];
                k2++;
            }
            todo.shrink(k2);
            if (k2 == 0)
                return;
            if (p > (todo[k2-1] / p) + 1) {
                // all numbers in todo are primes
                for (unsigned k1 = 0; k1 < k2; k1++) {
                    m_primes.push_back(todo[k1]);
                }
                return;
            }
        }
        uint64_t p = m_primes.back();
        p = p*p;
        unsigned todo_sz = todo.size();
        unsigned k1 = 0;
        for (k1 = 0; k1 < todo_sz; k1++) {
            if (todo[k1] < p) {
                m_primes.push_back(todo[k1]);
            }
            else {
                break;
            }
        }
        unsigned k2 = 0;
        for (; k1 < todo_sz; k1++, k2++) {
            todo[k2] = todo[k1];
        }
        todo.shrink(k2);
    }
}

void prime_generator::finalize() {
    m_primes.finalize();
}

uint64_t prime_generator::operator()(unsigned idx) {
    if (idx < m_primes.size())
        return m_primes[idx];
    if (idx > PRIME_LIST_MAX_SIZE)
        throw prime_generator_exception("prime generator capacity exceeded");
    process_next_k_numbers(1024);
    if (idx < m_primes.size())
        return m_primes[idx];
    while (idx <= m_primes.size())
        process_next_k_numbers(1024*16);
    return m_primes[idx];
}

static prime_generator g_prime_generator;

prime_iterator::prime_iterator(prime_generator * g):m_idx(0) {
    if (g == nullptr) {
        m_generator = &g_prime_generator;
        m_global    = true;
    }
    else {
        m_generator = g;
        m_global    = false;
    }
}

uint64_t prime_iterator::next() {
    unsigned idx = m_idx;
    m_idx++;
    if (!m_global) {
        return (*m_generator)(idx);
    }
    else {
        uint64_t r;
        #pragma omp critical (prime_iterator)
        {
            r = (*m_generator)(idx);
        }
        return r;
    }
}

void prime_iterator::finalize() {
    g_prime_generator.finalize();
}

