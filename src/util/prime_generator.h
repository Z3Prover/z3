/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    prime_generator.h

Abstract:

    Prime generator

Author:

    Leonardo (leonardo) 2011-12-23

Notes:

--*/
#ifndef PRIME_GENERATOR_H_
#define PRIME_GENERATOR_H_

#include"vector.h"
#include"z3_exception.h"
#include"util.h"

class prime_generator_exception : public default_exception {
public:
    prime_generator_exception(char const * msg):default_exception(msg) {}
};

/**
   \brief Prime generator
*/
class prime_generator {
    svector<uint64> m_primes;
    void process_next_k_numbers(uint64 k);
public:
    prime_generator();
    uint64 operator()(unsigned idx);
    void finalize();
};

class prime_iterator {
    unsigned          m_idx;
    prime_generator * m_generator;
    bool              m_global;
public:
    prime_iterator(prime_generator * g = 0);
    uint64 next();
    static void finalize();
    /*
      ADD_FINALIZER('prime_iterator::finalize();')
    */
};

#endif
