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
#include "util/mpz.h"
#include "util/prime_generator.h"

void tst_prime_generator() {
    unsynch_mpz_manager m;
    scoped_mpz sqrt_p(m);

    prime_generator gen;
    gen.initialize();
    for (unsigned i = 0; i < 10000; i++) {
        uint64_t p = gen(i);
        std::cout << p << ", ";
        if (i % 11 == 0) std::cout << "\n";
        std::cout.flush();
        if (p == 2)
            continue;
        m.set(sqrt_p, p);
        m.root(sqrt_p, 2);
        uint64_t k = m.get_uint64(sqrt_p);
        for (uint64_t i = 2; i <= k; i++) {
            ENSURE(p % i != 0);
        }
    }
    gen.finalize();
    std::cout << std::endl;
}
