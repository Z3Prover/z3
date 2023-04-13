/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    distribution.cpp

Abstract:

    Test distribution

Author:

    Nikolaj Bjorner (nbjorner) 2023-04-13


--*/
#include "util/distribution.h"
#include <iostream>

static void tst1() {
    distribution dist(1);
    dist.push(1, 3);
    dist.push(2, 1);
    dist.push(3, 1);
    dist.push(4, 1);

    unsigned counts[4] = { 0, 0, 0, 0 };
    for (unsigned i = 0; i < 1000; ++i)
        counts[dist.choose()-1]++;
    for (unsigned i = 1; i <= 4; ++i)
        std::cout << "count " << i << ": " << counts[i-1] << "\n";

    for (unsigned i = 0; i < 5; ++i) {
        std::cout << "enum ";
        for (auto j : dist)
            std::cout << j << " ";
        std::cout << "\n";
    }

}

void tst_distribution() {
    tst1();
}
