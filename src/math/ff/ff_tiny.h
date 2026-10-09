/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_tiny.h

Abstract:

    Complete finite-domain search for polynomial systems over tiny prime
    fields (p < 64). Every variable ranges over F_p, represented as a 64-bit
    domain mask; the search branches on the variable with the smallest domain
    and filters domains by forward checking: a constraint with a single
    unassigned variable is restricted to the univariate polynomial left after
    substituting the assigned values, and evaluated on the remaining domain.

    SAT answers are total assignments that satisfy every constraint. UNSAT
    answers follow from exhausting the finite search space, so every input
    constraint is a premise.

Author:

    Romain Soulat

--*/
#pragma once
#include "util/lbool.h"
#include <cstdint>
#include <functional>
#include <vector>

namespace ff {

    struct tiny_term {
        uint32_t coef;                // in [0, p)
        std::vector<uint32_t> vars;   // local variable indices, repeated for powers
    };

    struct tiny_constraint {
        bool is_neq = false;          // f != 0 instead of f = 0
        std::vector<tiny_term> terms;
    };

    struct tiny_stats {
        uint64_t nodes = 0;
        uint64_t filters = 0;
    };

    // Decide the constraints over F_p for variables 0..num_vars-1. On l_true,
    // model holds a satisfying assignment. `charge` is called with work units
    // and may throw to abort the search.
    lbool tiny_search(uint32_t p, unsigned num_vars, std::vector<tiny_constraint> const &cs,
                      std::vector<uint32_t> &model, std::function<void(unsigned)> const &charge,
                      tiny_stats &st);

}  // namespace ff
