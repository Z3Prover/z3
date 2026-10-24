/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_certificate.h

Abstract:

    Format-independent ideal-membership certificates (a topologically
    ordered DAG of input/multiply/add steps) witnessing unsatisfiability of
    a system of prime-field polynomial equations, plus bounded
    reconstruction from the original equations.

Author:

    Romain Soulat

--*/
#pragma once
#include "math/ff/ff_polynomial.h"

namespace ff {
    // Format-independent ideal-membership evidence. Node IDs are indices in a
    // topologically ordered DAG; no node contains an expanded proof multiplier.
    struct certificate {
        enum class rule { input, multiply, add };
        struct node {
            rule kind;
            unsigned left = 0, right = 0;
            rational coefficient{1};
            monomial factor;
        };
        std::vector<node> nodes;
        unsigned root = 0;
    };

    enum class certificate_backend { scalar, f4, native, automatic };

    // Run the ordinary algebra engine with evidence observers attached. An
    // UNSAT result carries a derivation; SAT carries a candidate for the caller
    // to validate against its original AST premises.
    lbool solve_with_certificate(engine &arithmetic, std::vector<polynomial> const &equations,
                                 std::vector<rational> &values, certificate &output,
                                 unsigned max_nodes = 100000,
                                 bool native_unique = true, bool native_branches = true);

    // Bounded reconstruction from the original polynomial equations.
    // true witnesses 1 in their ideal. false means no certificate, never SAT.
    // Exhaustion propagates; output is replaced only on success. No cache,
    // field axioms, sampled models or unproved facts are used. The native backend
    // records shared uniqueness, native elimination and basis operations. Local
    // Boolean hypotheses are discharged into ring identities before export.
    // native_unique/native_branches disable shared propagation/branching for ablation.
    bool certify(engine &arithmetic, std::vector<polynomial> const &equations,
                 certificate &output, unsigned max_nodes = 100000,
                 certificate_backend backend = certificate_backend::automatic,
                 bool native_unique = true, bool native_branches = true);
}
