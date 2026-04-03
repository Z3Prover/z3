
/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_gc.cpp

Abstract:

    Benchmark to test the effect of learned clause cleanup on user pop,
    controlled by the sat.gc.learned_pop parameter.

    After push/check-sat/pop, learned clauses produced by conflict analysis
    that uses only outer-scope clause reasons (and thus carries no scope-guard
    literal) survive gc_vars.  These stale clauses accumulate across repeated
    push/pop cycles and can slow subsequent proofs.

    The gc.learned_pop parameter (default true) removes those clauses on each
    pop so the clause database stays clean.

--*/

#include "sat/sat_solver.h"
#include "util/util.h"
#include "util/stopwatch.h"
#include <iostream>

// Add random 3-SAT clauses on variables [base, base+n_vars).
static void add_random_3sat(sat::solver& s, unsigned base, unsigned n_vars,
                             unsigned n_clauses, random_gen& rng) {
    while ((unsigned)s.num_vars() < base + n_vars)
        s.mk_var(true, true);
    for (unsigned i = 0; i < n_clauses; ++i) {
        sat::literal lits[3];
        for (unsigned k = 0; k < 3; ++k)
            lits[k] = sat::literal(base + rng(n_vars), rng(2) == 0);
        s.mk_clause(3, lits);
    }
}

// Run the benchmark.
//
// Scenario:
//   1. Add a near-phase-transition random 3-SAT formula on N outer variables.
//      Clause ratio > 4.27 means many instances are UNSAT.
//      These outer-scope clauses carry no scope-guard literal.
//   2. Run cycles push/pop rounds.  In each round the solver derives conflicts
//      from those outer clauses, producing learned lemmas that do NOT carry the
//      scope-guard literal and therefore survive gc_vars after pop.
//      - gc.learned_pop=true:  surviving clauses are removed on pop.
//      - gc.learned_pop=false: they accumulate across all cycles.
//   3. Perform the final check-sat and measure time.
//
// The extra accumulated learned clauses (without gc.learned_pop) inflate watch
// lists for outer variables and slow subsequent BCP.
static void run_benchmark(bool gc_learned_pop,
                           unsigned n_vars, double ratio, unsigned cycles,
                           unsigned seed,
                           unsigned& out_learned, double& out_time) {
    params_ref p;
    p.set_bool("gc.learned_pop", gc_learned_pop);
    p.set_uint("random_seed", seed);
    reslimit rlim;

    sat::solver s(p, rlim);
    s.mk_var(false, false);   // variable 0 unused

    random_gen rng(seed);
    unsigned n_clauses = static_cast<unsigned>(ratio * n_vars);
    add_random_3sat(s, 1, n_vars, n_clauses, rng);

    // Push/pop cycles: each re-solves the same outer formula, generating
    // learned lemmas from outer-scope clauses that survive pop when not cleaned.
    for (unsigned c = 0; c < cycles; ++c) {
        s.user_push();
        s.check();
        s.user_pop(1);
    }

    out_learned = s.learned().size();

    stopwatch sw;
    sw.start();
    s.check();
    sw.stop();
    out_time = sw.get_seconds();
}

void tst_sat_gc() {
    // Use a moderate near-phase-transition instance to demonstrate the effect.
    // Increase n_vars, cycles, or ratio for a larger performance difference.
    const unsigned n_vars  = 200;
    const double   ratio   = 4.5;
    const unsigned cycles  = 3;
    const unsigned seed    = 42;

    unsigned lrn_with, lrn_without;
    double   t_with,   t_without;

    run_benchmark(true,  n_vars, ratio, cycles, seed, lrn_with,    t_with);
    run_benchmark(false, n_vars, ratio, cycles, seed, lrn_without, t_without);

    std::cout << "sat.gc.learned_pop=true  : learned=" << lrn_with
              << "  time=" << t_with    << "s\n";
    std::cout << "sat.gc.learned_pop=false : learned=" << lrn_without
              << "  time=" << t_without << "s\n";

    // The core invariant: gc.learned_pop removes stale inner-scope clauses.
    VERIFY(lrn_with <= lrn_without);

    if (lrn_without > lrn_with)
        std::cout << "Clauses cleaned up by gc.learned_pop: "
                  << (lrn_without - lrn_with) << "\n";
    if (t_without > t_with * 1.05)
        std::cout << "Speedup: " << (t_without / t_with) << "x\n";
    else
        std::cout << "(use larger n_vars/cycles to observe timing impact)\n";
}
