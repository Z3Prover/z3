/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    tactical.h

Abstract:

    Basic combinators

Author:

    Leonardo (leonardo) 2011-10-13

Notes:

--*/
#pragma once

#include "tactic/tactic.h"
#include "tactic/probe.h"

tactic * and_then(unsigned num, tactic * const * ts);
tactic * and_then(tactic * t1, tactic * t2);
tactic * and_then(tactic * t1, tactic * t2, tactic * t3);
tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4);
tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5);
tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6);
tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7);
tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8);
tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8, tactic * t9);
tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8, tactic * t9, tactic * t10);
tactic * and_then(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8, tactic * t9, tactic * t10, tactic * t11);

tactic * or_else(unsigned num, tactic * const * ts);
tactic * or_else(tactic * t1, tactic * t2);
tactic * or_else(tactic * t1, tactic * t2, tactic * t3);
tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4);
tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5);
tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6);
tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7);
tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8);
tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8, tactic * t9);
tactic * or_else(tactic * t1, tactic * t2, tactic * t3, tactic * t4, tactic * t5, tactic * t6, tactic * t7, tactic * t8, tactic * t9, tactic * t10);

/**
   \brief Variant of or_else(t1, t2) for the case where only \c t2 supports user
   propagation. All user propagator and on-clause registrations are forwarded to
   \c t2 only, and once any of them is registered \c t1 is bypassed entirely.

   The optional \c use_t1 predicate is evaluated on the current parameters before
   every invocation and can additionally disable \c t1. \c p seeds those
   parameters, so the predicate is meaningful even when updt_params is never called.
*/
tactic * or_else_no_user_propagate(tactic * t1, tactic * t2, params_ref const & p,
                                   std::function<bool(params_ref const &)> use_t1 = nullptr);

tactic * repeat(tactic * t, unsigned max = UINT_MAX); 
/**
   \brief Fails if \c t produces more than \c threshold subgoals.
   Otherwise, it behaves like \c t.
*/
tactic * fail_if_branching(tactic * t, unsigned threshold = 1);

tactic * par(unsigned num, tactic * const * ts);
tactic * par(tactic * t1, tactic * t2);
tactic * par(tactic * t1, tactic * t2, tactic * t3);
tactic * par(tactic * t1, tactic * t2, tactic * t3, tactic * t4);

tactic * par_and_then(unsigned num, tactic * const * ts);
tactic * par_and_then(tactic * t1, tactic * t2);

tactic * try_for(tactic * t, unsigned msecs);
tactic * clean(tactic * t);
tactic * using_params(tactic * t, params_ref const & p);
tactic * annotate_tactic(char const* name, tactic * t);

// Create a tactic that fails if the result returned by probe p is true.
tactic * fail_if(probe * p);
tactic * fail_if_not(probe * p);
// Execute t1 if p returns true, and t2 otherwise
tactic * cond(probe * p, tactic * t1, tactic * t2);
// Alias for cond(p, t, mk_skip_tactic())
tactic * when(probe * p, tactic * t);

// alias for (or-else t skip)
tactic * skip_if_failed(tactic * t);

// Execute the given tactic only if proof production is not enabled.
// If proof production is enabled it is a skip
tactic * if_no_proofs(tactic * t);
tactic * if_no_unsat_cores(tactic * t);
tactic * if_no_models(tactic * t);

