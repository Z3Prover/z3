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

/**
   \brief Name the step \c t: route the keys of the \c tactic module under \c path to it.

   \c path is relative to the \c tactic module, e.g. "qfbv.preamble". updt_params(p)
   passes p to \c t, and also sets <rest> for every key <path>.<rest>:
   - a local entry of p (also written tactic.<path>.<rest>) sets <rest>, unflagged;
   - a global tactic.<path>.<rest> sets <rest>, unflagged, unless a local value for
     <rest> is present.
   The scoped keys stay in the parameters, so nested scopes are more specific. The
   key <path>.enabled, local before global, is read and not passed on: if it is false,
   the scope passes the goal through unchanged, like skip.

   The resulting precedence for a key at a step is: forced value of the author (set_*),
   local scoped, local unscoped, global scoped, global unscoped, author default
   (set_default_*). For forced values to win, place the scope outside the
   using_params of the step: scope_tactic(path, using_params(t, p)).

   collect_param_descrs adds the keys of the tactic module that start with <path>.
   Only the keys declared there can be set by users (local and global settings are
   validated), so a scope routes only the keys its rows declare, <path>.enabled included.

   Scope paths share the namespace of the tactic module with its other keys: a scope
   named "solve_eqs" would take tactic.solve_eqs.max_occs as its key max_occs. Prefix
   paths with the logic, e.g. "qfbv.preamble".

   The tactic language has no scopes. display-tactic shows a scope as what it does
   under the current settings: skip if it is disabled (or (when 0 t), if an enclosing
   using-params has keys that only t declares), else t with the values it routes as
   explicit using-params keys. Run without the scoped settings, the output does what
   the pipeline does with them.
*/
tactic * scope_tactic(char const * path, tactic * t);

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

