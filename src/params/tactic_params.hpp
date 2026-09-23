/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    tactic_params.hpp

Abstract:

    Parameters for the 'tactic' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define TACTIC_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_  (solve_eqs_context_solve,       "solve_eqs.context_solve",       true,      "solve equalities within disjunctions.") \
  BOOL_  (solve_eqs_theory_solver,       "solve_eqs.theory_solver",       true,      "use theory solvers.") \
  BOOL_  (solve_eqs_ite_solver,          "solve_eqs.ite_solver",          true,      "use if-then-else solvers.") \
  UINT_  (solve_eqs_max_occs,            "solve_eqs.max_occs",            UINT_MAX,  "maximum number of occurrences for considering a variable for gaussian eliminations.") \
  UINT_  (blast_term_ite_max_inflation,  "blast_term_ite.max_inflation",  UINT_MAX,  "multiplicative factor of initial term size.") \
  UINT_  (blast_term_ite_max_steps,      "blast_term_ite.max_steps",      UINT_MAX,  "maximal number of steps allowed for tactic.") \
  UINT_  (propagate_values_max_rounds,   "propagate_values.max_rounds",   4,         "maximal number of rounds to propagate values.") \
  UINT_  (lia2card_max_range,            "lia2card.max_range",            100,       "maximal range of integers to compilation into Booleans") \
  UINT_  (lia2card_max_ite_nesting,      "lia2card.max_ite_nesting",      4,         "maximal nesting depth for ite expressions to be compiled into PB constraints") \
  UINT_  (randomizer_seed,               "randomizer.seed",               0,         "seed for randomizer pre-processor") \
  SYMBOL_(default_tactic,                "default_tactic",                "",        "overwrite default tactic in strategic solver")

Z3_DEFINE_MODULE_PARAMS(tactic_params, "tactic", TACTIC_PARAMS_LIST, "tactic parameters");

#undef TACTIC_PARAMS_LIST
