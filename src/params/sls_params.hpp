/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_params.hpp

Abstract:

    Parameters for the Stochastic Local Search Solver.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define SLS_PARAMS(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_)                                                                         \
  UINT_(max_memory,                  "max_memory",                  UINT_MAX, "maximum amount of memory in megabytes")             \
  UINT_(max_restarts,                "max_restarts",                UINT_MAX, "maximum number of restarts")                        \
  UINT_(max_repairs,                 "max_repairs",                 1000,     "maximum number of repairs before restart")          \
  BOOL_(walksat,                     "walksat",                     true,     "use walksat assertion selection (instead of gsat)") \
  BOOL_(walksat_ucb,                 "walksat_ucb",                 true,     "use bandit heuristic for walksat assertion selection (instead of random)") \
  DOUBLE_(walksat_ucb_constant,      "walksat_ucb_constant",        20.0,     "the ucb constant c in the term score + c * f(touched)") \
  BOOL_(walksat_ucb_init,            "walksat_ucb_init",            false,    "initialize total ucb touched to formula size")       \
  DOUBLE_(walksat_ucb_forget,        "walksat_ucb_forget",          1.0,      "scale touched by this factor every base restart interval") \
  DOUBLE_(walksat_ucb_noise,         "walksat_ucb_noise",           0.0002,   "add noise 0 <= 256 * ucb_noise to ucb score for assertion selection") \
  BOOL_(walksat_repick,              "walksat_repick",              true,     "repick assertion if randomizing in local minima")    \
  DOUBLE_(scale_unsat,               "scale_unsat",                 0.5,      "scale score of unsat expressions by this factor")    \
  UINT_(paws_init,                   "paws_init",                   40,       "initial/minimum assertion weights")                 \
  UINT_(paws_sp,                     "paws_sp",                     52,       "smooth assertion weights with probability paws_sp / 1024") \
  UINT_(wp,                          "wp",                          100,      "random walk with probability wp / 1024")            \
  UINT_(vns_mc,                      "vns_mc",                      0,        "in local minima, try Monte Carlo sampling vns_mc many 2-bit-flips per bit") \
  BOOL_(vns_repick,                  "vns_repick",                  false,    "in local minima, try picking a different assertion (only for walksat)") \
  UINT_(restart_base,                "restart_base",                100,      "base restart interval given by moves per run")      \
  BOOL_(restart_init,                "restart_init",                false,    "initialize to 0 or random value (= 1) after restart") \
  BOOL_(early_prune,                 "early_prune",                 true,     "use early pruning for score prediction")            \
  BOOL_(random_offset,               "random_offset",               true,     "use random offset for candidate evaluation")        \
  BOOL_(rescore,                     "rescore",                     true,     "rescore/normalize top-level score every base restart interval") \
  BOOL_(dt_axiomatic,                "dt_axiomatic",                true,     "use axiomatic mode or model reduction for datatype solver") \
  BOOL_(track_unsat,                 "track_unsat",                 false,    "keep a list of unsat assertions as done in SAT - currently disabled internally") \
  UINT_(random_seed,                 "random_seed",                 0,        "random seed")                                        \
  BOOL_(arith_use_lookahead,         "arith_use_lookahead",         true,     "use lookahead solver for NIRA")                      \
  BOOL_(arith_allow_plateau,         "arith_allow_plateau",         false,    "allow plateau moves during NIRA solving")            \
  BOOL_(arith_use_clausal_lookahead, "arith_use_clausal_lookahead", false,    "use clause based lookahead for NIRA")                \
  BOOL_(bv_use_top_level_assertions, "bv_use_top_level_assertions", true,     "use top-level assertions for BV lookahead solver")   \
  BOOL_(bv_use_lookahead,            "bv_use_lookahead",            true,     "use lookahead solver for BV")                        \
  BOOL_(bv_allow_rotation,           "bv_allow_rotation",           true,     "allow model rotation when repairing literal assignment") \
  UINT_(str_update_strategy,         "str_update_strategy",         2,        "string update candidate selection: 0 - single character based update, 1 - subsequence based update, 2 - combined")

Z3_DEFINE_MODULE_PARAMS(sls_params, "sls", SLS_PARAMS, "Stochastic Local Search Solver (invoked by sls-qfbv and sls-smt tactics or enabled by smt.sls.enable=true)");

#undef SLS_PARAMS
