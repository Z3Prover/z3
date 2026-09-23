/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_simplifier_params.hpp

Abstract:

    Parameters for the 'sat' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define SAT_SIMPLIFIER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(bce,                           "bce",                           false,      "eliminate blocked clauses") \
  BOOL_(abce,                          "abce",                          false,      "eliminate blocked clauses using asymmetric literals") \
  BOOL_(cce,                           "cce",                           false,      "eliminate covered clauses") \
  BOOL_(ate,                           "ate",                           true,       "asymmetric tautology elimination") \
  BOOL_(acce,                          "acce",                          false,      "eliminate covered clauses using asymmetric added literals") \
  UINT_(bce_at,                        "bce_at",                        2,          "eliminate blocked clauses only once at the given simplification round") \
  BOOL_(bca,                           "bca",                           false,      "blocked clause addition - add blocked binary clauses") \
  UINT_(bce_delay,                     "bce_delay",                     2,          "delay eliminate blocked clauses until simplification round") \
  BOOL_(retain_blocked_clauses,        "retain_blocked_clauses",        true,       "retain blocked clauses as lemmas") \
  UINT_(blocked_clause_limit,          "blocked_clause_limit",          100000000,  "maximum number of literals visited during blocked clause elimination") \
  BOOL_(override_incremental,          "override_incremental",          false,      "override incremental safety gaps. Enable elimination of blocked clauses and variables even if solver is reused") \
  UINT_(resolution_limit,              "resolution.limit",              500000000,  "approx. maximum number of literals visited during variable elimination") \
  UINT_(resolution_occ_cutoff,         "resolution.occ_cutoff",         10,         "first cutoff (on number of positive/negative occurrences) for Boolean variable elimination") \
  UINT_(resolution_occ_cutoff_range1,  "resolution.occ_cutoff_range1",  8,          "second cutoff (number of positive/negative occurrences) for Boolean variable elimination, for problems containing less than res_cls_cutoff1 clauses") \
  UINT_(resolution_occ_cutoff_range2,  "resolution.occ_cutoff_range2",  5,          "second cutoff (number of positive/negative occurrences) for Boolean variable elimination, for problems containing more than res_cls_cutoff1 and less than res_cls_cutoff2") \
  UINT_(resolution_occ_cutoff_range3,  "resolution.occ_cutoff_range3",  3,          "second cutoff (number of positive/negative occurrences) for Boolean variable elimination, for problems containing more than res_cls_cutoff2") \
  UINT_(resolution_lit_cutoff_range1,  "resolution.lit_cutoff_range1",  700,        "second cutoff (total number of literals) for Boolean variable elimination, for problems containing less than res_cls_cutoff1 clauses") \
  UINT_(resolution_lit_cutoff_range2,  "resolution.lit_cutoff_range2",  400,        "second cutoff (total number of literals) for Boolean variable elimination, for problems containing more than res_cls_cutoff1 and less than res_cls_cutoff2") \
  UINT_(resolution_lit_cutoff_range3,  "resolution.lit_cutoff_range3",  300,        "second cutoff (total number of literals) for Boolean variable elimination, for problems containing more than res_cls_cutoff2") \
  UINT_(resolution_cls_cutoff1,        "resolution.cls_cutoff1",        100000000,  "limit1 - total number of problems clauses for the second cutoff of Boolean variable elimination") \
  UINT_(resolution_cls_cutoff2,        "resolution.cls_cutoff2",        700000000,  "limit2 - total number of problems clauses for the second cutoff of Boolean variable elimination") \
  BOOL_(elim_vars,                     "elim_vars",                     true,       "enable variable elimination using resolution during simplification") \
  BOOL_(probing,                       "probing",                       true,       "apply failed literal detection during simplification") \
  UINT_(probing_limit,                 "probing_limit",                 5000000,    "limit to the number of probe calls") \
  BOOL_(probing_cache,                 "probing_cache",                 true,       "add binary literals as lemmas") \
  UINT_(probing_cache_limit,           "probing_cache_limit",           1024,       "cache binaries unless overall memory usage exceeds cache limit") \
  BOOL_(probing_binary,                "probing_binary",                true,       "probe binary clauses") \
  BOOL_(subsumption,                   "subsumption",                   true,       "eliminate subsumed clauses") \
  UINT_(subsumption_limit,             "subsumption.limit",             100000000,  "approx. maximum number of literals visited during subsumption (and subsumption resolution)")

Z3_DEFINE_MODULE_PARAMS(sat_simplifier_params, "sat", SAT_SIMPLIFIER_PARAMS_LIST, nullptr);

#undef SAT_SIMPLIFIER_PARAMS_LIST
