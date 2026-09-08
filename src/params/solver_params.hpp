/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    solver_params.hpp

Abstract:

    Parameters for the 'solver' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define SOLVER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  SYMBOL_(smtlib2_log,             "smtlib2_log",             "",        "file to save solver interaction") \
  SYMBOL_(cancel_backup_file,      "cancel_backup_file",      "",        "file to save partial search state if search is canceled") \
  UINT_  (timeout,                 "timeout",                 UINT_MAX,  "timeout on the solver object; overwrites a global timeout") \
  BOOL_  (lemmas2console,          "lemmas2console",          false,     "print lemmas during search") \
  BOOL_  (instantiations2console,  "instantiations2console",  false,     "print quantifier instantiations to the console") \
  BOOL_  (axioms2files,            "axioms2files",            false,     "print negated theory axioms to separate files during search") \
  BOOL_  (slice,                   "slice",                   false,     "use slice solver that filters assertions to use symbols occuring in @query formulas") \
  SYMBOL_(proof_log,               "proof.log",               "",        "log clause proof trail into a file") \
  BOOL_  (proof_check,             "proof.check",             true,      "check proof logs") \
  BOOL_  (proof_check_rup,         "proof.check_rup",         true,      "check proof RUP inference in proof logs") \
  BOOL_  (proof_save,              "proof.save",              false,     "save proof log into a proof object that can be extracted using (get-proof)") \
  BOOL_  (proof_trim,              "proof.trim",              false,     "trim and save proof into a proof object that an be extracted using (get-proof)")

Z3_DEFINE_MODULE_PARAMS(solver_params, "solver", SOLVER_PARAMS_LIST);

/*
   REG_MODULE_PARAMS('solver', 'solver_params::collect_param_descrs')
   REG_MODULE_DESCRIPTION('solver', 'solver parameters')
*/

#undef SOLVER_PARAMS_LIST
