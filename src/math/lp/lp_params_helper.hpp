/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    lp_params_helper.hpp

Abstract:

    Parameters for the 'lp' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define LP_PARAMS_HELPER_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(dio,                        "dio",                        true,     "use Diophantine equalities") \
  UINT_(dio_branching_period,       "dio_branching_period",       100,      "Period of calling branching on undef in Diophantine handler") \
  BOOL_(dio_cuts_enable_gomory,     "dio_cuts_enable_gomory",     false,    "enable Gomory cuts together with Diophantine cuts, only relevant when dioph_eq is true") \
  UINT_(dio_gomory_enable_period,   "dio_gomory_enable_period",   16,       "number of consecutive unproductive (undef) Diophantine-handler calls after which the controller starts running Gomory cuts and the gcd test alongside dio; a dio conflict resets the count and stops them; set very large to never start them this way so Gomory follows dio_cuts_enable_gomory only") \
  BOOL_(dio_cuts_enable_hnf,        "dio_cuts_enable_hnf",        true,     "enable hnf cuts together with Diophantine cuts, only relevant when dioph_eq is true") \
  BOOL_(dio_ignore_big_nums,        "dio_ignore_big_nums",        true,     "Ignore the terms with big numbers in the Diophantine handler, only relevant when dioph_eq is true") \
  UINT_(dio_calls_period,           "dio_calls_period",           1,        "Period of calling the Diophantine handler in the final_check()") \
  UINT_(dio_calls_period_decrease,  "dio_calls_period_decrease",  2,        "Amount by which dio_calls_period is decreased on each final_check() call where the Diophantine handler is not triggered, until it returns to its initial value") \
  BOOL_(dio_run_gcd,                "dio_run_gcd",                false,    "Run the GCD heuristic if dio is on, if dio is disabled the option is not used") \
  UINT_(dio_undo_max_work,          "dio_undo_max_work",          1000000,  "work budget, in machine words, for eliminating the columns of the retired terms from the certificate matrix of the Diophantine handler; when a scope pop exceeds it the Diophantine state is discarded and rebuilt lazily on the next check instead of being updated incrementally; 0 means no budget") \
  BOOL_(lcube,                      "lcube",                      true,     "use the largest cube test for integer feasibility") \
  UINT_(lcube_flips,                "lcube_flips",                16,       "maximal number of coordinate flips when repairing the rounded largest cube center, only relevant when lcube is true") \
  UINT_(int_hammer_period,          "int_hammer_period",          4,        "period (in final_check calls) for the integer cut/cube heuristics (find_cube, hnf, gomory); a smaller value calls them more often") \
  BOOL_(random_hammers,             "random_hammers",             true,     "draw the periodic integer heuristic gates (find_cube, lcube, hnf, gomory, dio) at random with the same 1/period rate instead of a deterministic every-k-th-call modulus")

Z3_DEFINE_MODULE_PARAMS(lp_params_helper, "lp", LP_PARAMS_HELPER_LIST);

/*
   REG_MODULE_PARAMS('lp', 'lp_params_helper::collect_param_descrs')
   REG_MODULE_DESCRIPTION('lp', 'linear programming parameters')
*/

#undef LP_PARAMS_HELPER_LIST
