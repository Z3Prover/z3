/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    parallel_params.hpp

Abstract:

    Parameters for the 'parallel' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define PARALLEL_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_  (enable,                       "enable",                       false,     "enable parallel solver by default on selected tactics (for QF_BV)") \
  UINT_  (threads_max,                  "threads.max",                  10000,     "caps maximal number of threads below the number of processors") \
  UINT_  (num_bb_threads,               "num_bb_threads",               2,         "run Janota-style chunking backbone worker threads; default is 2 (negative and positive mode), supported values are 0 (off), 1 (negative mode only) or 2 (negative and positive mode)") \
  BOOL_  (core_minimize,                "core_minimize",                true,      "minimize unsat cores used for parallel cube backtracking") \
  BOOL_  (ablate_backtracking,          "ablate_backtracking",          false,     "ablation: pass entire cube as core instead of unsat core during backtracking") \
  BOOL_  (cube_lookahead,               "cube.lookahead",               false,     "use lookahead cubing in the parallel solver; when false, use VSIDS activity to select one split literal") \
  UINT_  (conquer_batch_size,           "conquer.batch_size",           100,       "number of cubes to batch together for fast conquer") \
  UINT_  (conquer_restart_max,          "conquer.restart.max",          5,         "maximal number of restarts during conquer phase") \
  UINT_  (conquer_delay,                "conquer.delay",                10,        "delay of cubes until applying conquer") \
  UINT_  (conquer_backtrack_frequency,  "conquer.backtrack_frequency",  10,        "frequency to apply core minimization during conquer") \
  DOUBLE_(simplify_exp,                 "simplify.exp",                 1,         "restart and inprocess max is multiplied by simplify.exp ^ depth") \
  UINT_  (simplify_max_conflicts,       "simplify.max_conflicts",       UINT_MAX,  "maximal number of conflicts during simplification phase") \
  UINT_  (simplify_restart_max,         "simplify.restart.max",         5000,      "maximal number of restarts during simplification phase") \
  UINT_  (simplify_inprocess_max,       "simplify.inprocess.max",       2,         "maximal number of inprocessing steps during simplification")

Z3_DEFINE_MODULE_PARAMS(parallel_params, "parallel", PARALLEL_PARAMS_LIST);

/*
   REG_MODULE_PARAMS('parallel', 'parallel_params::collect_param_descrs')
   REG_MODULE_DESCRIPTION('parallel', 'parameters for parallel solver')
*/

#undef PARALLEL_PARAMS_LIST
