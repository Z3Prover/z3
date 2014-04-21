/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sls_compilation_constants.h

Abstract:

    Stochastic Local Search (SLS) compilation constants

Author:

    Christoph (cwinter) 2014-03-19

Notes:

    This file should go away completely once we have evaluated all options.

--*/

#ifndef _SLS_COMPILATION_SETTINGS_H_
#define _SLS_COMPILATION_SETTINGS_H_

// shall we use addition/subtraction?
#define _USE_ADDSUB_ 0

// should we use unsat-structures as done in SLS 4 SAT instead for random or bfs selection?
#define _REAL_RS_ 0

// shall we use early pruning for incremental update?
#define _EARLY_PRUNE_ 1

#endif