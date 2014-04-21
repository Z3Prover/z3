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

// how many terms are considered for variable selection?
// 0 = all terms (GSAT), 1 = only one top level assertion (WSAT)
#define _FOCUS_ 1

// shall we use additive weighting scheme?
#define _PAWS_ 5
#define _PAWS_INIT_ 40

// do we use restarts?
// 0 = no, 1 = use #moves, 2 = use #plateaus, 3 = use time
#define _RESTARTS_ 1
// limit of moves/plateaus/seconds until first restart occurs
#define _RESTART_LIMIT_ 100
//// 0 = initialize with all zero, 1 initialize with random value
#define _RESTART_INIT_ 0
// 0 = even intervals, 1 = pseudo luby, 2 = real luby, 3 = armin, 4 = rapid, 5 = minisat
#define _RESTART_SCHEME_ 1
// base value c for armin restart scheme using c^inner - only applies for _RESTART_SCHEME_ 3
#define _RESTART_CONST_ARMIN_ 2.0

// timelimit
#define _TIMELIMIT_ 3600

// should score of conjunctions be calculated by average rather than max?
#define _SCORE_AND_AVG_ 0

// shall we check 2-bit flips in plateaus using Monte Carlo?
#define _VNS_MC_ 0

// how many 2-bit flips shall we try per bit?
#define _VNS_MC_TRIES_ 1

// shall we check another assertion if no improving step was found in the first one?
#define _VNS_REPICK_ 0

// do we reduce the score of unsatisfied literals?
// 0 = no, 1 = yes, by multiplying it with some factor
#define _WEIGHT_DIST_ 1

// the factor used for _WEIGHT_DIST_ = 1
#define _WEIGHT_DIST_FACTOR_ 0.5

// shall we repick assertion when randomizing in a plateau or use the current one?
// 0 = use old one, 1 = repick according to usual scheme, 2 = repick randomly and force different one
#define _REPICK_ 1

// do we use some UCT-like scheme for assertion-selection? overrides _BFS_
#define _UCT_ 1

// how much diversification is used in the UCT-scheme?
#define _UCT_CONSTANT_ 20.0

// how shall we initialize the _UCT_ total touched counter?
// 0 = initialize with one, 1 = initialize with number of assertions
#define _UCT_INIT_ 0

// do we gradually reduce the touched values of _UCT_?
#define _UCT_FORGET_ 0
#define _UCT_FORGET_FACTOR_ 0.9

// shall we use addition/subtraction?
#define _USE_ADDSUB_ 1

// should we use unsat-structures as done in SLS 4 SAT instead for random or bfs selection?
#define _REAL_RS_ 0

// with what probability _PERM_STEP_/1000 will the random step happen? 
#define _PERM_RSTEP_ 0

// shall we use early pruning for incremental update?
#define _EARLY_PRUNE_ 1

// shall we use caching for top_score?
#define _CACHE_TOP_SCORE_ 1

#if ((_UCT_ > 0) + _REAL_RS_ > 1)
InvalidConfiguration;
#endif

#endif