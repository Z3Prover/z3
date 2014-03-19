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
// which unsatisfied assertion is selected? only works with _FOCUS_ > 0
// 0 = random, 1 = #moves, 2 = assertion with min score, 3 = assertion with max score
#define _BFS_ 0

// how many terms are considered for variable selection?
// 0 = all terms (GSAT), 1 = only one top level assertion (WSAT), 2 = only one bottom level atom
#define _FOCUS_ 1

// probability of choosing the same assertion again in the next step
#define _PERC_STICKY_ 0

// do we use dirty unit propagation to get rid of nested top level assertions?
#define _DIRTY_UP_ 0

// do we use restarts?
// 0 = no, 1 = use #moves, 2 = use #plateaus, 3 = use time
#define _RESTARTS_ 3
// limit of moves/plateaus/seconds until first restart occurs
#define _RESTART_LIMIT_ 10
// 0 = initialize with all zero, 1 initialize with random value
#define _RESTART_INIT_ 0
// 0 = even intervals, 1 = pseudo luby, 2 = real luby, 3 = armin, 4 = rapid
#define _RESTART_SCHEME_ 1
// base value c for armin restart scheme using c^inner - only applies for _RESTART_SCHEME_ 3
#define _RESTART_CONST_ARMIN_ 3.0

// timelimit
#define _TIMELIMIT_ 3600

// should score of conjunctions be calculated by average rather than max?
#define _SCORE_AND_AVG_ 0

// should score of discunctions be calculated by multiplication of the inverse score rather than min?
#define _SCORE_OR_MUL_ 0

// do we use some kind of variable neighbourhood-search?
// 0 = no, 1 = only consider flipping bits if no better score can be obtained otherwise, 2 = only consider flipping bits until a better score can be obtained
#define _VNS_ 0

// do we reduce the score of unsatisfied literals?
// 0 = no
// 1 = yes, by multiplying it with some factor
// 2 = yes, by squaring it
// 3 = yes, by setting it to zero
// 4 = by progessively increasing weight (_TIMELIMIT_ needs to be set appropriately!)
#define _WEIGHT_DIST_ 1

// the factor used for _WEIGHT_DIST_ = 1
#define _WEIGHT_DIST_FACTOR_ 0.25

// shall we toggle the weight after each restart?
#define _WEIGHT_TOGGLE_ 0

// do we use intensification steps in local minima? if so, how many?
#define _INTENSIFICATION_ 0
#define _INTENSIFICATION_TRIES_ 0

// what is the percentage of random moves in plateaus (instead of full randomization)?
#define _PERC_PLATEAU_MOVES_ 0

// shall we repick clause when randomizing in a plateau or use the current one?
#define _REPICK_ 1

// do we use some UCT-like scheme for assertion-selection? overrides _BFS_
#define _UCT_ 1

// how much diversification is used in the UCT-scheme?
#define _UCT_CONSTANT_ 10.0

// is uct clause selection probabilistic similar to variable selection in sparrow?
// 0 = no, 1 = yes, use uct-value, 2 = yes, use score-value (_UCT_CONSTANT_ = 0.0) with squared score
#define _PROBABILISTIC_UCT_ 0

// additive constants for probabilistic uct > 0
#define _UCT_EPS_ 0.0001

// shall we reset _UCT_ touched values after restart?
#define _UCT_RESET_ 0

// how shall we initialize the _UCT_ total touched counter?
// 0 = initialize with one, 1 = initialize with number of assertions
#define _UCT_INIT_ 1

// shall we use addition/subtraction?
#define _USE_ADDSUB_ 1

// shall we try multilication and division by 2?
#define _USE_MUL2DIV2_ 0

// shall we try multiplication by 3?
#define _USE_MUL3_ 0

// shall we try unary minus (= inverting and incrementing)
#define _USE_UNARY_MINUS_ 0

// is random selection for assertions uniform? only works with _BFS_ = _UCT_ = 0
#define _UNIFORM_RANDOM_ 0

// should we use unsat-structures as done in SLS 4 SAT instead for random or bfs selection?
#define _REAL_RS_ 0
#define _REAL_PBFS_ 0

// how many bits do we neglect in each iteration?
#define _SKIP_BITS_ 0

// when randomizing local, what is the probability for changing a single bit?
// 0 = use standard scheme and pick a new value at random (= 50), otherwise the value (as int) gives the percentage
#define _PERC_CHANGE_ 0

// do we use random steps for noise?
// 0 = no, 1 = randomize local, 2 = make random move
#define _TYPE_RSTEP_ 0

// with what probability _PERM_STEP_/1000 will the random step happen? 
#define _PERM_RSTEP_ 0

// shall we use early pruning for incremental update?
#define _EARLY_PRUNE_ 1

// shall we use caching for top_score?
#define _CACHE_TOP_SCORE_ 1


#if ((_BFS_ > 0) + (_UCT_ > 0) + _UNIFORM_RANDOM_ + _REAL_RS_ + _REAL_PBFS_ > 1)
InvalidConfiguration;
#endif
#if (_PROBABILISTIC_UCT_ && !_UCT_)
InvalidConfiguration;
#endif
#if (_PERM_RSTEP_ && !_TYPE_RSTEP_)
InvalidConfiguration;
#endif
#if (_PERC_CHANGE_ == 50)
InvalidConfiguration;
#endif
#if (_PERC_STICKY_ && !_FOCUS_)
InvalidConfiguration;
#endif