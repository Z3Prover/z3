# Parallel project notes



We track notes for updates to 
[smt/parallel.cpp](https://github.com/Z3Prover/z3/blob/master/src/smt/smt_parallel.cpp) 
and possibly 
[solver/parallel_tactic.cpp](https://github.com/Z3Prover/z3/blob/master/src/solver/parallel_tactical.cpp).





## Variable selection heuristics



* Lookahead solvers:
  * lookahead in the smt directory performs a simplistic lookahead search using unit propagation.
  * lookahead in the sat directory uses custom lookahead solver based on MARCH. March is described in Handbook of SAT and Knuth volumne 4.
  * They both proxy on a cost model where the most useful variable to branch on is the one that _minimizes_ the set of new clauses maximally
  through unit propagation. In other words, if a literal _p_ is set to true, and _p_ occurs in clause $\neg p \vee q \vee r$, then it results in 
  reducing the clause from size 3 to 2 (because $\neg p$ will be false after propagating _p_).
  * Selected references: SAT handbook, Knuth Volumne 4, Marijn's March solver on github, [implementation of march in z3](https://github.com/Z3Prover/z3/blob/master/src/sat/sat_lookahead.cpp)
* VSIDS:
  * As referenced in Matteo and Antti's solvers. 
  * Variable activity is a proxy for how useful it is to case split on a variable during search. Variables with a higher VSIDS are split first.
  * VSIDS is updated dynamically during search. It was introduced in the paper with Moscovitz, Malik, et al in early 2000s. A good overview is in Armin's tutorial slides (also in my overview of SMT). 
  * VSIDS does not keep track of variable phases (if the variable was set to true or false).
  * Selected refernces [DAC 2001](https://www.princeton.edu/~chaff/publication/DAC2001v56.pdf) and [Biere Tutorial, slide 64 on Variable Scoring Schemes](https://alexeyignatiev.github.io/ssa-school-2019/slides/ab-satsmtar19-slides.pdf)
* Proof prefix:
  * Collect the literals that occur in learned clauses. Count their occurrences based on polarity. This gets tracked in a weighted score.
  * The weight function can be formulated to take into account clause sizes.
  * The score assignment may also decay similar to VSIDS. 
  * We could also use a doubly linked list for literals used in conflicts and keep reinsert literals into the list when they are used. This would be a "Variable move to front" (VMTF) variant.
  * Selected references: [Battleman et al](https://www.cs.cmu.edu/~mheule/publications/proofix-SAT25.pdf)
* From local search:
  * Note also that local search solvers can be used to assign variable branch priorities. 
  * We are not going to directly run a local search solver in the mix up front, but let us consider this heuristic for completeness.
  * The heuristic is documented in Biere and Cai's journal paper on integrating local search for CDCL. 
  * Roughly, it considers clauses that move from the UNSAT set to the SAT set of clauses. It then keeps track of the literals involved.
  * Selected references: [Cai et al](https://www.jair.org/index.php/jair/article/download/13666/26833/)
* Assignment trails:
  * We could also consider the assignments to variables during search. 
  * Variables that are always assigned to the same truth value could be considered to be safe to assign that truth value. 
  * The cubes resulting from such variables might be a direction towards finding satisfying solutions.
  * Selected references: [Alex and Vadim](https://link.springer.com/chapter/10.1007/978-3-319-94144-8_7) and most recently [Robin et al](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2024.9).
  

## Algorithms

This section considers various possible algorithms. 
In the following, $F$ refers to the original goal, $T$ is the number of CPU cores or CPU threads.

### Base algorithm

The existing algorithm in <b>smt_parallel</b> is as follows:

1. Run a solver on $F$ with a bounded number of conflicts.
2. If the result is SAT/UNSAT, or UNKNOWN with an interrupt or timeout, return. If the maximal number of conflicts were reached continue.
3. Spawn $T$ solvers on $F$ with a bounded number of conflicts, wait until a thread returns UNSAT/SAT or all threads have reached a maximal number of conflicts.
4. Perform a similar check as in 2.
5. Share unit literals learned by each thread.
6. Compute unit cubes for each thread $T$.
7. Spawn $T$ solvers with $F \wedge \ell$, where $\ell$ is a unit literal determined by lookahead function in each thread.
8. Perform a similar check as in 2. But note that a thread can be UNSAT because the unit cube $\ell$ contradicted $F$. In this case learn the unit literal $\neg \ell$.
9. Shared unit literals learned by each thread, increase the maximal number of conflicts, go to 3.

### Algorithm Variants

* Instead of using lookahead solving to find unit cubes use the proof-prefix based scoring function.
* Instead of using independent unit cubes, perform a systematic (where systematic can mean many things) cube and conquer strategy.
* Spawn some threads to work in "SAT" mode, tuning to find models instead of short resolution proofs.
* Change the synchronization barrier discipline.
* [Future] Include in-processing 

### Cube and Conquer strategy

We could maintain a global decomposition of the search space by maintaing a list of _cubes_.
Initially, the list of cubes has just one element, the cube with no literals $[ [] ]$.
By using a list of cubes instead of a _set_ of cubes we can refer to an ordering.
For example, cubes can be ordered by a suffix traversal of the _cube tree_ (the tree formed by
case splitting on the first literal, children of the _true_ branch are the cubes where the first
literal is true, children of the _false_ branch are the cubes where the first literal is false).

The main question is going to be how the cube decomposition is created.

#### Static cubing
We can aim for a static cube strategy that uses a few initial (concurrent) probes to find cube literals.
This strategy would be a parallel implementaiton of proof-prefix approach. The computed cubes are inserted
into the list of cubes and the list is consumed by a second round.

#### Growing cubes on demand
Based on experiences with cubing so far, there is high variance in how easy cubes are to solve.
Some cubes will be harder than others to solve. For hard cubes, it is tempting to develop a recursive
cubing strategy. Ideally, a recursive cubing strategy is symmetric to top-level cubing.

* The solver would have to identify hard cubes vs. easy cubes.
* It would have to know when to stop working on a hard cube and replace it in the list of cubes by
  a new list of sub-cubes.

* Ideally, we don't need any static cubing and cubing is grown on demand while all threads are utilized.
  * If we spawn $T$ threads to initially work with empty cubes, we could extract up to $T$ indepenent cubes
    by examining the proof-prefix of their traces. This can form the basis for the first, up to $2^T$ cubes.
  * After a round of solving with each thread churning on some cubes, we may obtain more proof-prefixes from
    _hard_ cubes. It is not obvious that we want to share cubes from different proof prefixes at this point.
    But a starting point is to split a hard cube into two by using the proof-prefix from attempting to solve it.    
  * Suppose we take the proof-prefix sampling algorithm at heart: It says to start with some initial cube prefix
    and then sample for other cube literals. If we translate it to the case where multiple cubes are being processed
    in parallel, then an analogy is to share candidates for new cube literals among cubes that are close to each-other.
    For example, if thread $t_1$ processes cube $a, b, c$ and $t_2$ processes $a,b, \neg c$. They are close. They are only
    separated by Hamming distance 1. If $t_1$ finds cube literal $d$ and $t_2$ finds cube literal $e$, we could consider the cubes
    $a, b, c, d, e$, and $a, b, c, d, \neg e$, $\ldots$, $a, b, \neg c, \neg d, \neg e$.

#### Representing cubes implicitly

We can represent a list of cubes by using intervals and only represent start and end-points of the intervals.

#### Batching
Threads can work on more than one cube in a batch.

### Synchronization

* The first thread to time out or finish could kill other threads instead of joining on all threads to finish.
* Instead of synchronization barriers have threads continue concurrently without terminating. They synchronize on signals and new units. This is trickier to implement, but in some guises accomplished in [sat/sat_parallel.cpp](https://github.com/Z3Prover/z3/blob/master/src/sat/sat_parallel.cpp)


## Parameter tuning

The idea is to have parallel threads try out different parameter settings and search the parameter space of an optimal parameter setting.

Let us assume that there is a set of tunable parameters $P$. The set comprises of a set of named parameters with initial values.
$P = \{ (p_1, v_1), \ldots, (p_n, v_n) \}$.
With each parameter associate a set of mutation functions $+=, -=, *=$, such as increment, decrement, scale a parameter by a non-negative multiplier (which can be less than 1).
We will initialize a search space of parameter settings by parameters, values and mutation functions that have assigned reward values. The reward value is incremented
if a parameter mutation step results in an improvement, and decremented if a mutation step degrades performance.
$P = \{ (p_1, v_1, \{ (r_{11}, m_{11}), \ldots, (r_{1k_1}, m_{1k_1}) \}), \ldots, (p_n, v_n, \{ (r_{n1}, m_{n1}), \ldots, (r_{nk_n}, m_{nk_n})\}) \}$.
The initial values of reward functions is fixed (to 1) and the initial values of parameters are the defaults.

* The batch manager maintains a set of candidate parameters $CP = \{ (P_1, r_1), \ldots, (P_n, r_n) \}$.
* A worker thread picks up a parameter $P_i$ from $CP$ from the batch manager.
* It picks one or more parameter settings within $P_i$ whose mutation function have non-zero reward functions and applies a mutation.
* It then runs with a batch of cubes.
* It measures the reward for the new parameter setting based in number of cubes, cube depth, number of timeouts, and completions with number of conflicts.
* If the new reward is an improvement over $(P_i, r_i)$ it inserts the new parameter setting $(P_i', r_i')$ into the batch manager.
* The batch manager discards the worst parameter settings keeping the top $K$ ($K = 5$) parameter settings.

When picking among mutation steps with reward functions use a weighted sampling algorithm.
Weighted sampling works as follows: You are given a set of items with weights $(i_1, w_1), \ldots, (i_k, w_k)$.
Add $w = \sum_j w_j$. Pick a random number $w_0$ in the range $0\ldots w$.
Then you pick item $i_n$ such that $n$ is the smallest index with $\sum_{j = 1}^n w_j \geq w_0$.

SMT parameters that could be tuned:

<pre>

  arith.bprop_on_pivoted_rows (bool) (default: true)
  arith.branch_cut_ratio (unsigned int) (default: 2)
  arith.eager_eq_axioms (bool) (default: true)
  arith.enable_hnf (bool) (default: true)
  arith.greatest_error_pivot (bool) (default: false)
  arith.int_eq_branch (bool) (default: false)
  arith.min (bool) (default: false)
  arith.nl.branching (bool) (default: true)
  arith.nl.cross_nested (bool) (default: true)
  arith.nl.delay (unsigned int) (default: 10)
  arith.nl.expensive_patching (bool) (default: false)
  arith.nl.expp (bool) (default: false)
  arith.nl.gr_q (unsigned int) (default: 10)
  arith.nl.grobner (bool) (default: true)
  arith.nl.grobner_cnfl_to_report (unsigned int) (default: 1)
  arith.nl.grobner_eqs_growth (unsigned int) (default: 10)
  arith.nl.grobner_expr_degree_growth (unsigned int) (default: 2)
  arith.nl.grobner_expr_size_growth (unsigned int) (default: 2)
  arith.nl.grobner_frequency (unsigned int) (default: 4)
  arith.nl.grobner_max_simplified (unsigned int) (default: 10000)
  arith.nl.grobner_row_length_limit (unsigned int) (default: 10)
  arith.nl.grobner_subs_fixed (unsigned int) (default: 1)
  arith.nl.horner (bool) (default: true)
  arith.nl.horner_frequency (unsigned int) (default: 4)
  arith.nl.horner_row_length_limit (unsigned int) (default: 10)
  arith.nl.horner_subs_fixed (unsigned int) (default: 2)
  arith.nl.nra (bool) (default: true)
  arith.nl.optimize_bounds (bool) (default: true)
  arith.nl.order (bool) (default: true)
  arith.nl.propagate_linear_monomials (bool) (default: true)
  arith.nl.rounds (unsigned int) (default: 1024)
  arith.nl.tangents (bool) (default: true)
  arith.propagate_eqs (bool) (default: true)
  arith.propagation_mode (unsigned int) (default: 1)
  arith.random_initial_value (bool) (default: false)
  arith.rep_freq (unsigned int) (default: 0)
  arith.simplex_strategy (unsigned int) (default: 0)
  dack (unsigned int) (default: 1)
  dack.eq (bool) (default: false)
  dack.factor (double) (default: 0.1)
  dack.gc (unsigned int) (default: 2000)
  dack.gc_inv_decay (double) (default: 0.8)
  dack.threshold (unsigned int) (default: 10)
  delay_units (bool) (default: false)
  delay_units_threshold (unsigned int) (default: 32)
  dt_lazy_splits (unsigned int) (default: 1)
  lemma_gc_strategy (unsigned int) (default: 0)
  phase_caching_off (unsigned int) (default: 100)
  phase_caching_on (unsigned int) (default: 400)
  phase_selection (unsigned int) (default: 3)
  qi.eager_threshold (double) (default: 10.0)
  qi.lazy_threshold (double) (default: 20.0)
  qi.quick_checker (unsigned int) (default: 0)
  relevancy (unsigned int) (default: 2)
  restart_factor (double) (default: 1.1)
  restart_strategy (unsigned int) (default: 1)
  seq.max_unfolding (unsigned int) (default: 1000000000)
  seq.min_unfolding (unsigned int) (default: 1)
  seq.split_w_len (bool) (default: true)
</pre>


