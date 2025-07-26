# Parallel project notes



We track notes for updates to smt/parallel.cpp and possibly solver/parallel\_tactic.cpp





## Variable selection heuristics



* Lookahead solvers:
  * lookahead in the smt directory performs a simplistic lookahead search using unit propagation.
  * lookahead in the sat directory uses custom lookahead solver.
  They both proxy on a cost model where the most useful variable to branch on is the one that _minimizes_ the set of new clauses maximally
  through unit propagation. In other words, if a literal _p_ is set to true, and _p_ occurs in clause $\neg p \vee q \vee r$, then it results in 
  reducing the clause from size 3 to 2 (because $\neg p$ will be false after propagating _p_).
* VSIDS:
  * As referenced in Matteo and Antti's solvers. 
  * Variable activity is a proxy for how useful it is to case split on a variable during search. Variables with a higher VSIDS are split first.
  * VSIDS is updated dynamically during search. It was introduced in the paper with Moscovitz, Malik, et al in early 2000s. A good overview is in Armin's tutorial slides (also in my overview of SMT). 
  * VSIDS does not keep track of variable phases (if the variable was set to true or false).
* Proof prefix:
  * Collect the literals that occur in learned clauses. Count their occurrences based on polarity. This gets tracked in a weighted score.
  * The weight function can be formulated to take into account clause sizes.
  * The score assignment may also decay similar to VSIDS. 
  * We could also use a doubly linked list for literals used in conflicts and keep reinsert literals into the list when they are used. This would be a "Variable move to front" (VMTF) variant.
* From local search:
  * Note also that local search solvers can be used to assign variable branch priorities. 
  * We are not going to directly run a local search solver in the mix up front, but let us consider this heuristic for completeness.
  * The heuristic is documented in Biere and Cai's journal paper on integrating local search for CDCL. 
  * Roughly, it considers clauses that move from the UNSAT set to the SAT set of clauses. It then keeps track of the literals involved.
* Assignment trails:
  * We could also consider the assignments to variables during search. 
  * Variables that are always assigned to the same truth value could be considered to be safe to assign that truth value. 
  * The cubes resulting from such variables might be a direction towards finding satisfying solutions.
  

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
* Instead of synchronization barriers have threads continue concurrently without terminating. They synchronize on signals and new units. This is trickier to implement, but in some guises accomplished in sat/sat_parallel.cpp.
