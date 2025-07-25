# Parallel project notes



We track notes for updates to smt\_parallel.cpp and possibly solver/parallel\_tactic.cpp





## Variable selection heuristics



* Lookahead solvers:
  * lookahead in the smt directory performs a simplistic lookahead search using unit propagation.
  * lookahead in the sat directory uses custom lookahead solver.
  They both proxy on a cost model where the most useful variable to branch on is the one that \_minimizes\_ the set of new clauses maximally
  through unit propagation. In other words, if a literal \_p\_ is set to true, and \_p\_ occurs in clause $\\neg p \\vee q \\vee r$, then it results in 
  reducing the clause from size 3 to 2 (because $\\neg p$ will be false after propagating \_p\_).
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
8. Perform a similar check as in 2.
9. Shared unit literals learned by each thread, increase the maximal number of conflicts, go to 3.

### Algorithm Variants

* Instead of using lookahead solving to find unit cubes use the proof-prefix based scoring function.
* Instead of using independent unit cubes, perform a systematic (where systematic can mean many things) cube and conquer strategy.
* Change the synchronization barrier discipline.
* [Future] Include in-processing 

