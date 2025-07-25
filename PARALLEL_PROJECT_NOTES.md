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

