# Parallel MaxSAT / Parallel SMT research notes

**Prepared:** 2026-08-13 (sources and local Z3 checkout checked on this date)
**Purpose:** design evidence for the Python prototype. This note is research/design evidence, not a claim that the prototype is already implemented or evaluated.

## Executive summary

MaxSAT minimizes the total weight of violated *soft propositional clauses* while satisfying hard clauses; MaxSMT generalizes the soft constraints and hard theory to SMT formulas (for example, linear arithmetic or bit-vectors). The useful exact architecture is an asynchronous combination of (i) diversified local-improvement searches that lower the upper bound, (ii) core/IHS workers that add certified lower-bound information, and (iii) backbone probes that propose candidates but may add a literal globally only after a refutation check. This combines the complementary core-guided and implicit-hitting-set views ([Ihalainen, Berg & Järvisalo, “Unifying Core-Guided and Implicit Hitting Set Based Optimization,” IJCAI 2023](https://www.ijcai.org/proceedings/2023/215); [Fazekas, Bacchus & Biere, “Implicit Hitting Set Algorithms for Maximum Satisfiability Modulo Theories,” IJCAR 2018, DOI 10.1007/978-3-319-94205-6_10](https://doi.org/10.1007/978-3-319-94205-6_10)).

The correctness invariant is: every recorded core is checked against hard constraints, every feasible model supplies an upper bound equal to its actual weighted violation cost, and the minimum-cost hitting-set value of recorded cores is a lower bound. When bounds meet, the coordinator emits an exact certificate. A sampled consensus literal is **not** a certificate: sampling estimates bias, but an unseen feasible/optimal model may disagree. Treat sampling as a source of candidates and use assumptions or a hard-plus-bound refutation test before asserting anything ([Hsu, Muise, Beck & McIlraith, “Probabilistically Estimating Backbones and Variable Bias: Experimental Overview,” CP 2008, DOI 10.1007/978-3-540-85958-1_52](https://doi.org/10.1007/978-3-540-85958-1_52); [Kilby, Slaney, Thiébaux & Walsh, “Backbones and Backdoors in Satisfiability,” AAAI 2005](https://aaai.org/papers/01368-aaai05-217-backbones-and-backdoors-in-satisfiability/)).

## 1. Parallel MaxSAT

### 1.1 Portfolio, splitting, and hybrid designs

**Portfolio parallelism** runs several complete or incomplete solvers on the same instance with different seeds, encodings, branching policies, or engines. It exploits high SAT/MaxSAT runtime variance. PWBO runs an unsatisfiability-based search for the lower bound and a linear/model-improving search for the upper bound, sharing learned clauses between those threads ([Martins, Manquinho & Lynce, “Parallel Search for Maximum Satisfiability,” *AI Communications* 25(2), 2012, pp. 75–95, DOI 10.3233/AIC-2012-0517](https://doi.org/10.3233/AIC-2012-0517); [PWBO Solver, INESC-ID, 2012](http://sat.inesc-id.pt/~vmm/research/pwbo/index.html)). A local-improvement worker can therefore publish a better model without waiting for a core worker.

**Search-space splitting** gives workers disjoint subproblems, commonly by a bound interval, a cube, or a partition of soft/objective variables. PWBO describes splitting by different upper-bound values, while its portfolio strategy uses different cardinality encodings ([Martins, Manquinho & Lynce, “Parallel Search for Maximum Satisfiability,” *AI Communications* 25(2), 2012, DOI 10.3233/AIC-2012-0517](https://doi.org/10.3233/AIC-2012-0517)). DistMS is explicitly non-portfolio distributed MaxSAT ([Neves, Lynce & Manquinho, “DistMS: A Non-Portfolio Distributed Solver for Maximum Satisfiability,” arXiv 2015, DOI 10.48550/arXiv.1505.02408](https://doi.org/10.48550/arXiv.1505.02408)).

A split is useful only when subproblems are complete and cover the original search space. A cube used only as a heuristic neighborhood is not a proof partition; the exact coordinator must retain a path to certify the lower bound. The portfolio/divide-and-conquer distinction and difficulty of finding useful partitions are also emphasized for SMT ([Barrett, Chen, Cook, Dutertre, Jones, Le, Reynolds, Sheth, Stephens & Whalen, “SMT-D: New Strategies for Portfolio-Based SMT Solving,” FMCAD 2024, pp. 39–48, DOI 10.34727/2024/isbn.978-3-85448-065-5_10](https://doi.org/10.34727/2024/isbn.978-3-85448-065-5_10)).

**Hybrid parallelism** is appropriate: portfolios diversify search while global monotone bound/core messages benefit all workers. Mallob-based MaxSAT transfers distributed clause sharing, incremental solving, task parallelism, and load balancing to solution-improving search; it is an anytime contribution, not a replacement for an exact certificate path ([Schreiber, Jabs & Berg, “From Scalable SAT to MaxSAT: Massively Parallel Solution Improving Search,” SoCS 2025, pp. 127–135, DOI 10.1609/socs.v18i1.35984](https://doi.org/10.1609/socs.v18i1.35984); [Schreiber, Jabs & Berg, “From Scalable SAT to MaxSAT – Appendix, Software, and Data,” Zenodo 2025](https://zenodo.org/records/15463749)).

### 1.2 Cores, clauses, correction sets, and bounds

PWBO is a concrete parallel core-guided pattern: its unsatisfiability-based thread searches the lower bound while a model/linear thread searches the upper bound, and the two share learned information ([Martins, Manquinho & Lynce, “Parallel Search for Maximum Satisfiability,” *AI Communications* 25(2), 2012, DOI 10.3233/AIC-2012-0517](https://doi.org/10.3233/AIC-2012-0517)). The prototype adopts this orthogonal lower/upper-bound allocation while adding asynchronous core, correction-set, model, and validated-backbone messages.

A core-guided worker asks a SAT/SMT oracle to satisfy hard constraints and selected soft constraints. An unsatisfiable core says at least one member must be violated; a model supplies a feasible correction set and upper bound. A worker can publish a core, correction set, model/cost, or bound. Cores and correction sets have complementary strengths: the primal-dual algorithm obtains either kind and rewrites incrementally ([Bjørner & Narodytska, “Maximum Satisfiability Using Cores and Correction Sets,” IJCAI 2015](https://www.ijcai.org/Proceedings/15/Papers/041.pdf); [Bjørner & Narodytska, IJCAI 2015 DOI record](https://dl.acm.org/doi/10.5555/2832249.2832283)).

Clause sharing is the SAT-level analogue of shared pruning information. Martins, Manquinho, and Lynce studied which learned clauses to share in deterministic parallel MaxSAT and identified nondeterministic scheduling/solution discovery as a problem ([Martins, Manquinho & Lynce, “Clause Sharing in Deterministic Parallel Maximum Satisfiability,” RCRA 2012](http://sat.inesc-id.pt/~ruben/papers/martins-rcra12.pdf)). In this prototype, serialize soft-item IDs and core assumptions, revalidate in the receiving isolated context, and add only verified cores to the proof set. Merge bounds monotonically (`LB := max(LB, received_LB)`, `UB := min(UB, received_UB)`).

Not every shared item helps. MallobSat uses buffering/filtering, while SMT-D balances useful pruning against overloading workers ([Schreiber & Sanders, “MallobSat: Scalable SAT Solving by Clause Sharing,” *JAIR* 80, 2024, pp. 1437–1495](https://www.jair.org/index.php/jair/article/view/15827); [Barrett, Chen, Cook, Dutertre, Jones, Le, Reynolds, Sheth, Stephens & Whalen, “SMT-D: New Strategies for Portfolio-Based SMT Solving,” FMCAD 2024, DOI 10.34727/2024/isbn.978-3-85448-065-5_10](https://doi.org/10.34727/2024/isbn.978-3-85448-065-5_10)). Make sharing policies configurable: all verified cores, bounded-size cores first, or a deduplicated queue.

### 1.3 Determinism and anytime solving

Race-based portfolios are normally nondeterministic: scheduling, arrival order, seeds, and interleavings change the anytime trace. This does not invalidate an exact result after certificate checking, but it affects reproducibility and comparisons. Deterministic parallel MaxSAT controls synchronization/sharing order; the Martins–Manquinho–Lynce work was motivated by the downside of nondeterministic runtime and solutions ([Martins, Manquinho & Lynce, “Clause Sharing in Deterministic Parallel Maximum Satisfiability,” RCRA 2012](http://sat.inesc-id.pt/~ruben/papers/martins-rcra12.pdf); [Martins, Manquinho & Lynce, “Deterministic Parallel MaxSAT Solving,” *International Journal on Artificial Intelligence Tools* 24(3), 2015](https://researchr.org/publication/MartinsML15)).

The requested coordinator is fully asynchronous: document event-order nondeterminism, record seeds and static role allocation, and make tie-breaking deterministic for equal-cost models. Exactness depends on rechecked models, cores, and bounds rather than message order.

An anytime solver returns the best feasible model found so far; an incomplete local search may have no proof. LNS selects a neighborhood around an incumbent and solves it exactly, improving suboptimal solutions from other anytime methods ([Hickey & Bacchus, “Large Neighbourhood Search for Anytime MaxSAT Solving,” IJCAI 2022, DOI 10.24963/ijcai.2022/253](https://doi.org/10.24963/ijcai.2022/253)). Core-boosted linear search combines SAT reasoning and stochastic local search ([Lübke & Berg, “SLS-Enhanced Core-Boosted Linear Search for Anytime Maximum Satisfiability,” CP 2025, DOI 10.4230/LIPIcs.CP.2025.28](https://doi.org/10.4230/LIPIcs.CP.2025.28)). Local workers may time out, but must publish each verified incumbent; a timeout is not optimality.

## 2. Core-guided and implicit-hitting-set MaxSAT

### 2.1 Model, cores, correction sets, and bound proof

Let `H` be satisfiable hard constraints and `S = {(s_i, w_i)}` soft constraints with positive weights. A feasible model satisfies `H`; its cost is `Σ w_i` over soft items false in that model. Unweighted partial MaxSAT is the special case `w_i = 1`. These definitions and the hard/soft distinction are standard ([Li & Manyà, “MaxSAT, Hard and Soft Constraints,” *Handbook of Satisfiability*, 2nd ed., 2021, pp. 903–927](https://ebooks.iospress.nl/doi/10.3233/FAIA201007); [Ignatiev, Morgado & Marques-Silva, “RC2: an Efficient MaxSAT Solver,” *JSAT* 11, 2019, pp. 53–64](https://www.cs.toronto.edu/~fbacchus/csc2512/Readings/rc2.pdf)).

A (soft) unsatisfiable core `C ⊆ S` satisfies `H ∧ ∧C` unsatisfiable. Every feasible model violates at least one member of every core. A correction set is a set of soft constraints whose removal makes the hard-plus-remaining-soft formula satisfiable; the violated soft set of a model is a correction set, and a minimal correction set is an MCS ([Bjørner & Narodytska, “Maximum Satisfiability Using Cores and Correction Sets,” IJCAI 2015](https://www.ijcai.org/Proceedings/15/Papers/041.pdf)).

**Why a minimum-cost hitting set is a lower bound.** Let `K` be any collection of verified cores. Every feasible model's violation set intersects every `C ∈ K`, so it is a hitting set of `K`. Therefore `min_cost_hitting_set(K) ≤ cost(model)` for every feasible model, and hence `min_cost_hitting_set(K) ≤ OPT`. The hitting set need not itself be feasible with respect to `H`, which is why its cost is a lower bound rather than necessarily a solution. This is the IHS duality: an optimizer proposes a set of violations and a core-extraction oracle either finds a model or adds a core ([Fazekas, Bacchus & Biere, “Implicit Hitting Set Algorithms for Maximum Satisfiability Modulo Theories,” IJCAR 2018, LNCS 10900, pp. 134–151, DOI 10.1007/978-3-319-94205-6_10](https://doi.org/10.1007/978-3-319-94205-6_10); [Ihalainen, Berg & Järvisalo, “Unifying Core-Guided and Implicit Hitting Set Based Optimization,” IJCAI 2023, pp. 1935–1943](https://www.ijcai.org/proceedings/2023/215)).

**Why a model is an upper bound.** If `M ⊨ H`, its measured violation cost is attainable; therefore `OPT ≤ cost(M)`. The exact certificate is a verified feasible model, all independently verified cores, a minimum-cost hitting-set value for those cores, and `LB = UB`. A model without a matching lower-bound proof is only an incumbent ([Berg, Bogaerts, Nordström & Oertel, “Certified Core-Guided MaxSAT Solving,” CADE-29 2023, LNCS 14132, pp. 1–22, DOI 10.1007/978-3-031-38499-8_1](https://doi.org/10.1007/978-3-031-38499-8_1)).

### 2.2 MSU3, OLL, MaxRes, and dual MaxRes

**MSU3.** MSU3 (Marques-Silva and Planes) is an unweighted core-guided algorithm. It keeps selector/relaxation variables for soft items that appeared in cores and raises a cardinality bound whenever a new core is found. The bound increase follows because each newly found core forces at least one additional violation in the current relaxation. The modern UniMaxSAT treatment identifies MSU3 as a cardinality-based core-guided instantiation ([Marques-Silva & Planes, “On Using Unsatisfiability for Solving Maximum Satisfiability,” CoRR abs/0712.1097, 2007](https://arxiv.org/abs/0712.1097); [Ihalainen, Berg & Järvisalo, “Unifying SAT-Based Approaches to Maximum Satisfiability Solving,” *JAIR* 81, 2024, pp. 933–976](https://www.cs.helsinki.fi/u/mjarvisa/papers/ibj.jair24.pdf)).

**OLL (one-literal-at-a-time / soft-cardinality relaxation).** OLL originated in unsatisfiability-based optimization in `clasp` and was adapted to MaxSAT with soft cardinality constraints. Given a core, it hardens/relaxes core literals and introduces a cardinality encoding whose output variables enter the working objective; each iteration raises the lower bound while preserving the optimum under the reformulation ([Andres, Kaufmann, Matheis & Schaub, “Unsatisfiability-Based Optimization in clasp,” ICLP 2012, LIPIcs 17, pp. 211–221](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICLP.2012.211); [Morgado, Dodaro & Marques-Silva, “Core-Guided MaxSAT with Soft Cardinality Constraints,” CP 2014, LNCS 8656, pp. 564–573, DOI 10.1007/978-3-319-10428-7_41](https://doi.org/10.1007/978-3-319-10428-7_41)).

**RC2.** RC2 (“Relaxable Cardinality Constraints”) is a Python core-guided solver built on incremental SAT assumptions. It turns a core into hardened relaxed clauses plus a soft cardinality constraint, reuses cardinality encodings, supports unweighted and weighted formulas (weight splitting/stratification), and adds core exhaustion and intrinsic AtMost1 heuristics. RC2 won both unweighted and weighted complete categories of MaxSAT Evaluation 2018 ([Ignatiev, Morgado & Marques-Silva, “RC2: an Efficient MaxSAT Solver,” *JSAT* 11, 2019, pp. 53–64](https://www.cs.toronto.edu/~fbacchus/csc2512/Readings/rc2.pdf)).

**MaxRes.** MaxRes is a MaxSAT-resolution-style core transformation: an extracted core is replaced with a cost-preserving, offset-adjusted construction that increases the represented lower bound. The core-guided MaxSAT-resolution algorithm of Narodytska and Bacchus is the direct reference ([Narodytska & Bacchus, “Maximum Satisfiability Using Core-Guided MaxSAT Resolution,” AAAI 2014, pp. 2717–2723](https://www.aaai.org/ocs/index.php/AAAI/AAAI14/paper/view/8261); [Bjørner & Narodytska, “Maximum Satisfiability Using Cores and Correction Sets,” IJCAI 2015](https://www.ijcai.org/Proceedings/15/Papers/041.pdf)).

**Dual MaxRes / correction-set restriction.** The dual transformation starts from a correction set and restricts/eliminates solutions that violate all items in that set, preserving the cost of remaining solutions while shrinking the working soft representation. Bjørner and Narodytska call the core and correction-set transformations dual and prove the cost-preservation properties ([Bjørner & Narodytska, “Maximum Satisfiability Using Cores and Correction Sets,” IJCAI 2015](https://www.ijcai.org/Proceedings/15/Papers/041.pdf)). In parallel, these rewrites belong to one coordinator state machine (or private worker copies followed by a versioned commit); threads must not mutate one solver/reformulation concurrently.

### 2.3 IHS versus core-guided search

IHS keeps the original hard/soft instance in a reasoning oracle and a growing set of cores in a hitting-set optimizer. The optimizer proposes a minimum-cost set of soft items to disable; the oracle checks the corresponding remaining constraints. SAT/SMT returns a feasible model/upper bound or a new core that every future hitting set must hit. This separates theory reasoning from combinatorial optimization and lifts naturally from MaxSAT to MaxSMT ([Fazekas, Bacchus & Biere, “Implicit Hitting Set Algorithms for Maximum Satisfiability Modulo Theories,” IJCAR 2018, DOI 10.1007/978-3-319-94205-6_10](https://doi.org/10.1007/978-3-319-94205-6_10)).

Core-guided methods instead reformulate the working objective and constraints after each core, so later cores are from a transformed formula. UniMaxSAT captures core-guided, IHS, and objective-bounding approaches and supplies a uniform correctness argument, supporting shared information with one explicit certificate representation ([Ihalainen, Berg & Järvisalo, “Unifying Core-Guided and Implicit Hitting Set Based Optimization,” IJCAI 2023](https://www.ijcai.org/proceedings/2023/215); [Ihalainen, Berg & Järvisalo, “Unifying SAT-Based Approaches to Maximum Satisfiability Solving,” *JAIR* 81, 2024](https://www.cs.helsinki.fi/u/mjarvisa/papers/ibj.jair24.pdf)).

## 3. Local improvement, MSS/MCS, and large neighborhoods

For a satisfiable subset of soft constraints, an **MSS** is maximal under inclusion; its complement among soft constraints is an **MCS**. A maximum-cardinality MSS is an unweighted MaxSAT solution, while weighted MaxSAT seeks minimum-weight MCS/violation cost. Enumeration can be exponential in the number of MCSes, so practical methods exploit rotation and locality rather than promise complete enumeration on every instance ([Morgado, Liffiton & Marques-Silva, “MaxSAT-Based MCS Enumeration,” HVC 2012, LNCS 7857, pp. 86–101, DOI 10.1007/978-3-642-39611-3_13](https://doi.org/10.1007/978-3-642-39611-3_13); [Grégoire, Izza & Lagniez, “Boosting MCSes Enumeration,” IJCAI 2018, DOI 10.24963/ijcai.2018/182](https://doi.org/10.24963/ijcai.2018/182)).

**Model rotation** starts from a model/MSS and probes a soft item currently false, or removes a satisfied item from the MSS. A satisfiable probe yields a neighbor; an unsatisfiable probe yields a core and often identifies a forced polarity under current assumptions. Rotation-based MSS/MCS enumeration formalizes this way to obtain nearby subsets ([Bendík & Černá, “Rotation Based MSS/MCS Enumeration,” LPAR 2020, EPTCS 346, pp. 120–137, DOI 10.29007/8btb](https://doi.org/10.29007/8btb)). The local `hs.py` uses the same pattern: `try_rotate` probes `mss | backbones | {p}` and records unsat-core information, while `mss_rotate` chooses repeatedly occurring literals to remove (`hs.py` lines 297–351).

**LNS with a SAT/SMT oracle.** Freeze most decisions of an incumbent, release a selected neighborhood, and ask an exact oracle whether the neighborhood admits lower cost. A successful solve updates the incumbent; an unsuccessful one can be blocked or deprioritized. Hickey and Bacchus apply LNS to anytime MaxSAT, selecting neighborhoods around current solutions ([Hickey & Bacchus, “Large Neighbourhood Search for Anytime MaxSAT Solving,” IJCAI 2022, DOI 10.24963/ijcai.2022/253](https://doi.org/10.24963/ijcai.2022/253)). For MaxSMT, the neighborhood uses Z3 Solver/Optimize under assumptions but must be evaluated against the original hard theory/objective ([Bjørner, Phan & Fleckenstein, “νZ – An Optimizing SMT Solver,” TACAS 2015, DOI 10.1007/978-3-662-46681-0_14](https://doi.org/10.1007/978-3-662-46681-0_14)).

**Incumbent seeding.** A feasible model gives local workers a concrete assignment, current UB, and basis for selecting a small/free-variable neighborhood. Copy assignments as ordinary values/literals into each isolated context; never pass a Z3 model object between threads. This follows model-improving PWBO and LNS designs ([Martins, Manquinho & Lynce, “Parallel Search for Maximum Satisfiability,” AI Communications 2012, DOI 10.3233/AIC-2012-0517](https://doi.org/10.3233/AIC-2012-0517); [Hickey & Bacchus, “Large Neighbourhood Search for Anytime MaxSAT Solving,” IJCAI 2022](https://doi.org/10.24963/ijcai.2022/253)).

## 4. Backbones and sampled candidates

A backbone literal of satisfiable `F` is true in every model; `l` is a backbone when `F ∧ ¬l` is unsatisfiable after confirming `F` is satisfiable. An **optimal backbone** has the same value in every optimum model, so the refutation formula includes hard constraints and an objective bound equal to the known optimum. Definitions and SAT-oracle extraction procedures are given by Marques-Silva, Janota, and Lynce and by CadiBack ([Marques-Silva, Janota & Lynce, “On Computing Backbones of Propositional Theories,” ECAI 2010, DOI 10.3233/978-1-60750-606-5-15](https://doi.org/10.3233/978-1-60750-606-5-15); [Biere, Froleyks & Wang, “CadiBack: Extracting Backbones with CaDiCaL,” SAT 2023, DOI 10.4230/LIPIcs.SAT.2023.3](https://doi.org/10.4230/LIPIcs.SAT.2023.3)).

For a fixed candidate literal, exact testing is one SAT/UNSAT query after finding a model; extracting all backbones can require many tests or chunk/core methods. Determining backbone structure is hard in general: Kilby et al. prove backbones hard even to approximate, and weighted MaxSAT backbone approximation is itself studied as an intractable task ([Kilby, Slaney, Thiébaux & Walsh, “Backbones and Backdoors in Satisfiability,” AAAI 2005](https://aaai.org/papers/01368-aaai05-217-backbones-and-backdoors-in-satisfiability/); [Jiang, Xuan & Hu, “Approximating the Backbone in the Weighted Maximum Satisfiability Problem,” arXiv 2017, DOI 10.48550/arXiv.1704.04775](https://doi.org/10.48550/arXiv.1704.04775)).

**Sampling estimates bias; it does not prove a backbone.** If `k` feasible models all assign `x=true`, that is evidence of high sampled bias, not evidence that no feasible/optimal model assigns `x=false`. Hsu, Muise, Beck & McIlraith explicitly study probabilistic estimation of backbone variables as a special case of variable bias ([Hsu, Muise, Beck & McIlraith, “Probabilistically Estimating Backbones and Variable Bias: Experimental Overview,” CP 2008, DOI 10.1007/978-3-540-85958-1_52](https://doi.org/10.1007/978-3-540-85958-1_52)). Asserting an unvalidated sampled candidate can remove a valid model and is unsound.

Safe uses are: a polarity/phase preference or local seed (search order only), a temporary assumption that the solver may reject, or a validated refutation `H ∧ objective_bound ∧ ¬l` followed by assertion. CadiBack uses iterative SAT tests; the current Z3 parallel SMT code turns a singleton assumption core into a backbone only after UNSAT (`smt_parallel.cpp` lines 434–459) ([Biere, Froleyks & Wang, “CadiBack: Extracting Backbones with CaDiCaL,” SAT 2023, DOI 10.4230/LIPIcs.SAT.2023.3](https://doi.org/10.4230/LIPIcs.SAT.2023.3); [Z3 source, commit `ba329f1f9874815666fbbbb57a8f8a4ca11dd70f`, lines 434–459](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/smt/smt_parallel.cpp#L434-L459)).

## 5. Parallel SMT and Z3 API constraints

### 5.1 Portfolio and cube-and-conquer

Parallel SMT has portfolio and divide-and-conquer shapes. SMT-D lets workers export/import theory-aware lemmas through a central broker and emphasizes runtime variance among equivalent formulas ([Barrett, Chen, Cook, Dutertre, Jones, Le, Reynolds, Sheth, Stephens & Whalen, “SMT-D: New Strategies for Portfolio-Based SMT Solving,” FMCAD 2024, pp. 39–48, DOI 10.34727/2024/isbn.978-3-85448-065-5_10](https://doi.org/10.34727/2024/isbn.978-3-85448-065-5_10)).

Z3's programming guide documents `parallel.enable=true` for selected tactics including QF_BV, where cube-and-conquer generates cubes and solves subgoals in parallel; `parallel.threads.max` caps workers ([Bjørner, “Programming Z3,” Z3 online guide, current documentation accessed 2026-08-13](https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-parallel-z3)). Its cube interface partitions a search space into parallel subproblems ([Bjørner, “Programming Z3,” Z3 online guide, current documentation](https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-cubes)). This inspires optional exact partition workers but does not itself solve MaxSMT objective sharing.

The local Z3 checkout calls its built-in engine “Parallel SMT, portfolio loop specialized to SMT core” and contains SLS and backbone workers (`C:\z3\src\smt\smt_parallel.cpp`, lines 1–17 and 73–114). Its failed-literal/batch path asserts a singleton-core backbone only after an UNSAT check (`lines 434–459`). These are useful references, but the Python prototype must not assume this private C++ engine is exposed through Python or that it supplies a MaxSMT certificate ([Z3 source, commit `ba329f1f9874815666fbbbb57a8f8a4ca11dd70f`](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/smt/smt_parallel.cpp#L1-L17)).

### 5.2 Isolated contexts and thread safety

Z3Py's Context reference states that objects belong to contexts, objects from different contexts cannot be mixed unless translated, and accessing Z3 objects from multiple threads is not safe; `interrupt()` is the cross-thread exception ([Z3 Project, “Context Class Reference,” Z3 Python API documentation, current documentation accessed 2026-08-13](https://z3prover.github.io/api/html/classz3py_1_1_context.html)). The Programming Z3 guide says operations on same-context objects are not thread-safe, while two threads can safely operate on objects from different contexts ([Bjørner, “Programming Z3,” Z3 online guide, current documentation](https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-parallel-z3)).

Each Python worker must construct its own `z3.Context`, Solver/Optimize, expressions, and model. The coordinator exchanges only plain Python data (soft IDs, serialized literals, costs, cores, assignments) and reconstructs expressions in the receiving context. A shared Solver, Optimize, ModelRef, AST, or mutable Z3 expression is not an acceptable message ([Z3 Project, “Context Class Reference,” Z3 Python API documentation](https://z3prover.github.io/api/html/classz3py_1_1_context.html)).

### 5.3 Lemma quality and sharing

SMT-D reports that older Z3 portfolio sharing used short (eight-literal-or-fewer) lemmas, queued for import at decision level zero; SMTS used a central database and filters, with a four-literal filter performing well. SMT-D adds delayed sharing and guided randomization because indiscriminate sharing can overwhelm workers ([Barrett, Chen, Cook, Dutertre, Jones, Le, Reynolds, Sheth, Stephens & Whalen, “SMT-D: New Strategies for Portfolio-Based SMT Solving,” FMCAD 2024, DOI 10.34727/2024/isbn.978-3-85448-065-5_10](https://doi.org/10.34727/2024/isbn.978-3-85448-065-5_10)).

For this MaxSMT prototype, verified cores and monotone bounds are higher-value messages than arbitrary theory lemmas. If lemma sharing is later added, use configurable quality (size, activity, source diversity, duplicate suppression, import budget) and verify context ownership before insertion. The final certificate contains proof-relevant cores, not an unverifiable claim that a learned lemma was shared.

## 6. MaxSMT, Z3 Optimize, and weighted objectives

MaxSMT differs from propositional MaxSAT in the language of constraints: MaxSAT has Boolean CNF clauses, while MaxSMT has theory formulas as hard or soft constraints. The objective remains a sum of penalties for violated soft constraints (or maximum satisfied weight), but the oracle reasons in a background theory ([Fazekas, Bacchus & Biere, “Implicit Hitting Set Algorithms for Maximum Satisfiability Modulo Theories,” IJCAR 2018, DOI 10.1007/978-3-319-94205-6_10](https://doi.org/10.1007/978-3-319-94205-6_10); [Bjørner, Phan & Fleckenstein, “νZ – An Optimizing SMT Solver,” TACAS 2015, DOI 10.1007/978-3-662-46681-0_14](https://doi.org/10.1007/978-3-662-46681-0_14)).

Z3 `Optimize` supports hard assertions, `assert_soft` with weights, and arithmetic `minimize`/`maximize` objectives. The online guide says MaxRes is the default MaxSAT engine and `wmax` an alternative that can work better on some domains ([Z3 Project, “Advanced Topics: Weighted Max-SAT solvers, a portfolio,” Z3 Guide, version 4.15.1 documentation accessed 2026-08-13](https://microsoft.github.io/z3guide/docs/optimization/advancedtopics/)).

The checked Z3 source records `maxsat_engine` and dispatches to MaxRes, binary MaxRes, RC2, primal-dual MaxRes, or WMax ([Z3 `src/opt/opt_params.pyg`, commit `ba329f1f9874815666fbbbb57a8f8a4ca11dd70f`, lines 4–15](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/opt/opt_params.pyg#L4-L15); [Z3 `src/opt/maxsmt.cpp`, same commit, lines 181–205](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/opt/maxsmt.cpp#L181-L205)). Relevant source is:

```text
('maxsat_engine', SYMBOL, 'maxres', ... 'core_maxsat', 'wmax', 'maxres', ... 'pd-maxres', ... 'rc2')
else if (maxsat_engine == symbol("pd-maxres")) m_msolver = mk_primal_dual_maxres(...);
else if (maxsat_engine == symbol("wmax")) m_msolver = mk_wmax(...);
```

The parameter file also exposes `enable_sls`, `enable_lns`, `enable_core_rotate`, and MaxRes core/upper-bound controls ([Z3 `src/opt/opt_params.pyg`, commit `ba329f1f9874815666fbbbb57a8f8a4ca11dd70f`, lines 12–31](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/opt/opt_params.pyg#L12-L31)). These validate local-improvement and rotation-inspired worker roles, but the prototype is independent of private internals.

Weights require exact integer/rational comparisons, residual-weight handling when relaxing a core, and a weighted hitting-set objective; they cannot be silently counted as unit clauses. RC2 documents weight splitting and stratification, while Z3's guide notes a lexicographic shortcut for weight sequences in which each next weight dominates the sum of previous weights ([Ignatiev, Morgado & Marques-Silva, “RC2: an Efficient MaxSAT Solver,” *JSAT* 11, 2019](https://www.cs.toronto.edu/~fbacchus/csc2512/Readings/rc2.pdf); [Z3 Project, “Advanced Topics: Weighted Max-SAT solvers, a portfolio,” Z3 Guide](https://microsoft.github.io/z3guide/docs/optimization/advancedtopics/)).

## 7. Public benchmark suites and downloads

**MaxSAT Evaluation (MSE).** The official MSE site evaluates open-source MaxSAT solvers and collects/re-distributes heterogeneous benchmarks ([MaxSAT Evaluation organizers, “MaxSAT Evaluations,” official site, current page accessed 2026-08-13](https://maxsat-evaluations.github.io/)). MSE 2023 has exact-track unweighted (572 instances) and weighted (558) collections, plus anytime unweighted (160) and weighted (179) archives ([MaxSAT Evaluation 2023 organizers, “Benchmark Sets,” MSE 2023, 2023](https://maxsat-evaluations.github.io/2023/benchmarks.html)). Concrete downloads:

* Exact unweighted: [MSE 2023 exact unweighted collection](https://drive.google.com/file/d/13qDbScs9jU1VaUaq4L7qSGEUrHxC9t6d/view?usp=drive_link).
* Exact weighted: [MSE 2023 exact weighted collection](https://drive.google.com/file/d/1pKuQkuTZr7CO3GXmOGRvrMeLTOaw9Fl6/view?usp=drive_link).
* Anytime weighted: [MSE2023-anytime-W-benchmarks.zip](https://www.cs.helsinki.fi/group/coreo/MSE2023-anytime-instances/MSE2023-anytime-W-benchmarks.zip).
* Anytime unweighted: [MSE2023-anytime-UW-benchmarks.zip](https://www.cs.helsinki.fi/group/coreo/MSE2023-anytime-instances/MSE2023-anytime-UW-benchmarks.zip).

MSE 2022 documents the revised WCNF convention: hard clauses are marked with `h` and the old `p` line is removed ([MaxSAT Evaluation 2022 organizers, “MaxSAT Evaluation 2022,” MSE 2022, 2022](https://maxsat-evaluations.github.io/2022/)). MSE 2023 asks main-track submissions to use revised WCNF ([MaxSAT Evaluation 2023 organizers, “Call for Benchmarks,” MSE 2023, 2023](https://maxsat-evaluations.github.io/2023/call-for-benchmarks.html)). The reader must accept the current `h` marker and not assume a legacy `p` header.

**SMT-LIB.** The official SMT-LIB benchmark library distributes theory benchmarks and metadata, pointing to Zenodo for current releases ([SMT-LIB community, “Benchmarks,” SMT-LIB official site, current page accessed 2026-08-13](https://smt-lib.org/benchmarks.shtml)). The 2025 non-incremental release is [Zenodo 15493090](https://zenodo.org/records/15493090), with archives such as [QF_LIA.tar.zst](https://zenodo.org/records/15493090/files/QF_LIA.tar.zst) and [QF_BV.tar.zst](https://zenodo.org/records/15493090/files/QF_BV.tar.zst); the 2025 incremental release is [Zenodo 15493096](https://zenodo.org/records/15493096). These are satisfiability benchmarks rather than a ready-made MaxSMT soft-assertion track, so the harness must document any soft-assertion transformation.

## 8. `C:\z3\examples\python\hs.py`: mechanisms and parallelism limits

The local file is the requested reference, not an upstream claim about every Z3 version. The following line ranges were read directly on 2026-08-13. A durable full-SHA copy of the same upstream file is [Z3 `examples/python/hs.py`, commit `ba329f1f9874815666fbbbb57a8f8a4ca11dd70f`](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/examples/python/hs.py#L1-L494); the local path is retained because the task explicitly requests it.

### 8.1 Mechanisms worth reusing

1. **Named definitions.** `add_def` creates a fresh Boolean name, asserts equivalence, and returns the name (lines 13–18). This keeps prefix expressions shareable; use worker-local name namespaces instead of the process-global counter.
2. **MaxRes core relaxation.** `relax_core` removes a core and inserts prefix definitions (lines 20–28). Reuse the compact rewrite in a private/versioned context; it is unweighted.
3. **Dual correction-set restriction.** `restrict_cs` creates prefix disjunction/conjunction definitions (lines 30–38), illustrating dual MaxRes.
4. **Hitting-set picker.** `HsPicker.pick_hs` encodes each core as `Or` over names, minimizes `Not(n)` with `Optimize.add_soft`, and updates `lo` (lines 81–125). The random greedy fallback (lines 81–88) is a heuristic, not an exact lower-bound proof.
5. **`lo`/`hi`/offset state.** `HsMaxSAT` stores bounds, cores, corrections, and offset (lines 128–143); `reinit_soft` adjusts offset and lower bound (163–169); `run` stops at `lo + offset < hi` (455–473). This is the right invariant shape for a certificate-producing coordinator.
6. **Core reduction.** `reduce_core` performs deletion checks under a short timeout (252–276). Keep the original verified core in an audit log even if a smaller replacement is found.
7. **Correction-set collection.** `improve` computes MSS/correction set, cost, and incumbent model (278–295), the right message shape for local workers.
8. **Local MSS and rotation.** `local_mss` probes remaining soft formulas, adds cores on UNSAT, and calls `improve` on SAT models (354–409); `try_rotate`/`mss_rotate` implement model rotation (297–351). Use these as local heuristics.
9. **Core exhaustion.** `get_cores` gathers more cores and invokes `local_mss` after progress stalls (411–453), a useful way to diversify information.
10. **Diagnostics.** Core-size counts and bound/offset reports (40–49, 455–468) should become structured JSONL telemetry.

### 8.2 Single-threaded assumptions that must change

* One mutable `self.s` is used by every method (130–133, 252–409); it assumes one solver/call stack. Each thread needs its own Z3 context and solver.
* `Ks`, `Cs`, soft sets, model, bounds, offset, and patterns are ordinary mutable fields with no locks/versioning (58–67, 128–143, 232–247, 278–295). Workers publish immutable messages; the coordinator merges/deduplicates.
* Module-global `counter` and `random.choice` (11–18, 81–87, 304–306, 371–374, 431–445) are not deterministic under asynchronous scheduling and can collide if copied naïvely. Use worker-local names and RNG seeds.
* `HsPicker` has a mutable Optimize timeout/backoff state (74–125); do not share it or treat a timeout/fallback as a certified hitting-set optimum.
* `maxres` rewrites the solver and resets core/correction collections (171–215). It is a serial state transition; use versioned coordinator commits or private proposals.
* `step`/`run` are serial loops (455–473); replace with an event queue and cancellation epochs while retaining monotone bounds.
* `main` explicitly assumes unweighted MaxSAT and ignores weights (476–486). New objective handling must not silently discard weights.
* `try_rotate` uses `backbones` as local assumptions (297–325). That is safe as a hypothesis, not proof of a global/optimal backbone; validate before assertion.

## 9. Ideas adopted in this prototype

These are actionable design decisions for the requested Python-threaded, isolated-context, fully-asynchronous, exact-anytime MaxSMT solver:

1. **Objective interface for unit and weighted penalties.** Stable soft IDs, exact integer/rational weights, and a common cost evaluator; unweighted is unit-weight specialization ([Ignatiev, Morgado & Marques-Silva, “RC2: an Efficient MaxSAT Solver,” JSAT 2019](https://www.cs.toronto.edu/~fbacchus/csc2512/Readings/rc2.pdf); [Fazekas, Bacchus & Biere, “Implicit Hitting Set Algorithms for MaxSMT,” IJCAR 2018, DOI 10.1007/978-3-319-94205-6_10](https://doi.org/10.1007/978-3-319-94205-6_10)).
2. **One Z3 context per worker.** Construct all expressions, Solver/Optimize objects, and models within that worker; exchange only plain IDs/literals/numbers ([Z3 Project, “Context Class Reference,” Z3 Python API documentation](https://z3prover.github.io/api/html/classz3py_1_1_context.html)).
3. **Static user-configurable role allocation.** CLI counts for `local`, `core/IHS`, and `backbone` roles, combining PWBO LB/UB roles with Z3's SLS/backbone separation ([Martins, Manquinho & Lynce, “Parallel Search for Maximum Satisfiability,” AI Communications 2012, DOI 10.3233/AIC-2012-0517](https://doi.org/10.3233/AIC-2012-0517); [Z3 `smt_parallel.cpp`, commit `ba329f1f9874815666fbbbb57a8f8a4ca11dd70f`, lines 73–114](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/smt/smt_parallel.cpp#L73-L114)).
4. **Fully asynchronous coordinator.** A thread-safe queue carries `CandidateModel`, `CoreFound`, `BackboneCandidate`, `BoundUpdate`, and `Stop`; workers do not barrier ([Barrett, Chen, Cook, Dutertre, Jones, Le, Reynolds, Sheth, Stephens & Whalen, “SMT-D: New Strategies for Portfolio-Based SMT Solving,” FMCAD 2024, DOI 10.34727/2024/isbn.978-3-85448-065-5_10](https://doi.org/10.34727/2024/isbn.978-3-85448-065-5_10)).
5. **Monotone bounds.** Merge LB by maximum and UB by minimum; attach epochs; discard stale transformations but retain valid models/cores; terminate only when verified LB equals verified UB ([Fazekas, Bacchus & Biere, “Implicit Hitting Set Algorithms for MaxSMT,” IJCAR 2018, DOI 10.1007/978-3-319-94205-6_10](https://doi.org/10.1007/978-3-319-94205-6_10)).
6. **Separate certificate verifier.** Recheck every core, compute the minimum-cost hitting set, recheck final model/cost, and require `LB == UB`; never certify from a heuristic LB or sampled backbone ([Berg, Bogaerts, Nordström & Oertel, “Certified Core-Guided MaxSAT Solving,” CADE 2023, DOI 10.1007/978-3-031-38499-8_1](https://doi.org/10.1007/978-3-031-38499-8_1)).
7. **Incumbent-seeded local workers.** Freeze most incumbent decisions, explore randomized neighborhoods under assumptions, and publish each strictly lower-cost model ([Hickey & Bacchus, “Large Neighbourhood Search for Anytime MaxSAT Solving,” IJCAI 2022, DOI 10.24963/ijcai.2022/253](https://doi.org/10.24963/ijcai.2022/253)).
8. **Core/IHS workers with reduction and correction collection.** Use deletion minimization under a budget, retain original cores for audit, and publish correction sets from models ([local Z3 `hs.py`, lines 252–295](file:///C:/z3/examples/python/hs.py#L252-L295); [Bjørner & Narodytska, “Maximum Satisfiability Using Cores and Correction Sets,” IJCAI 2015](https://www.ijcai.org/Proceedings/15/Papers/041.pdf)).
9. **Validated sampled-backbone pipeline.** Sample feasible models and report consensus with counts; use candidates only as hints/assumptions until `H ∧ bound ∧ ¬l` is refuted, then record/assert ([Hsu, Muise, Beck & McIlraith, “Probabilistically Estimating Backbones and Variable Bias,” CP 2008, DOI 10.1007/978-3-540-85958-1_52](https://doi.org/10.1007/978-3-540-85958-1_52); [Z3 `smt_parallel.cpp`, commit `ba329f1f9874815666fbbbb57a8f8a4ca11dd70f`, lines 448–459](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/smt/smt_parallel.cpp#L448-L459)).
10. **Rotation/MSS exploration as heuristic only.** Reuse `local_mss`, `try_rotate`, and `mss_rotate` in private contexts for neighboring incumbents/cores; hypotheses are not global facts ([local Z3 `hs.py`, lines 297–409](file:///C:/z3/examples/python/hs.py#L297-L409); [Bendík & Černá, “Rotation Based MSS/MCS Enumeration,” LPAR 2020, DOI 10.29007/8btb](https://doi.org/10.29007/8btb)).
11. **No concurrent MaxRes/dual-MaxRes mutation.** Treat `relax_core`/`restrict_cs` as coordinator-committed versioned transformations or private proposals; cancel stale workers ([local Z3 `hs.py`, lines 20–38 and 163–205](file:///C:/z3/examples/python/hs.py#L20-L38)).
12. **Anytime JSONL trace.** Log elapsed time, role/id, seed, incumbent cost, LB/UB, core count, candidate/validated backbone status, and certificate status; compare cost-at-time and time-to-certified-optimum ([Martins, Manquinho & Lynce, “Clause Sharing in Deterministic Parallel Maximum Satisfiability,” RCRA 2012](http://sat.inesc-id.pt/~ruben/papers/martins-rcra12.pdf); [Nadel, “Anytime Algorithms for MaxSAT and Beyond,” FMCAD 2020, DOI 10.34727/2020/isbn.978-3-85448-042-6_1](https://doi.org/10.34727/2020/isbn.978-3-85448-042-6_1)).
13. **Two baselines.** Compare one-worker internal sequential mode with Z3 `Optimize` engines (`maxres`, `wmax`, `pd-maxres`, `rc2` where supported), recording Z3 version/parameters ([Z3 `opt_params.pyg`, full-SHA source](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/opt/opt_params.pyg#L4-L15); [Z3 Guide, weighted Max-SAT portfolio](https://microsoft.github.io/z3guide/docs/optimization/advancedtopics/)).
14. **Public benchmark manifest.** Include MSE exact/anytime weighted/unweighted WCNF, checksums and revised-WCNF parsing, plus an explicitly documented SMT-LIB soft-assertion transformation ([MSE 2023 organizers, “Benchmark Sets,” MSE 2023](https://maxsat-evaluations.github.io/2023/benchmarks.html); [SMT-LIB community, “Benchmarks,” official site](https://smt-lib.org/benchmarks.shtml)).

## 10. Limits and source index

The literature establishes useful architectures, not guaranteed linear speedup; performance is instance- and communication-policy-dependent ([Lynce, Manquinho & Martins, “Parallel Maximum Satisfiability,” *Handbook of Parallel Constraint Reasoning*, Springer 2018, DOI 10.1007/978-3-319-63516-3_3](https://doi.org/10.1007/978-3-319-63516-3_3); [Barrett, Chen, Cook, Dutertre, Jones, Le, Reynolds, Sheth, Stephens & Whalen, “SMT-D: New Strategies for Portfolio-Based SMT Solving,” FMCAD 2024](https://doi.org/10.34727/2024/isbn.978-3-85448-065-5_10)). `hs.py` is explicitly unweighted and its `main` ignores weights (`lines 476–486`), so weighted support must be independently designed and tested. A sampled backbone can improve search but cannot shorten an exact certificate without a recorded refutation ([Hsu, Muise, Beck & McIlraith, “Probabilistically Estimating Backbones and Variable Bias,” CP 2008, DOI 10.1007/978-3-540-85958-1_52](https://doi.org/10.1007/978-3-540-85958-1_52)). SMT-LIB is primarily a satisfiability library; MaxSMT soft-constraint construction must be documented ([SMT-LIB community, “Benchmarks,” SMT-LIB](https://smt-lib.org/benchmarks.shtml)).

### Primary references

1. Martins, Manquinho & Lynce, “Parallel Search for Maximum Satisfiability,” *AI Communications*, 2012. DOI: https://doi.org/10.3233/AIC-2012-0517.
2. Martins, Manquinho & Lynce, “Clause Sharing in Deterministic Parallel Maximum Satisfiability,” RCRA 2012. http://sat.inesc-id.pt/~ruben/papers/martins-rcra12.pdf.
3. Lynce, Manquinho & Martins, “Parallel Maximum Satisfiability,” *Handbook of Parallel Constraint Reasoning*, Springer 2018. DOI: https://doi.org/10.1007/978-3-319-63516-3_3.
4. Schreiber, Jabs & Berg, “From Scalable SAT to MaxSAT: Massively Parallel Solution Improving Search,” SoCS 2025. DOI: https://doi.org/10.1609/socs.v18i1.35984.
5. Bjørner & Narodytska, “Maximum Satisfiability Using Cores and Correction Sets,” IJCAI 2015. https://www.ijcai.org/Proceedings/15/Papers/041.pdf.
6. Narodytska & Bacchus, “Maximum Satisfiability Using Core-Guided MaxSAT Resolution,” AAAI 2014. https://www.aaai.org/ocs/index.php/AAAI/AAAI14/paper/view/8261.
7. Morgado, Dodaro & Marques-Silva, “Core-Guided MaxSAT with Soft Cardinality Constraints,” CP 2014. DOI: https://doi.org/10.1007/978-3-319-10428-7_41.
8. Ignatiev, Morgado & Marques-Silva, “RC2: an Efficient MaxSAT Solver,” *JSAT* 11, 2019. https://www.cs.toronto.edu/~fbacchus/csc2512/Readings/rc2.pdf.
9. Fazekas, Bacchus & Biere, “Implicit Hitting Set Algorithms for Maximum Satisfiability Modulo Theories,” IJCAR 2018. DOI: https://doi.org/10.1007/978-3-319-94205-6_10.
10. Ihalainen, Berg & Järvisalo, “Unifying Core-Guided and Implicit Hitting Set Based Optimization,” IJCAI 2023. https://www.ijcai.org/proceedings/2023/215.
11. Hickey & Bacchus, “Large Neighbourhood Search for Anytime MaxSAT Solving,” IJCAI 2022. DOI: https://doi.org/10.24963/ijcai.2022/253.
12. Barrett, Chen, Cook, Dutertre, Jones, Le, Reynolds, Sheth, Stephens & Whalen, “SMT-D: New Strategies for Portfolio-Based SMT Solving,” FMCAD 2024. DOI: https://doi.org/10.34727/2024/isbn.978-3-85448-065-5_10.
13. Bjørner, Phan & Fleckenstein, “νZ – An Optimizing SMT Solver,” TACAS 2015. DOI: https://doi.org/10.1007/978-3-662-46681-0_14.
14. Hsu, Muise, Beck & McIlraith, “Probabilistically Estimating Backbones and Variable Bias,” CP 2008. DOI: https://doi.org/10.1007/978-3-540-85958-1_52.
15. Marques-Silva, Janota & Lynce, “On Computing Backbones of Propositional Theories,” ECAI 2010. DOI: https://doi.org/10.3233/978-1-60750-606-5-15.
16. Biere, Froleyks & Wang, “CadiBack: Extracting Backbones with CaDiCaL,” SAT 2023. DOI: https://doi.org/10.4230/LIPIcs.SAT.2023.3.
17. Z3 Project, “Programming Z3,” online guide, accessed 2026-08-13. https://theory.stanford.edu/~nikolaj/programmingz3.html.
18. Z3 Project, “Context Class Reference,” Python API documentation, accessed 2026-08-13. https://z3prover.github.io/api/html/classz3py_1_1_context.html.
19. MaxSAT Evaluation organizers, “Benchmark Sets,” MSE 2023. https://maxsat-evaluations.github.io/2023/benchmarks.html.
20. SMT-LIB community, “Benchmarks,” official site; Zenodo releases 15493090/15493096. https://smt-lib.org/benchmarks.shtml.

## Appendix A. Durable Z3 source excerpts

The local Z3 checkout was at commit `ba329f1f9874815666fbbbb57a8f8a4ca11dd70f` (2026-08-13). These snippets are included so implementation claims are tied to durable full-SHA links rather than a moving branch:

* Parallel SMT role split: [full-SHA `smt_parallel.cpp` lines 73–114](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/smt/smt_parallel.cpp#L73-L114) contains `sls_worker::run`, `backbones_worker::run`, and the two backbone modes.

  ```cpp
  void parallel::sls_worker::run() { ... }
  void parallel::backbones_worker::run() {
      if (m_use_failed_literal_test) run_failed_literal_mode();
      else run_batch_mode();
  }
  ```

* Validated singleton backbone: [full-SHA `smt_parallel.cpp` lines 434–459](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/smt/smt_parallel.cpp#L434-L459) inspects an UNSAT core, recognizes a singleton assumption, calls `collect_global_backbone`, and only then asserts the literal.

  ```cpp
  if (bb_asms_in_core.size() == 1) {
      expr_ref backbone_lit(mk_not(m, a), m);
      if (b.collect_global_backbone(m_l2g, backbone_lit))
          ctx->assert_expr(backbone_lit.get());
  }
  ```

* MaxSMT engine selection: [full-SHA `opt_params.pyg` lines 4–15](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/opt/opt_params.pyg#L4-L15) lists `maxsat_engine` and options such as `maxres`, `wmax`, `pd-maxres`, and `rc2`; [full-SHA `maxsmt.cpp` lines 181–205](https://github.com/Z3Prover/z3/blob/ba329f1f9874815666fbbbb57a8f8a4ca11dd70f/src/opt/maxsmt.cpp#L181-L205) dispatches to the corresponding solver constructors.

  ```cpp
  else if (maxsat_engine == symbol("pd-maxres"))
      m_msolver = mk_primal_dual_maxres(...);
  else if (maxsat_engine == symbol("wmax"))
      m_msolver = mk_wmax(...);
  ```

The `hs.py` references above are deliberately local absolute path plus line ranges because that example is outside the current workspace's version-controlled checkout; no branch URL is being presented as durable source evidence.
