RELEASE NOTES

Version 4.next
================
- Planned features
  - sat.euf 
    - CDCL core for SMT queries. It extends the SAT engine with theory solver plugins.
  - add global incremental pre-processing for the legacy core.


Version 4.15.0
==============
- Improved integer cut algorithms for linear integer arithmetic.
  It integrates diophantine equation solving with stronger cuts.
- C and OCaml API for accessing numerics, thanks to Josh Berdine
- A minimal mcp server in src/api/z3mcp.py that can run locally.
- Bug fixes.


Version 4.14.1
==============
- Add ubv_to_int, sbv_to_int, int_to_bv to SMTLIB2 API.
- Fix nuget package regression omitting Microsoft.Z3.* files

Version 4.14.0
==============
- [SLS modulo theories](https://microsoft.github.io/z3guide/programming/Local%20Search/) engine v1 release.
- API for accessing term [depth and groundness](https://github.com/Z3Prover/z3/pull/7479).
- Two fixes to relevancy propagation thanks to Can Cebeci. Two instacnes where literals lemmas and axioms were not marked relevant and therefore not propagated to other theories. Theory lemmas are replayed during backjumping and have are now by default marked relevant. 
- A new API for solving LRA variables modulo constraints.
- Performance and bug fixes.

Version 4.13.4
==============
- several updates to emscripten including #7473
- add preliminary pyodie build
- address issues with Java bindings
- Include start of sls-smt functionality SLS modulo theories as co-processor to SMT core and stand-alone tactic.

Version 4.13.3
==============
- Fixes, including #7363
- Fix paths to Java binaries in release
- Remove internal build names from pypi wheels

Version 4.13.2
==============
- Performance regression fix. #7404

Version 4.13.1
==============
- single-sample cell projection in nlsat was designed by Haokun Li and Bican Xia. 
- using simple-checker together with and variable ordering supported by qfnra_tactic was developed by Mengyu Zhao (Linxi) and Shaowei Cai.

   The projection is described in paper by Haokun Li and Bican Xia,   [Solving Satisfiability of Polynomial Formulas By Sample - Cell Projection](https://arxiv.org/abs/2003.00409). The code ported from https://github.com/hybridSMT/hybridSMT.git

- Add API for providing hints for the solver/optimize contexts for which initial values to attempt to use for variables.
 The new API function are Z3_solver_set_initial_value and Z3_optimize_set_initial_value, respectively. Supply these functions with a Boolean or numeric variable, and a value. The solver will then attempt to use these values in the initial phase of search. The feature is aimed at resolving nearly similar problems, or problems with a predicted model and the intent is that restarting the solver based on a near solution can avoid prune the space of constraints that are initially infeasible.
 The SMTLIB front-end contains the new command (set-initial-value var value). For example,
 (declare-const x Int)
 (set-initial-value x 10)
 (push)
 (assert (> x 0))
 (check-sat)
 (get-model)
 produces a model where x = 10. We use (push) to ensure that z3 doesn't run a
 specialized pre-processor that eliminates x, which renders the initialization
 without effect.
 

Version 4.13.0
==============
- add ARM64 wheels for Python, thanks to Steven Moy, smoy

Version 4.12.6
==============
- remove expensive rewrite that coalesces adjacent stores
- improved Java use of reference queues thanks to Thomas Haas #7131
- fixes to conditional import of python library thanks to Cal Jacobson #7116
- include universe for constants that get removed during pre-processing #7121
- code improvements, Bruce Mitchener #7119
- fix nested callback handling for user propagators
- include ARM64 binaries in distribution
- added Julia API, Thanks to Yisu Remy Yang #7108

Version 4.12.5
==============
- Fixes to pypi setup and build for MacOS distributions
- A new theory solver "int-blast" enabled by using:
  - sat.smt=true smt.bv.solver=2
  - It solves a few bit-vector problems not handled by bit-blasting, especially if the bit-widths are large.
  - It is based on encoding bit-vector constraints to non-linear integer arithmetic.
- Optimizations to the arithmetic solver. Description: https://github.com/Z3Prover/doc/tree/master/arithmetic

Version 4.12.4
==============
- Re-release fixing a few issues with 4.12:
  - Python dependency on importlib.resources vs importlib_resources break automatic pypi installations. Supposedly fixed by conditioning dependency on Python 3.9 where the feature is built-in.
  - Missing release of arm64 for Ubuntu.
  - Futile attempt to streamline adding readme.md file as part of Nuget distribution. Nuget.org now requires a readme file. I was able to integrate the readme with the cmake build, but the cross-platform repackage in scripts/mk_nuget_task.py does not ingest a similar readme file with the CI pipelines.

Version 4.12.3
==============
- Alpha support for polymorphism.
  - SMTLIB3-ish, C, Python
  It adds the new command `(declare-type-var A)` that declares a symbol (in this case `A`) globally as a polymorphic type variable.
  The C API contains a new function `Z3_mk_type_variable` and a new enumeration case `Z3_TYPE_VAR` as a kind associated with sorts.
  All occurrences of `A` are treated as type variables. A function declaration whose signature uses `A` is treated as a shorthand
  for declarations of all functions that use instances of `A`.
  Assertions that use type variables are shorthands for assertions covering all instantiations.
- Various (ongoing) performance fixes and improvements to smt.arith.solver=6
- A working version of solver.proof.trim=true option. Proofs logs created when using sat.smt=true may be trimmed by running z3
  on the generated proof log using the option solver.proof.trim=true. 
- Optimizations LIA and NIA (linear integer arithmetic and non-linear integer (and real) arithmetic reasoning).
  smt.arith.solver=6 is the default for most use cases. It trails smt.arith.solver=2 in some scenarios and the gap has been either removed or reduced.
  smt.arith.solver=6 is complete for integrations of non-linear real arithmetic and theories, smt.arith.solver=2 is not. 
- qel: Light quantifier elimination based on term graphs (egraphs), and corresponding Model Based Projection for arrays and ADTs. Used by Spacer and QSAT.
- added real-closed fields features to C API, exposed more RCF over OCaml API
- fixes to FP

Version 4.12.2
==============
- remove MSF (Microsoft Solver Foundation) plugin
- updated propagate-ineqs tactic and implementing it as a simplifier, bound_simplifier.
  It now eliminates occurrences of "mod" operators when bounds information
  implies that the modulus is redundant. This tactic is useful for
  benchmarks created by converting bit-vector semantics to integer 
  reasoning.
- add API function Z3_mk_real_int64 to take two int64 as arguments. The Z3_mk_real function takes integers.
- Add _simplifiers_ as optional incremental pre-processing to solvers.
  They are exposed over the SMTLIB API using the command [`set-simplifier`](https://microsoft.github.io/z3guide/docs/strategies/simplifiers).
  Simplifiers are similar to tactics, but they operate on solver state that can be incrementally updated. 
  The exposed simplifiers cover all the pre-processing techniques used internally with some additional simplifiers, such as `solve-eqs`
  and `elim-predicates` that go beyond incremental pre-processing used internally. The advantage of using `solve-eqs` during pre-processing
  can be significant. Incremental pre-processing simplification using `solve-eqs` and other simplifiers that change interpretations 
  was not possible before.
- Optimize added to JS API, thanks to gbagan
- SMTLIB2 proposal for bit-vector overflow predicates added, thanks to aehyvari 
- bug fixes, thanks to Clemens Eisenhofer, hgvk94, Lev Nachmanson, and others


Version 4.12.1
==============
- change macos build to use explicit reference to Macos version 11. Hosted builds are migrating to macos-12 and it broke a user Issue #6539.

Version 4.12.0
==============
- add clause logging API.
  - The purpose of logging API and self-checking is to enable an array of use cases.
    - proof mining (what instantiations did Z3 use)? 
      - A refresh of the AxiomProfiler could use the logging API. 
        The (brittle) trace feature should be deprecated.
    - debugging
      - a built-in self certifier implements a custom proof checker for 
        the format used by the new solver (sat.euf=true).
    - other potential options:
      - integration into certified tool chains      
      - interpolation 
  - Z3_register_on_clause (also exposed over C++, Python and .Net)
  - it applies to z3's main CDCL(T) core and a new CDCL(T) core (sat.euf=true).
  - The added API function allows to register a callback for when clauses 
    are inferred. More precisely, when clauses are assumed (as part of input), 
    deleted, or deduced.
    Clauses that are deduced by the CDCL SAT engine using standard 
    inferences are marked as 'rup'.
    Clauses that are deduced by theories are marked by default 
    by 'smt', and when more detailed information
    is available with proof hints or proof objects. 
    Instantiations are considered useful to track so they
    are logged using terms of the form 

         (inst (not (forall (x) body)) body[t/x] (bind t)), where

    'inst' is a name of a function that produces a proof term representing 
    the instantiation.
- add options for proof logging, trimming, and checking for the new core.
  - sat.smt.proof (symbol) add SMT proof to file (default: )
  - sat.smt.proof.check (bool) check SMT proof while it is created (default: false)
    - it applies a custom self-validator. The self-validator comprises of 
      several small checkers and represent a best-effort validation mechanism. 
      If there are no custom validators associated with inferences, or the custom 
      validators fail to certify inferences, the self-validator falls back to 
      invoking z3 (SMT) solving on the lemma.
      - euf - propagations and conflicts from congruence closure 
              (theory of equality and uninterpreted functions) are checked
              based on a proof format that tracks uses of congruence closure and 
              equalities. It only performs union find operations.
      - tseitin - clausification steps are checked for Boolean operators.
      - farkas, bound, implies_eq - arithmetic inferences that can be justified using 
              a combination of Farkas lemma and cuts are checked.
              Note: the arithmetic solver may produce proof hints that the proof 
              checker cannot check. It is mainly a limitation
              of the arithmetic solver not pulling relevant information. 
              Ensuring a tight coupling with proof hints and the validator
              capabilities is open ended future work and good material for theses. 
      - bit-vector inferences - are treated as trusted 
        (there is no validation, it always blindly succeeds)
      - arrays, datatypes - there is no custom validation for 
        other theories at present. Lemmas are validated using SMT.
  - sat.smt.proof.check_rup (bool) apply forward RUP proof checking (default: true)
    - this option can incur significant runtime overhead. 
      Effective proof checking relies on first trimming proofs into a 
      format where dependencies are tracked and then checking relevant inferences. 
      Turn this option off if you just want to check theory inferences.                         
- add options to validate proofs offline. It applies to proofs 
  saved when sat.smt.proof is set to a valid file name.
  - solver.proof.check (bool) check proof logs (default: true)
    - the option sat.smt.proof_check_rup can be used to control what is checked
  - solver.proof.save (bool) save proof log into a proof object 
      that can be extracted using (get-proof) (default: false)
    - experimental: saves a proof log into a term
  - solver.proof.trim (bool) trim the offline proof and print the trimmed proof to the console
    - experimental: performs DRUP trimming to reduce the set of hypotheses 
      and inferences relevant to derive the empty clause.
- JS support for Arrays, thanks to Walden Yan
- More portable memory allocation, thanks to Nuno Lopes 
  (avoid custom handling to calculate memory usage)

- clause logging and proofs: many open-ended directions.
  Many directions and functionality features remain in an open-ended state, 
  subject to fixes, improvements, and contributions.
  We list a few of them here:
  - comprehensive efficient self-validators for arithmetic, and other theories
  - an efficient proof checker when several theory solvers cooperate in a propagation or 
    conflict. The theory combination case is currently delegated to the smt solver. 
    The proper setup for integrating theory lemmas is in principle not complicated, 
    but the implementation requires some changes.
  - external efficient proof validators (based on certified tool chains) 
    can be integrated over the API.
  - dampening repeated clauses: A side-effect of conflict resolution is to 
    log theory lemmas. It often happens that the theory lemma becomes
    the conflict clause, that is then logged as rup. Thus, two clauses are 
    logged.
  - support for online trim so that proofs generated using clause logging can be used for SPACER
    - SPACER also would benefit from more robust proof hints for arithmetic 
      lemmas (bounds and implied equalities are sometimes not logged correctly)
  - integration into axiom profiling through online and/or offline interfaces.
    - an online interface attaches a callback with a running solver. This is available.
    - an offline interface saves a clause proof to a file (currently just 
      supported for sat.euf) and then reads the file in a separate process
      The separate process attaches a callback on inferred clauses. 
      This is currently not available but a relatively small feature.
  - more detailed proof hints for the legacy solver clause logger. 
    Other than quantifier instantiations, no detailed information is retained for 
    theory clauses. 
  - integration of pre-processing proofs with logging proofs. There is 
    currently no supported bridge to create a end-to-end proof objects.
- experimental API for accessing E-graphs. Exposed over Python. This API should be considered temporary
and subject to be changed depending on use cases or removed. The functions are `Z3_solver_congruence_root`, `Z3_solver_congruence_next`.


Version 4.11.2
==============
- add error handling to fromString method in JavaScript
- fix regression in default parameters for CDCL, thanks to Nuno Lopes
- fix model evaluation bugs for as-array nested under functions (data-type constructors)
- add rewrite simplifications for datatypes with a single constructor
- add "Global Guidance" capability to SPACER, thanks to Arie Gurfinkel and Hari Gorvind.
  The commit logs related to Global Guidance contain detailed information.
- change proof logging format for the new core to use SMTLIB commands.
  The format was so far an extension of DRAT used by SAT solvers, but not well compatible
  with SMT format that is extensible. The resulting format is a mild extension of SMTLIB with
  three extra commands assume, learn, del. They track input clauses, generated clauses and deleted clauses.
  They are optionally augmented by proof hints. Two proof hints are used in the current version: "rup" and "farkas".
  "rup" is used when the generated clause can be justified by reverse unit propagation. "farkas" is used when
  the clause can be justified by a combination of Farkas cutting planes. There is a built-in proof checker for the
  format. Quantifier instantiations are also tracked as proof hints.
  Other proof hints are to be added as the feature set is tested and developed. The fallback, built-in,
  self-checker uses z3 to check that the generated clause is a consequence. Note that this is generally
  insufficient as generated clauses are in principle required to only be satisfiability preserving.
  Proof checking and transformation operations is overall open ended.
  The log for the first commit introducing this change contains further information on the format.
- fix to re-entrancy bug in user propagator (thanks to Clemens Eisenhofer).
- handle _toExpr for quantified formulas in JS bindings

Version 4.11.1
==============
- skipped

Version 4.11.0
==============
- remove `Z3_bool`, `Z3_TRUE`, `Z3_FALSE` from the API. Use `bool`, `true`, `false` instead.
- z3++.h no longer includes `<sstream>` as it did not use it.
- add solver.axioms2files
  - prints negated theory axioms to files. Each file should be unsat
- add solver.lemmas2console
  - prints lemmas to the console.
- remove option smt.arith.dump_lemmas. It is replaced by solver.axioms2files
- add option smt.bv.reduce_size. 
  - it allows to apply incremental pre-processing of bit-vectors by identifying ranges that are known to be constant.
    This rewrite is beneficial, for instance, when bit-vectors are constrained to have many high-level bits set to 0.
- add feature to model-based projection for arithmetic to handle integer division.
- add fromString method to JavaScript solver object.

Version 4.10.2
==============
- fix regression #6194. It broke mod/rem/div reasoning.
- fix user propagator scope management for equality callbacks.

Version 4.10.1
==============
- fix implementation of mk_fresh in user propagator for Python API

Version 4.10.0
==============
- Added API Z3_enable_concurrent_dec_ref to be set by interfaces that
  use concurrent GC to manage reference counts. This feature is integrated
  with the OCaml bindings and fixes a regression introduced when OCaml
  transitioned to concurrent GC. Use of this feature for .Net and Java
  bindings is not integrated for this release. They use external queues
  that are unnecessarily complicated.
- Added pre-declared abstract datatype declarations to the context so
  that Z3_eval_smtlib2_string works with List examples.
- Fixed Java linking for MacOS Arm64.
- Added missing callback handlers in tactics for user-propagator,
  Thanks to Clemens Eisenhofer
- Tuning to Grobner arithmetic reasoning for smt.arith.solver=6
  (currently the default in most cases). The check for consistency
  modulo multiplication was updated in the following way:
  - polynomial equalities are extracted from Simplex tableau rows using
    a cone of influence algorithm. Rows where the basic variables were
    unbounded were previously included. Following the legacy implementation
    such rows are not included when building polynomial equations.
  - equations are pre-solved if they are linear and can be split
    into two groups one containing a single variable that has a
    lower (upper) bound, the other with more than two variables
    with upper (lower) bounds. This avoids losing bounds information
    during completion.
  - After (partial) completion, perform constant propagation for equalities
    of the form x = 0
  - After (partial) completion, perform factorization for factors of the
    form x*y*p = 0 where x, are variables, p is linear.
- Added support for declaring algebraic datatypes from the C++ interface.
    

Version 4.9.1
=============
- Bugfix release to ensure npm package works

Version 4.9.0
=============
- Native M1 (Mac ARM64) binaries and pypi distribution.
  - thanks to Isabel Garcia Contreras and Arie Gurfinkel for testing and fixes
- API for incremental parsing of assertions.
  A description of the feature is given by example here: https://github.com/Z3Prover/z3/commit/815518dc026e900392bf0d08ed859e5ec42d1e43
  It also allows incrementality at the level of adding assertions to the 
  solver object. 
- Fold/map for sequences:
  https://microsoft.github.io/z3guide/docs/guide/Sequences#map-and-fold
  At this point these functions are only exposed over the SMTLIB2 interface (and not programmatic API)
  maxdiff/mindiff on arrays are more likely to be deprecated
- User Propagator: 
  - Add functions and callbacks for external control over branching thanks to Clemens Eisenhofer
  - A functioning dotnet API for the User Propagator 
    https://github.com/Z3Prover/z3/blob/master/src/api/dotnet/UserPropagator.cs
- Java Script API
  - higher level object wrappers are available thanks to Kevin Gibbons and Olaf Tomalka
- Totalizers and RC2
  - The MaxSAT engine now allows to run RC2 with totalizer encoding.
    Totalizers are on by default as preliminary tests suggest this solves already 10% more problems on
    standard benchmarks. The option opt.rc2.totalizer (which by default is true) is used to control whether to use
    totalizer encoding or built-in cardinality constraints.
    The default engine is still maxres, so you have to set opt.maxsat_engine=rc2 to
    enable the rc2 option at this point. The engines maxres-bin and rc2bin are experimental should not be used
    (they are inferior to default options).
- Incremental constraints during optimization set option opt.incremental = true
  - The interface `Z3_optimize_register_model_eh` allows to monitor incremental results during optimization.
    It is now possible to also add constraints to the optimization context during search.
    You have to set the option opt.incremental=true to be able to add constraints. The option
    disables some pre-processing functionality that removes variables from the constraints. 

Version 4.8.17
==============
 - fix breaking bug in python interface for user propagator pop
 - integrate fixes to z3str3
 - initial support for nested algebraic datatypes with sequences
 - initiate map/fold operators on sequences - full integration for next releases
 - initiate maxdiff/mindiff on arrays - full integration for next releases

Examples:

```
(declare-sort Expr)
(declare-sort Var)
(declare-datatypes ((Stmt 0)) 
  (((Assignment (lval Var) (rval Expr)) 
    (If (cond Expr) (th Stmt) (el Stmt)) 
    (Seq (stmts (Seq Stmt))))))

(declare-const s Stmt)
(declare-const t Stmt)

(assert ((_ is Seq) t))
(assert ((_ is Seq) s))
(assert (= s (seq.nth (stmts t) 2)))
(assert (>= (seq.len (stmts s)) 5))
(check-sat)
(get-model)
(assert (= s (Seq (seq.unit s))))
(check-sat)
```
 
Version 4.8.16
==============
 - initial support for Darwin Arm64 (for M1, M2, .. users) thanks to zwimer and Anja Petkovi'c
   Komel for updates.
   Java is not yet supported, pypi native arm64 distributions are not yet supported.
   cmake dependency added to enable users to build for not-yet-supported platforms directly;
   specifically M1 seems to come up.
 - added functionality to user propagator decisions. Thanks to Clemens Eisenhofer.
 - added options for rc2 and maxres-bin to maxsat (note that there was no real difference measured
   from maxres on MaxSAT unweighted so default option is unchanged)
 - improved search for mutex constraints (at-most-1 constraints) among soft
   constraints for maxsat derived from approach used in rc2 sample.
 - multiple merges

Version 4.8.15
==============
 - elaborate user propagator API. Change id based scheme to expressions
 - includes a Web Assembly ffi API thanks to Kevin Gibbons

Version 4.8.14
==============
 - fixes Antimirov derivatives for intersections and unions required
   required for solving non-emptiness constraints.
 - includes x86 dll in nuget package for Windows.
 - exposes additional user propagator functionality 

Version 4.8.13
==============
The release integrates various bug fixes and tuning.

Version 4.8.12
==============
Release provided to fix git tag discrepancy issues with 4.8.11  


Version 4.8.11
==============
  - self-contained character theory, direct support for UTF8, Unicode character sets.
    Characters are by default unicode with an 18 bit range.
  - support for incremental any-time MaxSAT using the option opt.enable_lns. The API
    allows registering a callback function that is invoked on each incremental improvement
    to objectives. 

Version 4.8.10
==============
  - rewritten arithmetic solver replacing legacy arithmetic solver and on by default

Version 4.8.9
=============
- New features
  - significant improvements to regular expression solving
  - expose user theory plugin. It is a leaner user theory plugin that was once available.
    It allows for registering callbacks that react to when bit-vector and Boolean variables
    receive fixed values.
- Bug fixes
  - many
- Notes
  - the new arithmetic theory is turned on by default. It _does_ introduce regressions on 
    several scenarios, but has its own advantages. Users can turn on the old solver by setting smt.arith.solver=2.
    Depending on feedback, we may turn toggle this default setting again back to smt.arith.solver=2.

Version 4.8.8
=============
- New features
  - rewritten NIA (non-linear integer arithmetic) core solver 
    It is enabled in selected theories as default. 
    The legacy arithmetic solver remains the overall default in this release
    as the rewritten solver shows regressions (on mainly NRA problems).
  - recursive function representation without hoisting ite expressions. Issue #2601
  - model-based interpolation for quantifier-free UF, arithmetic 
  - Julia bindings over the C++ API, thanks to ahumenberger 
- Bug fixes
  - numerous, many based on extensive fuzz testing. 
    Thanks to 5hadowblad3, muchang, numairmansur, rainoftime, wintered
- Notes
  - recursive functions are unfolded with separate increments based on unsat core
    analysis of blocking literals that are separate for different recursive functions.   
  - the seq (string) solver has been revised in several ways and likely shows some 
    regressions in this release.

Version 4.8.7
=============
- New features
  - setting parameter on solver over the API by
    solver.smtlib2_log=<filename>
    enables tracing calls into the solver as SMTLIB2 commands.
    It traces, assert, push, pop, check_sat, get_consequences.
- Notes
  - various bug fixes
  - remove model_compress. Use model.compact
  - print weights with quantifiers when weight is != 1
  

Version 4.8.6
=============
- Notes
  - various bug fixes
  - built in support for PIP, thanks to Audrey Dutcher
  - VS compilation mode including misc flags for managed packages

Version 4.8.5
=============
- Notes
  - various bug fixes

Version 4.8.4
=============

- Notes
  - fixes bugs
  - a substantial update to how the seq theory solver handles regular
    expressions. Other performance improvements to the seq solver.
  - Managed .NET DLLs include dotnet standard 1.4 on supported platforms.
  - Windows Managed DLLs are strong signed in the released binaries.

Version 4.8.3
=============
- New features
  - Native handling of recursive function definitions, thanks to Simon Cruanes
  - PB rounding based option for conflict resolution when reasoning about PB constraints.
  - Access to numeral constants as a double from the native API.

- Notes
  - fixes several bugs discovered since the 4.8.1 release.

Version 4.8.2
=============
- Post-Release. 

Version 4.8.1
=============
- Release. Bug-fix for 4.8.0

Version 4.8.0
=============

- New requirements:
  - A breaking change to the API is that parsers for SMT-LIB2 formulas return a vector of 
    formulas as opposed to a conjunction of formulas. The vector of formulas correspond to 
    the set of "assert" instructions in the SMT-LIB input.

- New features
   - A parallel mode is available for select theories, including QF_BV. 
     By setting parallel.enable=true Z3 will spawn a number of worker threads proportional to the 
     number of available CPU cores to apply cube and conquer solving on the goal.
   - The SAT solver by default handle cardinality and PB constraints using a custom plugin 
     that operates directly on cardinality and PB constraints.
   - A "cube" interface is exposed over the solver API. 
   - Model conversion is first class over the textual API, such that subgoals created from running a 
     solver can be passed in text files and a model for the original formula can be recreated from the result.
   - This has also led to changes in how models are tracked over tactic subgoals. The API for 
     extracting models from apply_result have been replaced.
   - An optional mode handles xor constraints using a custom xor propagator. 
     It is off by default and its value not demonstrated.
   - The SAT solver includes new inprocessing techniques that are available during simplification.
     It performs asymmetric tautology elimination by default, and one can turn on more powerful inprocessing techniques 
     (known as ACCE, ABCE, CCE). Asymmetric branching also uses features introduced in Lingeling by exploiting binary implication graphs.
     Use sat.acce=true to enable the full repertoire of inprocessing methods. By default, clauses that are "eliminated" by acce are tagged
     as lemmas (redundant) and are garbage collected if their glue level is high.
   - Substantial overhaul of the spacer horn clause engine.
   - Added basic features to support Lambda bindings.
   - Added model compression to eliminate local function definitions in models when
     inlining them does not incur substantial overhead. The old behavior, where models are left
     uncompressed can be replayed by setting the top-level parameter model_compress=false.
   - Integration of a new solver for linear integer arithmetic and mixed linear integer arithmetic by Lev Nachmanson.
     It incorporates several improvements to QF_LIA solving based on
     . using a better LP engine, which is already the foundation for QF_LRA
     . including cuts based on Hermite Normal Form (thanks to approaches described 
       in "cuts from proofs" and "cutting the mix").
     . extracting integer solutions from LP solutions by tightening bounds selectively.
       We use a generalization of Bromberger and Weidenbach that allows avoiding selected
       bounds tightenings (https://easychair.org/publications/paper/qGfG).
     It solves significantly more problems in the QF_LIA category and may at this point also 
     be the best solver for your problem as well.
     The new solver is enabled only for select SMT-LIB logics. These include QF_LIA, QF_IDL, and QF_UFLIA.
     Other theories (still) use the legacy solver for arithmetic. You can enable the new solver by setting
     the parameter smt.arith.solver=6 to give it a spin.


- Removed features:
  - interpolation API
  - duality engine for constrained Horn clauses.
  - pdr engine for constrained Horn clauses. The engine's functionality has been 
    folded into spacer as one of optional strategies.
  - long deprecated API functions have been removed from z3_api.h
  
  

Version 4.7.1
=============

- New requirements:
  - uses stdbool and stdint as part of z3.

- New features:
  - none

- Removed features:
  - none

- Notes:
   This is a minor release prior to a set of planned major updates.
   It uses minor version 7 to indicate that the use of stdbool and
   stdint are breaking changes to consumers of the C-based API.

Version 4.6.0
=============

- New requirements:
  - C++11 capable compiler to build Z3.
  - C++ API now requires C++11 or newer.

- New features (including):
  - A new string solver from University of Waterloo
  - A new linear real arithmetic solver
  - Changed behavior for optimization commands from the SMT2 command-line interface.
    Objective values are no longer printed by default. They can be retrieved by
    issuing the command (get-objectives). Pareto front objectives are accessed by
    issuing multiple (check-sat) calls until it returns unsat.

- Removed features:
  - Removed support for SMT-LIB 1.x


Version 4.5.0
=============

- New features:
  - New theories of strings and sequences.
  - Consequence finding API "get-consequences" to compute
    set of consequences modulo hard constraints and set of
    assumptions. Optimized implementations provided for finite
    domains (QF_FD) and for most SMT logics. 
  - CMake build system (thanks @delcypher).
  - New API functions, including accessing assertions, parsing SMT-LIB benchmarks.
  - Updated and improved OCaml API (thanks @martin-neuhaeusser).
  - Updated and improved Java API (thanks @cheshire).
  - New resource limit facilities to avoid non-deterministic timeout behaviour.
    You can enable it from the command-line using the switch rlimit=<numeral>.
  - New bit-vector simplification and ackermannization 
    tactics (thanks @MikolasJanota, @nunoplopes).
  - QSAT: a new solver for satisfiability of quantified arithmetic formulas. 
    See: Bjorner, Janota: Playing with Quantified Satisfaction, LPAR 2016.
    This is the new default solver for logics LIA, LRA, NRA. It furthermore
    can be applied as a tactic on quantified formulas using algebraic 
    data-types (but excluding selector sub-terms because Z3 does not
    specify the semantics of applying a selector to a non-matching 
    constructor term). 
  - A specialized logic QF_FD and associated incremental solver 
    (that supports push/pop). 
    The QF_FD domain comprises of bit-vectors, enumeration data-types 
    used only in equalities, and bounded integers: Integers used in 
    QF_FD problems have to be constrained by a finite bound. 
  - Queries in the fixedpoint engine are now function symbols and not 
    formulas with free variables. This makes the association of
    free variables in the answers unambiguous. To emulate queries 
    over compound formulas, introduce a fresh predicate whose 
    arguments are the relevant free variables in the formula and add a rule
    that uses the fresh predicate in the head and formula in the body.
  - Minimization of unsat cores is available as an option for the SAT and SMT cores.
    By setting smt.core.minimize=true resp. sat.core.minimize=true
    cores produced by these modules are minimized.    

- A multitude of bugs has been fixed.


Version 4.4.1
=============

- This release marks the transition to the new GitHub fork & pull model; the unstable and contrib branches will be retired with all new contributions going into the master branch directly.

- A multitude of bugs has been fixed.

- New Feature: Support for optimization queries. The SMT-LIB2 command language
  is augmented by three commands (maximize <expr>), (minimize <expr) 
  and (assert-soft <expr> [:weight <numeral>] [:id <identifier>]). 
  The programmatic API also contains a dedicated context for solving 
  optimization queries. The TACAS 2015 tool paper by Bjorner, Dung and 
  Fleckenstein describes additional details and the online tutorial on 
  http://rise4fun.com/z3opt illustrates some uses.


Version 4.4.0
=============

- New feature: Support for the theory of floating-point numbers. This comes in the form of logics (QF_FP and QF_FPBV), tactics (qffp and qffpbv), as well as a theory plugin that allows theory combinations. Z3 supports the official SMT theory definition of FP (see http://smtlib.cs.uiowa.edu/theories/FloatingPoint.smt2) in SMT2 files, as well as all APIs.

- New feature: Stochastic local search engine for bit-vector formulas (see the qfbv-sls tactic).
  See also: Froehlich, Biere, Wintersteiger, Hamadi: Stochastic Local Search 
  for Satisfiability Modulo Theories, AAAI 2015.

- Upgrade: This release includes a brand new OCaml/ML API that is much better integrated with the build system, and hopefully also easier to use than the previous one.

- Fixed various bugs reported by Marc Brockschmidt, Venkatesh-Prasad Ranganath, Enric Carbonell, Morgan Deters, Tom Ball, Malte Schwerhoff, Amir Ebrahimi, Codeplex users rsas, clockish, Heizmann, susmitj, steimann, and Stackoverflow users user297886.


Version 4.3.2
=============

- Added preliminary support for the theory of floating point numbers (tactics qffpa, qffpabv, and logics QF_FPA, QF_FPABV).

- Added the interpolation features of iZ3, which are now integrated into Z3. 

- Fixed a multitude of bugs and inconsistencies that were reported to us either in person, by email, or on Codeplex. Of those that we do have records of, we would like to express our gratitude to:
    Vladimir Klebanov, Konrad Jamrozik, Nuno Lopes, Carsten Ruetz, Esteban Pavese, Tomer Weiss, Ilya Mironov, Gabriele Paganelli, Levent Erkok, Fabian Emmes, David Cok, Etienne Kneuss, Arlen Cox, Matt Lewis, Carsten Otto, Paul Jackson, David Monniaux, Markus Rabe, Martin Pluecker, Jasmin Blanchette, Jules Villard, Andrew Gacek, George Karpenkov, Joerg Pfaehler, and Pablo Aledo
    as well as the following Codeplex users that either reported bugs or took part in discussions:
xor88, parno, gario, Bauna, GManNickG, hanwentao, dinu09, fhowar, Cici, chinissai, barak_cohen, tvalentyn, krikunts, sukyoung, daramos, snedunuri, rajtendulkar, sonertari, nick8325, dvitek, amdragon, Beatgodes, dmonniaux, nickolai, DameNingen, mangpo, ttsiodras, blurium, sbrickey, pcodemod, indranilsaha, apanda, hougaardj, yoff, EfForEffort, Ansotegui, scottgw, viorelpreoteasa, idudka, c2855337, gario, jnfoster, omarmrivas, switicus, vosandi, foens, yzwwf, Heizmann, znajem, ilyagri, hougaardj, cliguda, rgrig, 92c849c1ccc707173, edmcman, cipher1024, MichaelvW, hellok, n00b42, ic3guy, Adorf, tvcsantos, zilongwang, Elarnon, immspw, jbridge99, danliew, zverlov, petross, jmh93, dradorf, fniksic, Heyji, cxcfan, henningg, wxlfrank, rvprasad, MovGP0, jackie1015, cowang, ffaghih, sanpra1989, gzchenyin, baitman, xjtulixiangyang, andreis, trucnguyenlam, erizzi, hanhchi, qsp, windypan, vadave, gradanne, SamWot, gsingh93, manjeetdahiya, zverlov, RaLa, and regehr.

- New parameter setting infrastructure. Now, it is possible to set parameter for Z3 internal modules. Several parameter names changed. Execute `z3 -p` for the new parameter list.

- Added get_version() and get_version_string() to Z3Py

- Added support for FreeBSD. Z3 can be compiled on FreeBSD using g++. 

- Added support for Python 3.x.

- Reverted to `(set-option :global-decls false)` as the default. In Z3 4.3.0 and Z3 4.3.1, this option was set to true.
  Thanks to Julien Henry for reporting this problem.

- Added `doc` directory and scripts for automatically generating the API documentation.

- Removed 'autoconf' dependency. We do not need to execute 'autoconf' and './configure' anymore to build Z3.

- Fixed incorrect result returned by Z3_solver_get_num_scopes. (Thanks to Herman Venter). This bug was introduced in Z3 4.3.0

- Java bindings. To enable them, we must use the option `--java` when executing the `mk_make.py` script. Example: `python scripts/mk_make.py --java`

- Fixed crash when parsing incorrect formulas. The crash was introduced when support for "arithmetic coercions" was added in Z3 4.3.0.

- Added new option to mk_make to allow users to specify where python bindings (Z3Py) will be installed. (Thanks to Dejan Jovanovic for reporting the problem).

- Fixed crash reported at http://z3.codeplex.com/workitem/10

- Removed auxiliary constants created by the nnf tactic from Z3 models.
  
- Fixed problem in the pretty printer. It was not introducing quotes for attribute names such as |foo:10|.

- Fixed bug when using assumptions (Thanks to Philippe Suter and Etienne Kneuss)
  Consider the following example:
      (assert F)
      (check-sat a)
      (check-sat)
  If 'F' is unsatisfiable independently of the assumption 'a', and 
  the inconsistency can be detected by just performing propagation,
  Then, version <= 4.3.1 may return
      unsat
      sat
  instead of
      unsat
      unsat
  We say may because 'F' may have other unsatisfiable cores.

- Fixed bug reported at http://stackoverflow.com/questions/13923316/unprintable-solver-model

- Fixed timers on Linux and FreeBSD.

- Fixed crash reported at http://z3.codeplex.com/workitem/11.

- Fixed bug reported at http://stackoverflow.com/questions/14307692/unknown-when-using-defs

- Relax check_logic procedure. Now, it accepts coercions (to_real) automatically introduced by Z3. (Thanks to Paul Jackson). This is a fix for http://z3.codeplex.com/workitem/19.

- Fixed http://stackoverflow.com/questions/14524316/z3-4-3-get-complete-model.

- Fixed bugs in the C++ API (Thanks to Andrey Kupriyanov).

- Fixed bug reported at http://z3.codeplex.com/workitem/23 (Thanks to Paul Jackson).

- Fixed bug reported at http://stackoverflow.com/questions/15226944/segmentation-fault-in-z3 (Thanks to Tianhai Liu).

Version 4.3.1
=============

- Added support for compiling Z3 using clang++ on Linux and OSX

- Added missing compilation option (-D _EXTERNAL_RELEASE) in release mode.

Version 4.3.0
=============

- Fixed bug during model construction reported by Heizmann (http://z3.codeplex.com/workitem/5)

- Remark: We skipped version 4.2 due to a mistake when releasing 4.1.2. Version 4.1.2 was accidentally tagged as 4.2. 
  Thanks to Claude Marche for reporting this issue.
  From now on, we are also officially moving to a 3 number naming convention for version numbers. 
  The idea is to have more frequent releases containing bug fixes. 

- The Z3 codebase was reorganized, we also have a new build system.
  In all platforms, we need Python 2.7.x installed.
  On Windows, you can build using Visual Studio Command Prompt.
  On Linux, OSX, Cygwin, you can build using g++. See README
  for compilation instructions.

- Removed tactic mip. It was based on code that was deleted during the code reorganization. 
     
- Fixed compilation problems with clang/llvm. Many thanks to Xi Wang for finding the problem, and suggesting the fix. 

- Now, Z3 automatically adds arithmetic coercions: to_real and to_int.
  Option (set-option :int-real-coercions false) disables this feature.
  If SMTLIB2_COMPLIANT=true in the command line, then :int-real-coercions is also set to false.

- SMTLIB2_COMPLIANT is false by default. Use command line option SMTLIB2_COMPLIANT=true to enable it back.

- Added "make install" and "make uninstall" to Makefile.in.
  
- Added "make install-z3py" and "make uninstall-z3py" to Makefile.in.

- Fixed crash/bug in the simplifier. The crash occurred when option ":sort-sums true" was used.

- Added "--with-python=<path>" option to configure script.

- Cleaned c++, maxsat, test_mapi examples.

- Move RELEASE_NOTES files to source code distribution.

- Removed unnecessary files from source code distribution.

- Removed unnecessary compilation modes from z3-prover.sln.

- Added Xor procedure to Z3Py.

- Z3 by default switches to an incremental solver when a Solver object is used to solve many queries.
  In the this version, we switch back to the tactic framework if the incremental solver returns "unknown".

- Allow negative numerals in the SMT 2.0 frontend. That is, Z3 SMT 2.0 parser now accepts numerals such as "-2". It is not needed to encode them as "(- 2)" anymore.
  The parser still accepts -foo as a symbol. That is, it is *not* a shorthand for (- foo).
  This feature is disabled when SMTLIB2_COMPLIANT=true is set in the command line.

- Now, Z3 can be compiled inside cygwin using gcc.

- Fixed bug in the unsat core generation.

First source code release (October 2, 2012)
===========================================

- Fixed bug in Z3Py. The method that builds Z3 applications could crash if one of the arguments have to be "casted" into the correct sort (Thanks to Dennis Yurichev).

- Fixed bug in datatype theory (Thanks to Ayrat).

- Fixed bug in the definition of MkEmptySet and MkFullSet in the .Net API.

- Display warning message and ignore option CASE_SPLIT=3,4 or 5 when auto configuration is enabled (AUTO_CONFIG=true) (Thanks Tobias from StackOverflow). 

- Made the predicates <, <=, > and >= chainable as defined in the SMT 2.0 standard (Thanks to Matthias Weiler). 

- Added missing Z3_decl_kind's for datatypes: Z3_OP_DT_CONSTRUCTOR, Z3_OP_DT_ACCESSOR, Z3_OP_DT_RECOGNISER.

- Added support for numbers in scientific notation at Z3_ast Z3_mk_numeral(__in Z3_context c, __in Z3_string numeral, __in Z3_sort ty).

- New builtin symbols in the arithmetic theory: pi, euler, sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh. The first two are constants, and the others are unary functions. These symbols are not available if a SMT 2.0 logic is specified (e.g., QF_LRA, QF_NRA, QF_LIA, etc) because these symbols are not defined in these logics. That is, the new symbols are only available if the logic is not specified.

Version 4.1
===========

- New OCAML API (Many thanks to Josh Berdine)

- CodeContracts in the .NET API (Many thanks to Francesco Logozzo).
  Users can now check whether they are using the .NET API correctly
  using <a href="http://msdn.microsoft.com/en-us/devlabs/dd491992">Clousot</a>.

- Added option :error-behavior. The default value is
  continued-execution. Now, users can force the Z3 SMT 2.0 frontend to
  exit whenever an error is reported.  They just have to use the
  command (set-option :error-behavior immediate-exit).

- Fixed bug in term-if-then-else elimination (Thanks to Artur Niewiadomski).  

- Fixed bug in difference logic detection code (Thanks to Dejan Jovanovic).
      
- Fixed bug in the pseudo-boolean preprocessor (Thanks to Adrien Champion).

- Fixed bug in bvsmod preprocessing rules (Thanks to Dejan Jovanovic).

- Fixed bug in Tactic tseitin-cnf (Thanks to Georg Hofferek).

- Added missing simplification step in nlsat. 

- Fixed bug in model construction for linear real arithmetic (Thanks to Marcello Bersani).

- Fixed bug in preprocessor that eliminated rational powers (e.g., (^ x (/ 1.0 2.0))), the bug affected only problems where the denominator was even (Thanks to Johannes Eriksson).

- Fixed bug in the k-th root operation in the algebraic number package. The result was correct, but the resulting polynomial could be incorrectly tagged as minimal and trigger nontermination on comparison operations. (Thanks to Johannes Eriksson).
  
- Fixed bug affecting problems containing patterns with n-ary arithmetic terms such as (p (+ x y 2)). This bug was introduced in Z3 4.0. (Thanks to Paul Jackson). 

- Fixed crash when running out of memory.

- Fixed crash reported by Alex Summers. The crash was happening on scripts that contain quantifiers, and use boolean formulas inside terms.

- Fixed crash in the MBQI module (Thanks to Stephan Falke).     

- Fixed bug in the E-matching engine. It was missing instances of multi-patterns (Thanks Alex Summers). 
      
- Fixed bug in Z3Py pretty printer.

- The pattern inference module does not generate warning messages by default anymore. This module was responsible for producing messages such as: "WARNING: failed to find a pattern for quantifier (quantifier id: k!199)". The option PI_WARNINGS=true can be used to enable these warning messages.

- Added missing return statements in z3++.h (Thanks to Daniel Neider).

- Removed support for TPTP5 and Simplify input formats. 

- Removed support for Z3 (low-level) input format. It is still available in the API.

- Removed support for "SMT 1.5" input format (aka .smtc files). This was a hybrid input format that was implemented while the SMT 2.0 standard was being designed. Users should move to SMT 2.0 format. Note that SMT 1.0 format is still available.

- Made tseitin-cnf tactic more "user friendly". It automatically applies required transformations needed to eliminate operators such as: and, distinct, etc.

- Implemented new PSC (principal subresultant coefficient) algorithm. This was one of the bottlenecks in the new nlsat solver/tactic.

Version 4.0
===========

Z3 4.0 is a major release. The main new features are:
- New C API, and it is backwards compatible, but several methods are marked as deprecated.
  In the new API, many solvers can be created in the same context. It also includes support
  for user defined strategies using Tactics. It also exposes a new interface for browsing models.

- A thin C++ layer around the C API that illustrates how to 
  leverage reference counting of ast objects.
  Several examples can be found in the directory 'examples/c++'.

- New .NET API together with updated version of the legacy .NET API. 
  The new .NET API supports the new features, Tactics, Solvers, Goals, 
  and integration of  with reference counting. Terms and sorts life-times 
  no longer requires a scoping discipline.

- <a class="el" href="http://rise4fun.com/Z3Py/tutorial/guide">Z3Py: Python interface for Z3</a>. 
  It covers all main features in the Z3 API.

- <a class="el" href="http://research.microsoft.com/apps/pubs/default.aspx?id=159549">NLSAT solver</a> for nonlinear arithmetic.  
       
- The PDR algorithm in muZ. 
   
- iZ3: an interpolating theorem prover built on top of Z3 (\ref iz3documentation). iZ3 is only available for Windows and Linux. 

- New logging infrastructure. Z3 logs are used to record every Z3 API call performed by your application.
  If you find a bug, just the log need to be sent to the Z3 team.
  The following APIs were removed: Z3_trace_to_file, Z3_trace_to_stderr, Z3_trace_to_stdout, Z3_trace_off. 
  The APIs: Z3_open_log, Z3_append_log and Z3_close_log do not receive a Z3_context anymore.
  When creating a log, you must invoke Z3_open_log before any other Z3 function call.
  The new logs are much more precise. 
  However, they still have two limitations. They are not useful for logging applications that use callbacks (e.g., theory plugins) 
  because the log interpreter does not have access to these callbacks.
  They are not precise for applications that are using multiple threads for processing multiple Z3 contexts.
        
- Z3 (for Linux and OSX) does not depend on GMP anymore.

- Z3 1.x backwards compatibility macros are defined in z3_v1.h. If you still use them, you have to explicitly include this file.
      
- Fixed all bugs reported at Stackoverflow.

Temporarily disabled features:

- User theories cannot be used with the new Solver API yet. Users may still use them with the deprecated solver API.

- Parallel Z3 is also disabled in this release. However, we have parallel combinators for creating strategies (See <a href="http://rise4fun.com/Z3/tutorial/strategies"> tutorial</a>).
      
The two features above will return in future releases. 

Here is a list of all <a class="el" href="deprecated.html">deprecated functions</a>.

Version 3.2
===========

This is a bug-fix refresh that fixes reported problems with 3.1.
        
- Added support for chainable and right associative attributes. 

- Fixed model generation for QBVF (aka UFBV) logic. Now, Z3 officially supports the logics BV and UFBV. 
  These are essentially QF_BV and QF_UFBV with quantifiers.

- Fixed bug in eval and get-value commands. Thanks to Levent Erkok.

- Fixed performance bug that was affecting VCC and Slayer. Thanks to Michal Moskal.

- Fixed time measurement on Linux. Thanks to Ayrat Khalimov.

- Fixed bug in destructive equality resolution (DER=true).
        
- Fixed bug in map operator in the theory of arrays. Thanks to Shaz Quadeer.
        
- Improved OCaml build scripts for Windows. Thanks to Josh Berdine.
        
- Fixed crash in MBQI (when Real variables were used). 

- Fixed bugs in quantifier elimination. Thanks to Josh Berdine.

- Fixed crash when an invalid datatype declaration is used.
        
- Fixed bug in the SMT2 parser.        

- Fixed crash in quick checker for quantified formulas. Thanks to Swen Jacobs.

- Fixed bug in the bvsmod simplifier. Thanks to Trevor Hansen.

- New APIs: \c Z3_substitute and \c Z3_substitute_vars.

- Fixed crash in MBQI. Thanks to Dejan Jovanovic.

Version 3.1
===========

This is a bug-fix refresh that fixes reported problems with 3.0.

- Fixed a bug in model generation. Thanks to Arlen Cox and Gordon Fraser.
        
- Fixed a bug in Z3_check_assumptions that prevented it from being used between satisfiable instances. Thanks to Krystof Hoder.

- Fixed two bugs in quantifier elimination. Thanks to Josh Berdine.        

- Fixed bugs in the preprocessor.

- Fixed performance bug in MBQI. Thanks to Kathryn Stolee.

- Improved strategy for QBVF (aka UFBV) logic.

- Added support for negative assumptions in the check-sat command.

Version 3.0
===========

- Fully compliant SMT-LIB 2.0 (SMT2) front-end. The old front-end is still available (command line option -smtc).
  The <a class="el" href="http://rise4fun.com/z3/tutorial/guide">Z3 Guide</a> describes the new front-end.

- Parametric inductive datatypes, and parametric user defined types.

- New SAT solver. Z3 can also read dimacs input formulas.

- New Bitvector (QF_BV) solver. The new solver is only available when using the new SMT2 front-end.

- Major performance improvements.

- New preprocessing stack.

- Performance improvements for linear and nonlinear arithmetic. The improvements are only available when using the SMT2 front-end.

- Added API for parsing SMT2 files.

- Fixed bug in AUTO_CONFIG=true. Thanks to Alberto Griggio.

- Fixed bug in the Z3 simplifier cache. It was not being reset during backtracking. Thanks to Alberto Griggio.

- Fixed many other bugs reported by users.

- Improved model-based quantifier instantiation (MBQI).

- New solver for Quantified Bitvector Logic (QBVF). 

- Z3 checks the user specified logic.
        
- <a href="http://www.cs.miami.edu/~tptp/">TPTP</a> 5 front-end.

Version 2.19
============

- In the SMT-LIB 1.0 frontend, Z3 will only display the model when requested by the user (MODEL=true).

- Fixed bug in the variable elimination preprocessor. Thanks to Alberto Griggio.
        
- Fixed bug in the expression strong simplifier. Thanks to Marko.

- Fixed bug in the Z3 auto configuration mode. Thanks to Vladimir Klebanov.

- Fixed bug when model generation is used in the context of user-defined-theories. Thanks to Philippe Suter.

- Fixed bug in quantifier elimination procedure. Thanks to Mikkel Larsen Pedersen.
        
- Improved speed of Z3 lexer for SMT-LIB frontend.

- Added a sample under examples/fixedpoints to illustrate using
	  the API for pluggable relations.

- Added an API method \c Z3_get_param_value for retrieving a 
  configuration value given a configuration parameter name.

Version 2.18
============

- Z3 has a new mode for solving fixed-point queries.
  It allows formulating Datalogish queries combined with constraints.
  <a class="el" href="http://rise4fun.com/z3py/tutorial/fixedpoints">Try it online</a>.

- Fixed bug that affects the array theory over the API using
  RELEVANCY=0. Thanks to Josh Berdine.

Version 2.17
============
      
- Z3 has new model finding capabilities for Quantified SMT formulas.
  The new features are enabled with <tt>MBQI=true</tt>.
  (Model Based Quantifier Instantiation). MBQI implements a
  counter-example based refinement loop, where candidate models are
  built and checked. When the model checking step fails, it creates new
  quantifier instantiations. The models are returned as simple
  functional programs. The new feature is also a decision procedure for
  many known decidable fragments such as: EPR (Effectively
  Propositional), Bradley&Manna&Sipma's Array Property Fragment (VMCAI'06), Almost
  Uninterpreted Fragment (Complete instantiation for quantified SMT formulas, CAV'09),
  McPeak&Necula's list fragment (CAV'05), QBVF (Quantified Bit-Vector Formulas FMCAD'10), 
  to cite a few. 
  MBQI is useful for checking the consistency of background axiomatizations,
  synthesizing functions, and building real counterexamples for
  verification tools. Users can constrain the search space by
  providing templates for function symbols, and constraints
  on the size of the universe and range of functions.
          
- Fixed bug in the command <tt>(simplify [expr])</tt> SMT-LIB 2.0 frontend.
        
- New model pretty printer. The old style is still available (option <tt>MODEL_V2=true</tt>).
  Z3 1.x style is also available (option <tt>MODEL_V1=true</tt>). 

- Removed \c ARRAY_PROPERTY option. It is subsumed by <tt>MBQI=true</tt>.

- Z3 uses the <tt>(set-logic [name])</tt> to configure itself.
  
- Assumptions can be provided to the \c check-sat command.
  The command <tt>(check-sat [assumptions])</tt> checks the satisfiability of the logical context modulo
  the given set of assumptions. The assumptions must be Boolean constants or
  the negation of Boolean constants. When the logical context is
  unsatisfiable modulo the given assumptions, Z3 will display a subset
  of the \c assumptions that contributed to the conflict. Lemmas
  learned during the execution of \c check-sat are preserved.

- Added command <tt>(echo [string])</tt> to the SMT-LIB 2.0 frontend.

- Z3 models explicitly include an interpretation for uninterpreted sorts.
  The interpretation is presented using the \c define-sort primitive.
  For example, 
  \code
      (define-sort S e_1 ... e_n)          
  \endcode
  states that the interpretation of the uninterpreted sort S is finite, and
  its universe is composed by values \c e_1, ..., \c e_n.

- Options \c WARNING and \c VERBOSE can be set in the SMT-LIB 2.0 frontend using
  the commands <tt>(set-option WARNING <flag>)</tt> <tt>(set-option VERBOSE <flag>)</tt>.
        
- Fixed unintentional side-effects in the Z3 pretty printer. Thanks to Swen Jacobs.

- Added interpreted constants of the form <tt>as-array[f]</tt>. The constants
  are used in models produced by Z3 to encode the interpretation of arrays. 
  The following axiom scheme axiomatizes the new constants:
  \code
     (forall (x1 S1) ... (xn Sn) (= (select as-array[f] x1 ... xn) (f x1 ... xn)))
  \endcode
        
- Fixed bug in the option MACRO_FINDER=true.

- Fixed bug in the <tt>(eval [expr])</tt> command in the SMT-LIB 2.0 frontend.

- Soundness bug in solver for array property fragment. Thanks to Trevor Hansen.

Version 2.16
============

The following bugs are fixed in this release:

- Bugs in quantifier elimination. Thanks to Mikkel Larsen Pedersen.

- Crash in non-linear arithmetic. Thanks to Trevor Hansen.

- Unsoundness in mixed integer-linear version using to_real. Thanks to Hirai.

- A crash and bugs in check_assumptions feature. Thanks to Akash Lal and Shaz Qadeer.

Version 2.15
============

The following bugs are fixed in this release:

- A bug in the quantifier elimination that affects nested
  alternating quantifiers that cannot be fully eliminated.

- A crash in proof generation. Thanks to Sascha Boehme.

Version 2.14
============

The following bugs are fixed in this release:

- A crash in arithmetic simplification. Thanks to Trevor Hansen.

- An unsoundness bug in the quantifier elimination. 
  It affects the equivalence of answers that are computed 
  in some cases.

- Incorrect printing of parameters and other values
  in SMT-LIB2 mode.
  Thanks to Tjark Weber.

Version 2.13
============

The following bugs are fixed in this release:

- Soundness bug in solver for array property fragment. Thanks to Trevor Hansen.

- Soundness bug introduced in macro expansion utilities. Thanks to Wintersteiger.

- Incorrect handling of QF_NRA. Thanks to Trevor Hansen.

- Mixup between SMT2 and SMT1 pretty printing formats. Thanks to Alvin Cheung and Tjark Weber.	

Version 2.12
============

News:
	
- Philippe Suter made a JNI binding available.
  There is also an existing Python binding by Sascha Boehme.
  See \ref contrib.

The following features are added in this release:

- Enable check_assumptions without enclosing push/pop.
  This resolves the limitation described 
  in \ref sub_release_limitations_2_0.

- Expose coefficients used in arithmetical proofs.

- Allow quantified theory axioms.

The following bugs are fixed in this release:

- Fixes to the SMT-LIB 2.0 pretty printing mode.

- Detect miss-annotated SMT-LIB benchmarks to avoid crashes when 
  using the wrong solvers. Thanks to Trevor Hansen.

- A digression in the managed API from 2.10 
  when passing null parameters.

- Crash/incorrect handling of inequalities over the reals
  during quantifier elimination.
  Thanks to Mikkel Larsen Pedersen.

- Bug in destructive equality resolution.
  Thanks to Sascha Boehme.

- Bug in initialization for x64_mt executable on SMT benchmarks.
  Thanks to Alvin Cheung.
	

Version 2.11
============

The following features are added in this release:

- SMT-LIB 2.0 parsing support for (! ..) in quantifiers and (_ ..).

- Allow passing strings to function and sort declarations in the .NET Theory builders.

- Add a parameter to the proof construct for theory lemmas to indicate which theory
  provided the lemma.
	
- More detailed proof production in rewrite steps.
  
The following bugs are fixed in this release:

- A bug in BV propagation. Thanks to Trevor Hansen.


Version 2.10
============

The following bugs are fixed in this release:

- Inconsistent printing of integer and real types from 
  the low level and SMT-LIB pretty printers. 
  Thanks to Sascha Boehme.

- Missing relevancy propagation and memory smash in
  user-theory plugins.
  Thanks to Stan Rosenberg.

Version 2.9
===========

The following bugs are fixed in this release:

- Incorrect constant folding of extraction for large bit-vectors.
  Thanks to Alvin.
	
- Z3 crashed when using patterns that are variables.
  Thanks to Michael Emmi.

- Unsound array property fragment handling of non-integer types.
  Thanks to Juergen Christ.

- The quantifier elimination procedure for data-types has
  been replaced.
  Thanks to Josh Berdine.

- Refresh 2.9.1: Add missing AssumeEq to the .NET managed API. 
  Thanks to Stan Rosenberg.

Version 2.8
===========

The following features have been added:

- User theories: The user can add theory solvers that
  get invoked by Z3's core during search.
  See also \ref theory_plugin_ex.

- SMT2 features: parse smt2 let bindings.
    
The following bugs are fixed in this release:
	
- Incorrect semantics of constant folding for (bvsmod 0 x), where
  x is positive, incorrect constant folding for bvsdiv, incorrect
  simplification of bvnor, bvnand, incorrect compilation of
  bvshl when using a shift amount that evaluates to the length
  of the bit-vector. Thanks to Trevor Hansen and Robert Brummayer. 

- Incorrect NNF conversion in linear quantifier elimination routines.
  Thanks to Josh Berdine.

- Missing constant folding of extraction for large bit-vectors.
  Thanks to Alvin.

- Missing APIs for bvredand and bvredor. 

Version 2.7
===========

The following features have been added:
	
- Partial support for SMT-LIB 2.0 format:
  Added declare-fun, define-fun, declare-sort, define-sort, get-value

- Added coercion function to_int and testing function is_int. 
  To coerce from reals to integers and to test whether a real is an integer.
  The function to_real was already supported.

- Added Z3_repeat to create the repetition of bit-vectors.

The following bugs are fixed in this release:
	
- Incorrect semantics of constant folding for bvsmod. 

- Incorrect semantics of constant folding for div/mod.
  Thanks to Sascha Boehme.	  

- Non-termination problem associated with option LOOKAHEAD=true.
  It gets set for QF_UF in auto-configuration mode.
  Thanks to Pierre-Christophe Bué.

- Incorrect axioms created for injective functions.
  Thanks to Sascha Boehme.

- Stack overflow during simplification of large nested
  bit-vector terms. Thanks to David Molnar.

- Crash in unsat-core generation when enabling SOLVER=true.
  Thanks to Lucas Cordeiro.

- Unlimited cache growth while simplifying bit-vectors.
  Thanks to Eric Landers.

- Crash when solving array property formulas using non-standard
  array operators. 
  Thanks to Sascha Boehme.

Version 2.6
===========

This release fixes a few bugs.
Thanks to Marko Kääramees for reporting a bug in the strong context simplifier and
to Josh Berdine. 

This release also introduces some new preprocessing features:

- More efficient destructive equality resolution DER=true.
        
- DISTRIBUTE_FORALL=true (distributes universal quantifiers over conjunctions, this transformation may affect pattern inference).

- Rewriter that uses universally quantified equations PRE_DEMODULATOR=true (yes, the option name is not good, we will change it in a future release).

- REDUCE_ARGS=true (this transformation is essentially a partial ackermannization for functions where a particular argument is always an interpreted value).

- Better support for macro detection (a macro is a universally quantified formula of the form Forall X. F(X) = T[X]). We also change the option name, now it is called MACRO_FINDER=true.

- ELIM_QUANTIFIERS=true enables quantifier elimination methods. Previous variants called QUANT_ARITH are deprecated.

Version 2.5
===========

This release introduces the following features:

- STRONG_CONTEXT_SIMPLIFIER=true allows simplifying sub-formulas
  to true/false depending on context-dependent information.
  The approach that we use is described on
  the <a href="http://community.research.microsoft.com/forums/p/4493/8140.aspx">
  Microsoft Z3 forum</a>.

- Some parameter values can be updated over the API. This functionality is called
  <tt>Z3_update_param_value</tt> in the C API. This is particularly useful
  for turning the strong context simplifier on and off.  
 
It also fixes bugs reported by Enric Rodríguez Carbonell, 
Nuno Lopes, Josh Berdine, Ethan Jackson, Rob Quigley and 
Lucas Cordeiro.

Version 2.4
===========
        
This release introduces the following features:

- Labeled literals for the SMT-LIB format. 
  The Simplify format has supported labeled formulas 
  to simplify displaying counter-examples. 
  Section \ref smtlib_labels explains how labels are now
  supported in the SMT-LIB format.

- Preliminary support for SMT-LIB2

It fixes the following bugs:

- Bug in non-linear arithmetic routines.

- Crash observed a class of modular integer arithmetic formulas.

- Incomplete saturation leading to incorrectly sat labeling.

- Crash in the bit-vector procedure when using int2bv and bv2int.

Thanks to Michal Moskal, Sascha Boehme and Ethan Jackson.

Version 2.3
===========

This release introduces the following features:

- F# Quotation utilities. The release contains a new directory 'utils'. 
  It contains utilities built on top of Z3. The main one is support for
  translating F# quoted expressions into Z3 formulas.

- QUANT_ARITH configuration. 
  Complete quantifier-elimination simplification for linear real and linear integer
  arithmetic. QUANT_ARITH=1 uses Ferrante/Rackhoff for reals and Cooper's method for integers.
  QUANT_ARITH=2 uses Fourier-Motzkin for reals and the Omega test for integers.

It fixes the following bugs:

- Incorrect simplification of map over store in the extended array theory. Reported by Catalin Hritcu.

- Incomplete handling of equality propagation with constant arrays. Reported by Catalin Hritcu.

- Crash in bit-vector theory.
 
- Incorrectness in proof reconstruction for quantifier manipulation.

Thanks to Catalin Hritcu, Nikolai Tillmann and Sascha Boehme.

Version 2.2
===========

This release fixes minor bugs. 
It introduces some additional features in the SMT-LIB front-end 
to make it easier to parse new operators in the theory of arrays.
These are described in \ref smtlibext. 

Version 2.1
===========

This is a bug fix release.
Many thanks to Robert Brummayer, Carine Pascal, François Remy, 
Rajesh K Karmani, Roberto Lublinerman and numerous others for their 
feedback and bug reports.

Version 2.0
===========

- <a href="http://research.microsoft.com/en-us/um/people/leonardo/parallel_z3.pdf">Parallel Z3</a>. 
  Thanks to Christoph Wintersteiger there is a binary 
  supporting running multiple instances of Z3 from different threads,
  but more interestingly, also making use of multiple cores for 
  a single formula. 

- Check Assumptions.
  The binary API exposes a new call #Z3_check_assumptions, which
  allows passing in additional assumptions while checking for 
  consistency of the already asserted formulas.
  The API function returns a subset of the assumptions that were
  used in an unsatisfiable core. It also returns an optional
  proof object.

- Proof Objects.
  The #Z3_check_assumptions returns a proof object if
  the configuration flag PROOF_MODE is set to 1 or 2.

- Partial support for non-linear arithmetic. 
  The support uses support for computing Groebner bases.
  It allows solving some, but far from all, formulas using 
  polynomials over the reals. Uses should be aware that the 
  support for non-linear arithmetic (over the reals) is not complete in Z3.
       
- Recursive data-types.
  The theory of well-founded recursive data-types is supported
  over the binary APIs. It supports ground satisfiability checking
  for tuples, enumeration types (scalars), 
  lists and mutually recursive data-types.
