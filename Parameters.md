## Module pi

Description: pattern inference (heuristics) for universal formulas (without annotation)
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
arith | unsigned int  |  0 - do not infer patterns with arithmetic terms, 1 - use patterns with arithmetic terms if there is no other pattern, 2 - always use patterns with arithmetic terms | 1
arith_weight | unsigned int  |  default weight for quantifiers where the only available pattern has nested arithmetic terms | 5
block_loop_patterns | bool  |  block looping patterns during pattern inference | true
max_multi_patterns | unsigned int  |  when patterns are not provided, the prover uses a heuristic to infer them, this option sets the threshold on the number of extra multi-patterns that can be created; by default, the prover creates at most one multi-pattern when there is no unary pattern | 0
non_nested_arith_weight | unsigned int  |  default weight for quantifiers where the only available pattern has non nested arithmetic terms | 10
pull_quantifiers | bool  |  pull nested quantifiers, if no pattern was found | true
use_database | bool  |  use pattern database | false
warnings | bool  |  enable/disable warning messages in the pattern inference module | false

## Module tactic

Description: tactic parameters
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
blast_term_ite.max_inflation | unsigned int  |  multiplicative factor of initial term size. | 4294967295
blast_term_ite.max_steps | unsigned int  |  maximal number of steps allowed for tactic. | 4294967295
default_tactic | symbol  |  overwrite default tactic in strategic solver | 
propagate_values.max_rounds | unsigned int  |  maximal number of rounds to propagate values. | 4
solve_eqs.context_solve | bool  |  solve equalities within disjunctions. | true
solve_eqs.ite_solver | bool  |  use if-then-else solvers. | true
solve_eqs.max_occs | unsigned int  |  maximum number of occurrences for considering a variable for gaussian eliminations. | 4294967295
solve_eqs.theory_solver | bool  |  use theory solvers. | true

## Module pp

Description: pretty printer
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
bounded | bool  |  ignore characters exceeding max width | false
bv_literals | bool  |  use Bit-Vector literals (e.g, #x0F and #b0101) during pretty printing | true
bv_neg | bool  |  use bvneg when displaying Bit-Vector literals where the most significant bit is 1 | false
decimal | bool  |  pretty print real numbers using decimal notation (the output may be truncated). Z3 adds a ? if the value is not precise | false
decimal_precision | unsigned int  |  maximum number of decimal places to be used when pp.decimal=true | 10
fixed_indent | bool  |  use a fixed indentation for applications | false
flat_assoc | bool  |  flat associative operators (when pretty printing SMT2 terms/formulas) | true
fp_real_literals | bool  |  use real-numbered floating point literals (e.g, +1.0p-1) during pretty printing | false
max_depth | unsigned int  |  max. term depth (when pretty printing SMT2 terms/formulas) | 5
max_indent | unsigned int  |  max. indentation in pretty printer | 4294967295
max_num_lines | unsigned int  |  max. number of lines to be displayed in pretty printer | 4294967295
max_ribbon | unsigned int  |  max. ribbon (width - indentation) in pretty printer | 80
max_width | unsigned int  |  max. width in pretty printer | 80
min_alias_size | unsigned int  |  min. size for creating an alias for a shared term (when pretty printing SMT2 terms/formulas) | 10
pretty_proof | bool  |  use slower, but prettier, printer for proofs | false
simplify_implies | bool  |  simplify nested implications for pretty printing | true
single_line | bool  |  ignore line breaks when true | false

## Module sat

Description: propositional SAT solver
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
abce | bool  |  eliminate blocked clauses using asymmetric literals | false
acce | bool  |  eliminate covered clauses using asymmetric added literals | false
anf | bool  |  enable ANF based simplification in-processing | false
anf.delay | unsigned int  |  delay ANF simplification by in-processing round | 2
anf.exlin | bool  |  enable extended linear simplification | false
asymm_branch | bool  |  asymmetric branching | true
asymm_branch.all | bool  |  asymmetric branching on all literals per clause | false
asymm_branch.delay | unsigned int  |  number of simplification rounds to wait until invoking asymmetric branch simplification | 1
asymm_branch.limit | unsigned int  |  approx. maximum number of literals visited during asymmetric branching | 100000000
asymm_branch.rounds | unsigned int  |  maximal number of rounds to run asymmetric branch simplifications if progress is made | 2
asymm_branch.sampled | bool  |  use sampling based asymmetric branching based on binary implication graph | true
ate | bool  |  asymmetric tautology elimination | true
backtrack.conflicts | unsigned int  |  number of conflicts before enabling chronological backtracking | 4000
backtrack.scopes | unsigned int  |  number of scopes to enable chronological backtracking | 100
bca | bool  |  blocked clause addition - add blocked binary clauses | false
bce | bool  |  eliminate blocked clauses | false
bce_at | unsigned int  |  eliminate blocked clauses only once at the given simplification round | 2
bce_delay | unsigned int  |  delay eliminate blocked clauses until simplification round | 2
binspr | bool  |  enable SPR inferences of binary propagation redundant clauses. This inprocessing step eliminates models | false
blocked_clause_limit | unsigned int  |  maximum number of literals visited during blocked clause elimination | 100000000
branching.anti_exploration | bool  |  apply anti-exploration heuristic for branch selection | false
branching.heuristic | symbol  |  branching heuristic vsids, chb | vsids
burst_search | unsigned int  |  number of conflicts before first global simplification | 100
cardinality.encoding | symbol  |  encoding used for at-most-k constraints: grouped, bimander, ordered, unate, circuit | grouped
cardinality.solver | bool  |  use cardinality solver | true
cce | bool  |  eliminate covered clauses | false
core.minimize | bool  |  minimize computed core | false
core.minimize_partial | bool  |  apply partial (cheap) core minimization | false
cut | bool  |  enable AIG based simplification in-processing | false
cut.aig | bool  |  extract aigs (and ites) from cluases for cut simplification | false
cut.delay | unsigned int  |  delay cut simplification by in-processing round | 2
cut.dont_cares | bool  |  integrate dont cares with cuts | true
cut.force | bool  |  force redoing cut-enumeration until a fixed-point | false
cut.lut | bool  |  extract luts from clauses for cut simplification | false
cut.npn3 | bool  |  extract 3 input functions from clauses for cut simplification | false
cut.redundancies | bool  |  integrate redundancy checking of cuts | true
cut.xor | bool  |  extract xors from clauses for cut simplification | false
ddfw.init_clause_weight | unsigned int  |  initial clause weight for DDFW local search | 8
ddfw.reinit_base | unsigned int  |  increment basis for geometric backoff scheme of re-initialization of weights | 10000
ddfw.restart_base | unsigned int  |  number of flips used a starting point for hessitant restart backoff | 100000
ddfw.threads | unsigned int  |  number of ddfw threads to run in parallel with sat solver | 0
ddfw.use_reward_pct | unsigned int  |  percentage to pick highest reward variable when it has reward 0 | 15
ddfw_search | bool  |  use ddfw local search instead of CDCL | false
dimacs.core | bool  |  extract core from DIMACS benchmarks | false
drat.activity | bool  |  dump variable activities | false
drat.binary | bool  |  use Binary DRAT output format | false
drat.check_sat | bool  |  build up internal trace, check satisfying model | false
drat.check_unsat | bool  |  build up internal proof and check | false
drat.file | symbol  |  file to dump DRAT proofs | 
drup.trim | bool  |  build and trim drup proof | false
dyn_sub_res | bool  |  dynamic subsumption resolution for minimizing learned clauses | true
elim_vars | bool  |  enable variable elimination using resolution during simplification | true
elim_vars_bdd | bool  |  enable variable elimination using BDD recompilation during simplification | true
elim_vars_bdd_delay | unsigned int  |  delay elimination of variables using BDDs until after simplification round | 3
enable_pre_simplify | bool  |  enable pre simplifications before the bounded search | false
euf | bool  |  enable euf solver (this feature is preliminary and not ready for general consumption) | false
force_cleanup | bool  |  force cleanup to remove tautologies and simplify clauses | false
gc | symbol  |  garbage collection strategy: psm, glue, glue_psm, dyn_psm | glue_psm
gc.burst | bool  |  perform eager garbage collection during initialization | false
gc.defrag | bool  |  defragment clauses when garbage collecting | true
gc.increment | unsigned int  |  increment to the garbage collection threshold | 500
gc.initial | unsigned int  |  learned clauses garbage collection frequency | 20000
gc.k | unsigned int  |  learned clauses that are inactive for k gc rounds are permanently deleted (only used in dyn_psm) | 7
gc.small_lbd | unsigned int  |  learned clauses with small LBD are never deleted (only used in dyn_psm) | 3
inprocess.max | unsigned int  |  maximal number of inprocessing passes | 4294967295
inprocess.out | symbol  |  file to dump result of the first inprocessing step and exit | 
local_search | bool  |  use local search instead of CDCL | false
local_search_dbg_flips | bool  |  write debug information for number of flips | false
local_search_mode | symbol  |  local search algorithm, either default wsat or qsat | wsat
local_search_threads | unsigned int  |  number of local search threads to find satisfiable solution | 0
lookahead.cube.cutoff | symbol  |  cutoff type used to create lookahead cubes: depth, freevars, psat, adaptive_freevars, adaptive_psat | depth
lookahead.cube.depth | unsigned int  |  cut-off depth to create cubes. Used when lookahead.cube.cutoff is depth. | 1
lookahead.cube.fraction | double  |  adaptive fraction to create lookahead cubes. Used when lookahead.cube.cutoff is adaptive_freevars or adaptive_psat | 0.4
lookahead.cube.freevars | double  |  cube free variable fraction. Used when lookahead.cube.cutoff is freevars | 0.8
lookahead.cube.psat.clause_base | double  |  clause base for PSAT cutoff | 2
lookahead.cube.psat.trigger | double  |  trigger value to create lookahead cubes for PSAT cutoff. Used when lookahead.cube.cutoff is psat | 5
lookahead.cube.psat.var_exp | double  |  free variable exponent for PSAT cutoff | 1
lookahead.delta_fraction | double  |  number between 0 and 1, the smaller the more literals are selected for double lookahead | 1.0
lookahead.double | bool  |  enable doubld lookahead | true
lookahead.global_autarky | bool  |  prefer to branch on variables that occur in clauses that are reduced | false
lookahead.preselect | bool  |  use pre-selection of subset of variables for branching | false
lookahead.reward | symbol  |  select lookahead heuristic: ternary, heule_schur (Heule Schur), heuleu (Heule Unit), unit, or march_cu | march_cu
lookahead.use_learned | bool  |  use learned clauses when selecting lookahead literal | false
lookahead_scores | bool  |  extract lookahead scores. A utility that can only be used from the DIMACS front-end | false
lookahead_simplify | bool  |  use lookahead solver during simplification | false
lookahead_simplify.bca | bool  |  add learned binary clauses as part of lookahead simplification | true
max_conflicts | unsigned int  |  maximum number of conflicts | 4294967295
max_memory | unsigned int  |  maximum amount of memory in megabytes | 4294967295
minimize_lemmas | bool  |  minimize learned clauses | true
override_incremental | bool  |  override incremental safety gaps. Enable elimination of blocked clauses and variables even if solver is reused | false
pb.lemma_format | symbol  |  generate either cardinality or pb lemmas | cardinality
pb.min_arity | unsigned int  |  minimal arity to compile pb/cardinality constraints to CNF | 9
pb.resolve | symbol  |  resolution strategy for boolean algebra solver: cardinality, rounding | cardinality
pb.solver | symbol  |  method for handling Pseudo-Boolean constraints: circuit (arithmetical circuit), sorting (sorting circuit), totalizer (use totalizer encoding), binary_merge, segmented, solver (use native solver) | solver
phase | symbol  |  phase selection strategy: always_false, always_true, basic_caching, random, caching | caching
phase.sticky | bool  |  use sticky phase caching | true
prob_search | bool  |  use probsat local search instead of CDCL | false
probing | bool  |  apply failed literal detection during simplification | true
probing_binary | bool  |  probe binary clauses | true
probing_cache | bool  |  add binary literals as lemmas | true
probing_cache_limit | unsigned int  |  cache binaries unless overall memory usage exceeds cache limit | 1024
probing_limit | unsigned int  |  limit to the number of probe calls | 5000000
propagate.prefetch | bool  |  prefetch watch lists for assigned literals | true
random_freq | double  |  frequency of random case splits | 0.01
random_seed | unsigned int  |  random seed | 0
reorder.activity_scale | unsigned int  |  scaling factor for activity update | 100
reorder.base | unsigned int  |  number of conflicts per random reorder  | 4294967295
reorder.itau | double  |  inverse temperature for softmax | 4.0
rephase.base | unsigned int  |  number of conflicts per rephase  | 1000
resolution.cls_cutoff1 | unsigned int  |  limit1 - total number of problems clauses for the second cutoff of Boolean variable elimination | 100000000
resolution.cls_cutoff2 | unsigned int  |  limit2 - total number of problems clauses for the second cutoff of Boolean variable elimination | 700000000
resolution.limit | unsigned int  |  approx. maximum number of literals visited during variable elimination | 500000000
resolution.lit_cutoff_range1 | unsigned int  |  second cutoff (total number of literals) for Boolean variable elimination, for problems containing less than res_cls_cutoff1 clauses | 700
resolution.lit_cutoff_range2 | unsigned int  |  second cutoff (total number of literals) for Boolean variable elimination, for problems containing more than res_cls_cutoff1 and less than res_cls_cutoff2 | 400
resolution.lit_cutoff_range3 | unsigned int  |  second cutoff (total number of literals) for Boolean variable elimination, for problems containing more than res_cls_cutoff2 | 300
resolution.occ_cutoff | unsigned int  |  first cutoff (on number of positive/negative occurrences) for Boolean variable elimination | 10
resolution.occ_cutoff_range1 | unsigned int  |  second cutoff (number of positive/negative occurrences) for Boolean variable elimination, for problems containing less than res_cls_cutoff1 clauses | 8
resolution.occ_cutoff_range2 | unsigned int  |  second cutoff (number of positive/negative occurrences) for Boolean variable elimination, for problems containing more than res_cls_cutoff1 and less than res_cls_cutoff2 | 5
resolution.occ_cutoff_range3 | unsigned int  |  second cutoff (number of positive/negative occurrences) for Boolean variable elimination, for problems containing more than res_cls_cutoff2 | 3
restart | symbol  |  restart strategy: static, luby, ema or geometric | ema
restart.emafastglue | double  |  ema alpha factor for fast moving average | 0.03
restart.emaslowglue | double  |  ema alpha factor for slow moving average | 1e-05
restart.factor | double  |  restart increment factor for geometric strategy | 1.5
restart.fast | bool  |  use fast restart approach only removing less active literals. | true
restart.initial | unsigned int  |  initial restart (number of conflicts) | 2
restart.margin | double  |  margin between fast and slow restart factors. For ema | 1.1
restart.max | unsigned int  |  maximal number of restarts. | 4294967295
retain_blocked_clauses | bool  |  retain blocked clauses as lemmas | true
scc | bool  |  eliminate Boolean variables by computing strongly connected components | true
scc.tr | bool  |  apply transitive reduction, eliminate redundant binary clauses | true
search.sat.conflicts | unsigned int  |  period for solving for sat (in number of conflicts) | 400
search.unsat.conflicts | unsigned int  |  period for solving for unsat (in number of conflicts) | 400
simplify.delay | unsigned int  |  set initial delay of simplification by a conflict count | 0
subsumption | bool  |  eliminate subsumed clauses | true
subsumption.limit | unsigned int  |  approx. maximum number of literals visited during subsumption (and subsumption resolution) | 100000000
threads | unsigned int  |  number of parallel threads to use | 1
variable_decay | unsigned int  |  multiplier (divided by 100) for the VSIDS activity increment | 110

## Module solver

Description: solver parameters
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
axioms2files | bool  |  print negated theory axioms to separate files during search | false
cancel_backup_file | symbol  |  file to save partial search state if search is canceled | 
lemmas2console | bool  |  print lemmas during search | false
smtlib2_log | symbol  |  file to save solver interaction | 
timeout | unsigned int  |  timeout on the solver object; overwrites a global timeout | 4294967295

## Module opt

Description: optimization parameters
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
dump_benchmarks | bool  |  dump benchmarks for profiling | false
dump_models | bool  |  display intermediary models to stdout | false
elim_01 | bool  |  eliminate 01 variables | true
enable_core_rotate | bool  |  enable core rotation to both sample cores and correction sets | false
enable_lns | bool  |  enable LNS during weighted maxsat | false
enable_sat | bool  |  enable the new SAT core for propositional constraints | true
enable_sls | bool  |  enable SLS tuning during weighted maxsat | false
incremental | bool  |  set incremental mode. It disables pre-processing and enables adding constraints in model event handler | false
lns_conflicts | unsigned int  |  initial conflict count for LNS search | 1000
maxlex.enable | bool  |  enable maxlex heuristic for lexicographic MaxSAT problems | true
maxres.add_upper_bound_block | bool  |  restict upper bound with constraint | false
maxres.hill_climb | bool  |  give preference for large weight cores | true
maxres.max_core_size | unsigned int  |  break batch of generated cores if size reaches this number | 3
maxres.max_correction_set_size | unsigned int  |  allow generating correction set constraints up to maximal size | 3
maxres.max_num_cores | unsigned int  |  maximal number of cores per round | 200
maxres.maximize_assignment | bool  |  find an MSS/MCS to improve current assignment | false
maxres.pivot_on_correction_set | bool  |  reduce soft constraints if the current correction set is smaller than current core | true
maxres.wmax | bool  |  use weighted theory solver to constrain upper bounds | false
maxsat_engine | symbol  |  select engine for maxsat: 'core_maxsat', 'wmax', 'maxres', 'pd-maxres', 'maxres-bin', 'rc2' | maxres
optsmt_engine | symbol  |  select optimization engine: 'basic', 'symba' | basic
pb.compile_equality | bool  |  compile arithmetical equalities into pseudo-Boolean equality (instead of two inequalites) | false
pp.neat | bool  |  use neat (as opposed to less readable, but faster) pretty printer when displaying context | true
pp.wcnf | bool  |  print maxsat benchmark into wcnf format | false
priority | symbol  |  select how to priortize objectives: 'lex' (lexicographic), 'pareto', 'box' | lex
rc2.totalizer | bool  |  use totalizer for rc2 encoding | true
rlimit | unsigned int  |  resource limit (0 means no limit) | 0
solution_prefix | symbol  |  path prefix to dump intermediary, but non-optimal, solutions | 
timeout | unsigned int  |  timeout (in milliseconds) (UINT_MAX and 0 mean no timeout) | 4294967295

## Module parallel

Description: parameters for parallel solver
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
conquer.backtrack_frequency | unsigned int  |  frequency to apply core minimization during conquer | 10
conquer.batch_size | unsigned int  |  number of cubes to batch together for fast conquer | 100
conquer.delay | unsigned int  |  delay of cubes until applying conquer | 10
conquer.restart.max | unsigned int  |  maximal number of restarts during conquer phase | 5
enable | bool  |  enable parallel solver by default on selected tactics (for QF_BV) | false
simplify.exp | double  |  restart and inprocess max is multiplied by simplify.exp ^ depth | 1
simplify.inprocess.max | unsigned int  |  maximal number of inprocessing steps during simplification | 2
simplify.max_conflicts | unsigned int  |  maximal number of conflicts during simplifcation phase | 4294967295
simplify.restart.max | unsigned int  |  maximal number of restarts during simplification phase | 5000
threads.max | unsigned int  |  caps maximal number of threads below the number of processors | 10000

## Module nnf

Description: negation normal form
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
ignore_labels | bool  |  remove/ignore labels in the input formula, this option is ignored if proofs are enabled | false
max_memory | unsigned int  |  maximum amount of memory in megabytes | 4294967295
mode | symbol  |  NNF translation mode: skolem (skolem normal form), quantifiers (skolem normal form + quantifiers in NNF), full | skolem
sk_hack | bool  |  hack for VCC | false

## Module algebraic

Description: real algebraic number package. Non-default parameter settings are not supported
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
factor | bool  |  use polynomial factorization to simplify polynomials representing algebraic numbers | true
factor_max_prime | unsigned int  |  parameter for the polynomial factorization procedure in the algebraic number module. Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. This parameter limits the maximum prime number p to be used in the first step | 31
factor_num_primes | unsigned int  |  parameter for the polynomial factorization procedure in the algebraic number module. Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. The search space may be reduced by factoring the polynomial in different GF(p)'s. This parameter specify the maximum number of finite factorizations to be considered, before lifiting and searching | 1
factor_search_size | unsigned int  |  parameter for the polynomial factorization procedure in the algebraic number module. Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. This parameter can be used to limit the search space | 5000
min_mag | unsigned int  |  Z3 represents algebraic numbers using a (square-free) polynomial p and an isolating interval (which contains one and only one root of p). This interval may be refined during the computations. This parameter specifies whether to cache the value of a refined interval or not. It says the minimal size of an interval for caching purposes is 1/2^16 | 16
zero_accuracy | unsigned int  |  one of the most time-consuming operations in the real algebraic number module is determining the sign of a polynomial evaluated at a sample point with non-rational algebraic number values. Let k be the value of this option. If k is 0, Z3 uses precise computation. Otherwise, the result of a polynomial evaluation is considered to be 0 if Z3 can show it is inside the interval (-1/2^k, 1/2^k) | 0

## Module combined_solver

Description: combines two solvers: non-incremental (solver1) and incremental (solver2)
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
ignore_solver1 | bool  |  if true, solver 2 is always used | false
solver2_timeout | unsigned int  |  fallback to solver 1 after timeout even when in incremental model | 4294967295
solver2_unknown | unsigned int  |  what should be done when solver 2 returns unknown: 0 - just return unknown, 1 - execute solver 1 if quantifier free problem, 2 - execute solver 1 | 1

## Module rcf

Description: real closed fields
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
clean_denominators | bool  |  clean denominators before root isolation | true
inf_precision | unsigned int  |  a value k that is the initial interval size (i.e., (0, 1/2^l)) used as an approximation for infinitesimal values | 24
initial_precision | unsigned int  |  a value k that is the initial interval size (as 1/2^k) when creating transcendentals and approximated division | 24
lazy_algebraic_normalization | bool  |  during sturm-seq and square-free polynomial computations, only normalize algebraic polynomial expressions when the defining polynomial is monic | true
max_precision | unsigned int  |  during sign determination we switch from interval arithmetic to complete methods when the interval size is less than 1/2^k, where k is the max_precision | 128
use_prem | bool  |  use pseudo-remainder instead of remainder when computing GCDs and Sturm-Tarski sequences | true
ERROR: unknown module 'rewriter, description: new formula simplification module used in the tactic framework'

## Module ackermannization

Description: solving UF via ackermannization
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
eager | bool  |  eagerly instantiate all congruence rules | true
inc_sat_backend | bool  |  use incremental SAT | false
sat_backend | bool  |  use SAT rather than SMT in qfufbv_ackr_tactic | false

## Module nlsat

Description: nonlinear solver
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
check_lemmas | bool  |  check lemmas on the fly using an independent nlsat solver | false
factor | bool  |  factor polynomials produced during conflict resolution. | true
inline_vars | bool  |  inline variables that can be isolated from equations (not supported in incremental mode) | false
lazy | unsigned int  |  how lazy the solver is. | 0
log_lemmas | bool  |  display lemmas as self-contained SMT formulas | false
max_conflicts | unsigned int  |  maximum number of conflicts. | 4294967295
max_memory | unsigned int  |  maximum amount of memory in megabytes | 4294967295
minimize_conflicts | bool  |  minimize conflicts | false
randomize | bool  |  randomize selection of a witness in nlsat. | true
reorder | bool  |  reorder variables. | true
seed | unsigned int  |  random seed. | 0
shuffle_vars | bool  |  use a random variable order. | false
simplify_conflicts | bool  |  simplify conflicts using equalities before resolving them in nlsat solver. | true


## Module fp

Description: fixedpoint parameters
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
bmc.linear_unrolling_depth | unsigned int  |  Maximal level to explore | 4294967295
datalog.all_or_nothing_deltas | bool  |  compile rules so that it is enough for the delta relation in union and widening operations to determine only whether the updated relation was modified or not | false
datalog.check_relation | symbol  |  name of default relation to check. operations on the default relation will be verified using SMT solving | null
datalog.compile_with_widening | bool  |  widening will be used to compile recursive rules | false
datalog.dbg_fpr_nonempty_relation_signature | bool  |  if true, finite_product_relation will attempt to avoid creating inner relation with empty signature by putting in half of the table columns, if it would have been empty otherwise | false
datalog.default_relation | symbol  |  default relation implementation: external_relation, pentagon | pentagon
datalog.default_table | symbol  |  default table implementation: sparse, hashtable, bitvector, interval | sparse
datalog.default_table_checked | bool  |  if true, the default table will be default_table inside a wrapper that checks that its results are the same as of default_table_checker table | false
datalog.default_table_checker | symbol  |  see default_table_checked | null
datalog.explanations_on_relation_level | bool  |  if true, explanations are generated as history of each relation, rather than per fact (generate_explanations must be set to true for this option to have any effect) | false
datalog.generate_explanations | bool  |  produce explanations for produced facts when using the datalog engine | false
datalog.initial_restart_timeout | unsigned int  |  length of saturation run before the first restart (in ms), zero means no restarts | 0
datalog.magic_sets_for_queries | bool  |  magic set transformation will be used for queries | false
datalog.output_profile | bool  |  determines whether profile information should be output when outputting Datalog rules or instructions | false
datalog.print.tuples | bool  |  determines whether tuples for output predicates should be output | true
datalog.profile_timeout_milliseconds | unsigned int  |  instructions and rules that took less than the threshold will not be printed when printed the instruction/rule list | 0
datalog.similarity_compressor | bool  |  rules that differ only in values of constants will be merged into a single rule | true
datalog.similarity_compressor_threshold | unsigned int  |  if similarity_compressor is on, this value determines how many similar rules there must be in order for them to be merged | 11
datalog.subsumption | bool  |  if true, removes/filters predicates with total transitions | true
datalog.timeout | unsigned int  |  Time limit used for saturation | 0
datalog.unbound_compressor | bool  |  auxiliary relations will be introduced to avoid unbound variables in rule heads | true
datalog.use_map_names | bool  |  use names from map files when displaying tuples | true
engine | symbol  |  Select: auto-config, datalog, bmc, spacer | auto-config
generate_proof_trace | bool  |  trace for 'sat' answer as proof object | false
print_aig | symbol  |  Dump clauses in AIG text format (AAG) to the given file name | 
print_answer | bool  |  print answer instance(s) to query | false
print_boogie_certificate | bool  |  print certificate for reachability or non-reachability using a format understood by Boogie | false
print_certificate | bool  |  print certificate for reachability or non-reachability | false
print_fixedpoint_extensions | bool  |  use SMT-LIB2 fixedpoint extensions, instead of pure SMT2, when printing rules | true
print_low_level_smt2 | bool  |  use (faster) low-level SMT2 printer (the printer is scalable but the result may not be as readable) | false
print_statistics | bool  |  print statistics | false
print_with_variable_declarations | bool  |  use variable declarations when displaying rules (instead of attempting to use original names) | true
spacer.arith.solver | unsigned int  |  arithmetic solver: 0 - no solver, 1 - bellman-ford based solver (diff. logic only), 2 - simplex based solver, 3 - floyd-warshall based solver (diff. logic only) and no theory combination 4 - utvpi, 5 - infinitary lra, 6 - lra solver | 2
spacer.blast_term_ite_inflation | unsigned int  |  Maximum inflation for non-Boolean ite-terms expansion: 0 (none), k (multiplicative) | 3
spacer.ctp | bool  |  Enable counterexample-to-pushing | true
spacer.dump_benchmarks | bool  |  Dump SMT queries as benchmarks | false
spacer.dump_threshold | double  |  Threshold in seconds on dumping benchmarks | 5.0
spacer.elim_aux | bool  |  Eliminate auxiliary variables in reachability facts | true
spacer.eq_prop | bool  |  Enable equality and bound propagation in arithmetic | true
spacer.gpdr | bool  |  Use GPDR solving strategy for non-linear CHC | false
spacer.gpdr.bfs | bool  |  Use BFS exploration strategy for expanding model search | true
spacer.ground_pobs | bool  |  Ground pobs by using values from a model | true
spacer.iuc | unsigned int  |  0 = use old implementation of unsat-core-generation, 1 = use new implementation of IUC generation, 2 = use new implementation of IUC + min-cut optimization | 1
spacer.iuc.arith | unsigned int  |  0 = use simple Farkas plugin, 1 = use simple Farkas plugin with constant from other partition (like old unsat-core-generation),2 = use Gaussian elimination optimization (broken), 3 = use additive IUC plugin | 1
spacer.iuc.debug_proof | bool  |  prints proof used by unsat-core-learner for debugging purposes (debugging) | false
spacer.iuc.old_hyp_reducer | bool  |  use old hyp reducer instead of new implementation, for debugging only | false
spacer.iuc.print_farkas_stats | bool  |  prints for each proof how many Farkas lemmas it contains and how many of these participate in the cut (for debugging) | false
spacer.iuc.split_farkas_literals | bool  |  Split Farkas literals | false
spacer.keep_proxy | bool  |  keep proxy variables (internal parameter) | true
spacer.logic | symbol  |  SMT-LIB logic to configure internal SMT solvers | 
spacer.max_level | unsigned int  |  Maximum level to explore | 4294967295
spacer.max_num_contexts | unsigned int  |  maximal number of contexts to create | 500
spacer.mbqi | bool  |  Enable mbqi | true
spacer.min_level | unsigned int  |  Minimal level to explore | 0
spacer.native_mbp | bool  |  Use native mbp of Z3 | true
spacer.order_children | unsigned int  |  SPACER: order of enqueuing children in non-linear rules : 0 (original), 1 (reverse), 2 (random) | 0
spacer.p3.share_invariants | bool  |  Share invariants lemmas | false
spacer.p3.share_lemmas | bool  |  Share frame lemmas | false
spacer.print_json | symbol  |  Print pobs tree in JSON format to a given file | 
spacer.propagate | bool  |  Enable propagate/pushing phase | true
spacer.push_pob | bool  |  push blocked pobs to higher level | false
spacer.push_pob_max_depth | unsigned int  |  Maximum depth at which push_pob is enabled | 4294967295
spacer.q3 | bool  |  Allow quantified lemmas in frames | true
spacer.q3.instantiate | bool  |  Instantiate quantified lemmas | true
spacer.q3.qgen.normalize | bool  |  normalize cube before quantified generalization | true
spacer.q3.use_qgen | bool  |  use quantified lemma generalizer | false
spacer.random_seed | unsigned int  |  Random seed to be used by SMT solver | 0
spacer.reach_dnf | bool  |  Restrict reachability facts to DNF | true
spacer.reset_pob_queue | bool  |  SPACER: reset pob obligation queue when entering a new level | true
spacer.restart_initial_threshold | unsigned int  |  Initial threshold for restarts | 10
spacer.restarts | bool  |  Enable resetting obligation queue | false
spacer.simplify_lemmas_post | bool  |  simplify derived lemmas after inductive propagation | false
spacer.simplify_lemmas_pre | bool  |  simplify derived lemmas before inductive propagation | false
spacer.simplify_pob | bool  |  simplify pobs by removing redundant constraints | false
spacer.trace_file | symbol  |  Log file for progress events | 
spacer.use_array_eq_generalizer | bool  |  SPACER: attempt to generalize lemmas with array equalities | true
spacer.use_bg_invs | bool  |  Enable external background invariants | false
spacer.use_derivations | bool  |  SPACER: using derivation mechanism to cache intermediate results for non-linear rules | true
spacer.use_euf_gen | bool  |  Generalize lemmas and pobs using implied equalities | false
spacer.use_inc_clause | bool  |  Use incremental clause to represent trans | true
spacer.use_inductive_generalizer | bool  |  generalize lemmas using induction strengthening | true
spacer.use_lemma_as_cti | bool  |  SPACER: use a lemma instead of a CTI in flexible_trace | false
spacer.use_lim_num_gen | bool  |  Enable limit numbers generalizer to get smaller numbers | false
spacer.validate_lemmas | bool  |  Validate each lemma after generalization | false
spacer.weak_abs | bool  |  Weak abstraction | true
tab.selection | symbol  |  selection method for tabular strategy: weight (default), first, var-use | weight
validate | bool  |  validate result (by proof checking or model checking) | false
xform.array_blast | bool  |  try to eliminate local array terms using Ackermannization -- some array terms may remain | false
xform.array_blast_full | bool  |  eliminate all local array variables by QE | false
xform.bit_blast | bool  |  bit-blast bit-vectors | false
xform.coalesce_rules | bool  |  coalesce rules | false
xform.coi | bool  |  use cone of influence simplification | true
xform.compress_unbound | bool  |  compress tails with unbound variables | true
xform.elim_term_ite | bool  |  Eliminate term-ite expressions | false
xform.elim_term_ite.inflation | unsigned int  |  Maximum inflation for non-Boolean ite-terms blasting: 0 (none), k (multiplicative) | 3
xform.fix_unbound_vars | bool  |  fix unbound variables in tail | false
xform.inline_eager | bool  |  try eager inlining of rules | true
xform.inline_linear | bool  |  try linear inlining method | true
xform.inline_linear_branch | bool  |  try linear inlining method with potential expansion | false
xform.instantiate_arrays | bool  |  Transforms P(a) into P(i, a[i] a) | false
xform.instantiate_arrays.enforce | bool  |  Transforms P(a) into P(i, a[i]), discards a from predicate | false
xform.instantiate_arrays.nb_quantifier | unsigned int  |  Gives the number of quantifiers per array | 1
xform.instantiate_arrays.slice_technique | symbol  |  <no-slicing>=> GetId(i) = i, <smash> => GetId(i) = true | no-slicing
xform.instantiate_quantifiers | bool  |  instantiate quantified Horn clauses using E-matching heuristic | false
xform.magic | bool  |  perform symbolic magic set transformation | false
xform.quantify_arrays | bool  |  create quantified Horn clauses from clauses with arrays | false
xform.scale | bool  |  add scaling variable to linear real arithmetic clauses | false
xform.slice | bool  |  simplify clause set using slicing | true
xform.subsumption_checker | bool  |  Enable subsumption checker (no support for model conversion) | true
xform.tail_simplifier_pve | bool  |  propagate_variable_equivalences | true
xform.transform_arrays | bool  |  Rewrites arrays equalities and applies select over store | false
xform.unfold_rules | unsigned int  |  unfold rules statically using iterative squaring | 0

## Module smt

Description: smt solver based on lazy smt
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
arith.auto_config_simplex | bool  |  force simplex solver in auto_config | false
arith.bprop_on_pivoted_rows | bool  |  propagate bounds on rows changed by the pivot operation | true
arith.branch_cut_ratio | unsigned int  |  branch/cut ratio for linear integer arithmetic | 2
arith.dump_lemmas | bool  |  dump arithmetic theory lemmas to files | false
arith.eager_eq_axioms | bool  |  eager equality axioms | true
arith.enable_hnf | bool  |  enable hnf (Hermite Normal Form) cuts | true
arith.greatest_error_pivot | bool  |  Pivoting strategy | false
arith.ignore_int | bool  |  treat integer variables as real | false
arith.int_eq_branch | bool  |  branching using derived integer equations | false
arith.min | bool  |  minimize cost | false
arith.nl | bool  |  (incomplete) nonlinear arithmetic support based on Groebner basis and interval propagation, relevant only if smt.arith.solver=2 | true
arith.nl.branching | bool  |  branching on integer variables in non linear clusters, relevant only if smt.arith.solver=2 | true
arith.nl.delay | unsigned int  |  number of calls to final check before invoking bounded nlsat check | 500
arith.nl.expp | bool  |  expensive patching | false
arith.nl.gr_q | unsigned int  |  grobner's quota | 10
arith.nl.grobner | bool  |  run grobner's basis heuristic | true
arith.nl.grobner_cnfl_to_report | unsigned int  |  grobner's maximum number of conflicts to report | 1
arith.nl.grobner_eqs_growth | unsigned int  |  grobner's number of equalities growth  | 10
arith.nl.grobner_expr_degree_growth | unsigned int  |  grobner's maximum expr degree growth | 2
arith.nl.grobner_expr_size_growth | unsigned int  |  grobner's maximum expr size growth | 2
arith.nl.grobner_frequency | unsigned int  |  grobner's call frequency | 4
arith.nl.grobner_max_simplified | unsigned int  |  grobner's maximum number of simplifications | 10000
arith.nl.grobner_subs_fixed | unsigned int  |  0 - no subs, 1 - substitute, 2 - substitute fixed zeros only | 1
arith.nl.horner | bool  |  run horner's heuristic | true
arith.nl.horner_frequency | unsigned int  |  horner's call frequency | 4
arith.nl.horner_row_length_limit | unsigned int  |  row is disregarded by the heuristic if its length is longer than the value | 10
arith.nl.horner_subs_fixed | unsigned int  |  0 - no subs, 1 - substitute, 2 - substitute fixed zeros only | 2
arith.nl.nra | bool  |  call nra_solver when incremental linearization does not produce a lemma, this option is ignored when arith.nl=false, relevant only if smt.arith.solver=6 | true
arith.nl.order | bool  |  run order lemmas | true
arith.nl.rounds | unsigned int  |  threshold for number of (nested) final checks for non linear arithmetic, relevant only if smt.arith.solver=2 | 1024
arith.nl.tangents | bool  |  run tangent lemmas | true
arith.print_ext_var_names | bool  |  print external variable names | false
arith.print_stats | bool  |  print statistic | false
arith.propagate_eqs | bool  |  propagate (cheap) equalities | true
arith.propagation_mode | unsigned int  |  0 - no propagation, 1 - propagate existing literals, 2 - refine finite bounds | 1
arith.random_initial_value | bool  |  use random initial values in the simplex-based procedure for linear arithmetic | false
arith.rep_freq | unsigned int  |  the report frequency, in how many iterations print the cost and other info | 0
arith.simplex_strategy | unsigned int  |  simplex strategy for the solver | 0
arith.solver | unsigned int  |  arithmetic solver: 0 - no solver, 1 - bellman-ford based solver (diff. logic only), 2 - simplex based solver, 3 - floyd-warshall based solver (diff. logic only) and no theory combination 4 - utvpi, 5 - infinitary lra, 6 - lra solver | 6
array.extensional | bool  |  extensional array theory | true
array.weak | bool  |  weak array theory | false
auto_config | bool  |  automatically configure solver | true
bv.delay | bool  |  delay internalize expensive bit-vector operations | true
bv.enable_int2bv | bool  |  enable support for int2bv and bv2int operators | true
bv.eq_axioms | bool  |  enable redundant equality axioms for bit-vectors | true
bv.reflect | bool  |  create enode for every bit-vector term | true
bv.watch_diseq | bool  |  use watch lists instead of eager axioms for bit-vectors | false
candidate_models | bool  |  create candidate models even when quantifier or theory reasoning is incomplete | false
case_split | unsigned int  |  0 - case split based on variable activity, 1 - similar to 0, but delay case splits created during the search, 2 - similar to 0, but cache the relevancy, 3 - case split based on relevancy (structural splitting), 4 - case split on relevancy and activity, 5 - case split on relevancy and current goal, 6 - activity-based case split with theory-aware branching activity | 1
clause_proof | bool  |  record a clausal proof | false
core.extend_nonlocal_patterns | bool  |  extend unsat cores with literals that have quantifiers with patterns that contain symbols which are not in the quantifier's body | false
core.extend_patterns | bool  |  extend unsat core with literals that trigger (potential) quantifier instances | false
core.extend_patterns.max_distance | unsigned int  |  limits the distance of a pattern-extended unsat core | 4294967295
core.minimize | bool  |  minimize unsat core produced by SMT context | false
core.validate | bool  |  [internal] validate unsat core produced by SMT context. This option is intended for debugging | false
cube_depth | unsigned int  |  cube depth. | 1
dack | unsigned int  |  0 - disable dynamic ackermannization, 1 - expand Leibniz's axiom if a congruence is the root of a conflict, 2 - expand Leibniz's axiom if a congruence is used during conflict resolution | 1
dack.eq | bool  |  enable dynamic ackermannization for transtivity of equalities | false
dack.factor | double  |  number of instance per conflict | 0.1
dack.gc | unsigned int  |  Dynamic ackermannization garbage collection frequency (per conflict) | 2000
dack.gc_inv_decay | double  |  Dynamic ackermannization garbage collection decay | 0.8
dack.threshold | unsigned int  |   number of times the congruence rule must be used before Leibniz's axiom is expanded | 10
delay_units | bool  |  if true then z3 will not restart when a unit clause is learned | false
delay_units_threshold | unsigned int  |  maximum number of learned unit clauses before restarting, ignored if delay_units is false | 32
dt_lazy_splits | unsigned int  |  How lazy datatype splits are performed: 0- eager, 1- lazy for infinite types, 2- lazy | 1
ematching | bool  |  E-Matching based quantifier instantiation | true
induction | bool  |  enable generation of induction lemmas | false
lemma_gc_strategy | unsigned int  |  lemma garbage collection strategy: 0 - fixed, 1 - geometric, 2 - at restart, 3 - none | 0
logic | symbol  |  logic used to setup the SMT solver | 
macro_finder | bool  |  try to find universally quantified formulas that can be viewed as macros | false
max_conflicts | unsigned int  |  maximum number of conflicts before giving up. | 4294967295
mbqi | bool  |  model based quantifier instantiation (MBQI) | true
mbqi.force_template | unsigned int  |  some quantifiers can be used as templates for building interpretations for functions. Z3 uses heuristics to decide whether a quantifier will be used as a template or not. Quantifiers with weight >= mbqi.force_template are forced to be used as a template | 10
mbqi.id | string  |  Only use model-based instantiation for quantifiers with id's beginning with string | 
mbqi.max_cexs | unsigned int  |  initial maximal number of counterexamples used in MBQI, each counterexample generates a quantifier instantiation | 1
mbqi.max_cexs_incr | unsigned int  |  increment for MBQI_MAX_CEXS, the increment is performed after each round of MBQI | 0
mbqi.max_iterations | unsigned int  |  maximum number of rounds of MBQI | 1000
mbqi.trace | bool  |  generate tracing messages for Model Based Quantifier Instantiation (MBQI). It will display a message before every round of MBQI, and the quantifiers that were not satisfied | false
pb.conflict_frequency | unsigned int  |  conflict frequency for Pseudo-Boolean theory | 1000
pb.learn_complements | bool  |  learn complement literals for Pseudo-Boolean theory | true
phase_caching_off | unsigned int  |  number of conflicts while phase caching is off | 100
phase_caching_on | unsigned int  |  number of conflicts while phase caching is on | 400
phase_selection | unsigned int  |  phase selection heuristic: 0 - always false, 1 - always true, 2 - phase caching, 3 - phase caching conservative, 4 - phase caching conservative 2, 5 - random, 6 - number of occurrences, 7 - theory | 3
pull_nested_quantifiers | bool  |  pull nested quantifiers | false
q.lift_ite | unsigned int  |  0 - don not lift non-ground if-then-else, 1 - use conservative ite lifting, 2 - use full lifting of if-then-else under quantifiers | 0
q.lite | bool  |  Use cheap quantifier elimination during pre-processing | false
qi.cost | string  |  expression specifying what is the cost of a given quantifier instantiation | (+ weight generation)
qi.eager_threshold | double  |  threshold for eager quantifier instantiation | 10.0
qi.lazy_threshold | double  |  threshold for lazy quantifier instantiation | 20.0
qi.max_instances | unsigned int  |  maximum number of quantifier instantiations | 4294967295
qi.max_multi_patterns | unsigned int  |  specify the number of extra multi patterns | 0
qi.profile | bool  |  profile quantifier instantiation | false
qi.profile_freq | unsigned int  |  how frequent results are reported by qi.profile | 4294967295
qi.quick_checker | unsigned int  |  specify quick checker mode, 0 - no quick checker, 1 - using unsat instances, 2 - using both unsat and no-sat instances | 0
quasi_macros | bool  |  try to find universally quantified formulas that are quasi-macros | false
random_seed | unsigned int  |  random seed for the smt solver | 0
refine_inj_axioms | bool  |  refine injectivity axioms | true
relevancy | unsigned int  |  relevancy propagation heuristic: 0 - disabled, 1 - relevancy is tracked by only affects quantifier instantiation, 2 - relevancy is tracked, and an atom is only asserted if it is relevant | 2
restart.max | unsigned int  |  maximal number of restarts. | 4294967295
restart_factor | double  |  when using geometric (or inner-outer-geometric) progression of restarts, it specifies the constant used to multiply the current restart threshold | 1.1
restart_strategy | unsigned int  |  0 - geometric, 1 - inner-outer-geometric, 2 - luby, 3 - fixed, 4 - arithmetic | 1
restricted_quasi_macros | bool  |  try to find universally quantified formulas that are restricted quasi-macros | false
seq.max_unfolding | unsigned int  |  maximal unfolding depth for checking string equations and regular expressions | 1000000000
seq.split_w_len | bool  |  enable splitting guided by length constraints | true
seq.validate | bool  |  enable self-validation of theory axioms created by seq theory | false
str.aggressive_length_testing | bool  |  prioritize testing concrete length values over generating more options | false
str.aggressive_unroll_testing | bool  |  prioritize testing concrete regex unroll counts over generating more options | true
str.aggressive_value_testing | bool  |  prioritize testing concrete string constant values over generating more options | false
str.fast_length_tester_cache | bool  |  cache length tester constants instead of regenerating them | false
str.fast_value_tester_cache | bool  |  cache value tester constants instead of regenerating them | true
str.fixed_length_naive_cex | bool  |  construct naive counterexamples when fixed-length model construction fails for a given length assignment (Z3str3 only) | true
str.fixed_length_refinement | bool  |  use abstraction refinement in fixed-length equation solver (Z3str3 only) | false
str.overlap_priority | double  |  theory-aware priority for overlapping variable cases; use smt.theory_aware_branching=true | -0.1
str.regex_automata_difficulty_threshold | unsigned int  |  difficulty threshold for regex automata heuristics | 1000
str.regex_automata_failed_automaton_threshold | unsigned int  |  number of failed automaton construction attempts after which a full automaton is automatically built | 10
str.regex_automata_failed_intersection_threshold | unsigned int  |  number of failed automaton intersection attempts after which intersection is always computed | 10
str.regex_automata_intersection_difficulty_threshold | unsigned int  |  difficulty threshold for regex intersection heuristics | 1000
str.regex_automata_length_attempt_threshold | unsigned int  |  number of length/path constraint attempts before checking unsatisfiability of regex terms | 10
str.string_constant_cache | bool  |  cache all generated string constants generated from anywhere in theory_str | true
str.strong_arrangements | bool  |  assert equivalences instead of implications when generating string arrangement axioms | true
string_solver | symbol  |  solver for string/sequence theories. options are: 'z3str3' (specialized string solver), 'seq' (sequence solver), 'auto' (use static features to choose best solver), 'empty' (a no-op solver that forces an answer unknown if strings were used), 'none' (no solver) | seq
theory_aware_branching | bool  |  Allow the context to use extra information from theory solvers regarding literal branching prioritization. | false
theory_case_split | bool  |  Allow the context to use heuristics involving theory case splits, which are a set of literals of which exactly one can be assigned True. If this option is false, the context will generate extra axioms to enforce this instead. | false
threads | unsigned int  |  maximal number of parallel threads. | 1
threads.cube_frequency | unsigned int  |  frequency for using cubing | 2
threads.max_conflicts | unsigned int  |  maximal number of conflicts between rounds of cubing for parallel SMT | 400

## Module sls

Description: Experimental Stochastic Local Search Solver (for QFBV only).
 Parameter | Type | Description | Default
 ----------|------|-------------|--------
early_prune | bool  |  use early pruning for score prediction | true
max_memory | unsigned int  |  maximum amount of memory in megabytes | 4294967295
max_restarts | unsigned int  |  maximum number of restarts | 4294967295
paws_init | unsigned int  |  initial/minimum assertion weights | 40
paws_sp | unsigned int  |  smooth assertion weights with probability paws_sp / 1024 | 52
random_offset | bool  |  use random offset for candidate evaluation | true
random_seed | unsigned int  |  random seed | 0
rescore | bool  |  rescore/normalize top-level score every base restart interval | true
restart_base | unsigned int  |  base restart interval given by moves per run | 100
restart_init | bool  |  initialize to 0 or random value (= 1) after restart | false
scale_unsat | double  |  scale score of unsat expressions by this factor | 0.5
track_unsat | bool  |  keep a list of unsat assertions as done in SAT - currently disabled internally | false
vns_mc | unsigned int  |  in local minima, try Monte Carlo sampling vns_mc many 2-bit-flips per bit | 0
vns_repick | bool  |  in local minima, try picking a different assertion (only for walksat) | false
walksat | bool  |  use walksat assertion selection (instead of gsat) | true
walksat_repick | bool  |  repick assertion if randomizing in local minima | true
walksat_ucb | bool  |  use bandit heuristic for walksat assertion selection (instead of random) | true
walksat_ucb_constant | double  |  the ucb constant c in the term score + c * f(touched) | 20.0
walksat_ucb_forget | double  |  scale touched by this factor every base restart interval | 1.0
walksat_ucb_init | bool  |  initialize total ucb touched to formula size | false
walksat_ucb_noise | double  |  add noise 0 <= 256 * ucb_noise to ucb score for assertion selection | 0.0002
wp | unsigned int  |  random walk with probability wp / 1024 | 100
