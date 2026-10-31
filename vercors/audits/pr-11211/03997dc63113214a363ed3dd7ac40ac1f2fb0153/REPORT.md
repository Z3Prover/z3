# VerCors audit, PR 11211, head 03997dc63113214a363ed3dd7ac40ac1f2fb0153 (base 5b25866d00e94fe04fd97301e22e03472ae4a121)

PR was open at this SHA and had no prior vercors-nfv-audit comment.

## Sources (fetched via contents API at head SHA)
- src/ast/rewriter/arith_swine.cpp, 426 lines, sha256 8b53077fafd66049ca9abd276c70c678af6a10718521b6db031e282709f6fe54
- src/ast/rewriter/arith_swine.h, 58 lines, sha256 19de765976d70c323316cfd5d3d67866dc03c04dfe2f3e606821b7aa3ff5fc51

## Candidate selection
1. compute_power (lines 22-49): exponentiation by squaring; candidate obligations: result == x^y when it returns true; loop invariant result*base^exponent == x^y; the size guard (y <= 2^20/bitsize(x)) bounds work.
2. check_model (lines 51-65): soundness of l_false (refutation) only when computed power differs from model value, or exponent exceeds bitsize(value)+1 with |x|>=2.
3. symmetry (lines 67-99): soundness of the lemma for negative base/exponent normalization.

## Outcome: all inconclusive
A sanity attempt was made with a machine-`int` extract of the compute_power loop (a deliberately failing draft containing `assert false`, only used to confirm the C++ frontend runs; it is not evidence). A faithful extract was not produced because:
- `rational` is an arbitrary-precision integer/rational class; replacing it with C++ `int` changes semantics (signed overflow is possible for the loop's base squaring and result multiplication, whereas the source is unbounded). Modeling it as a VerCors mathematical integer would be an unjustified abstraction of the class, not source correspondence.
- `m.inc(...)` (resource limit, side-effecting, returns bool), `rational::bitsize/is_unsigned/get_unsigned`, `vector<power>`, `expr_ref`, lambdas via std::function, and PR-owned headers cannot be included (policy) and have no bundled contracts. Inventing contracts for them would be trusted assumptions, which is disallowed.
- check_model and symmetry additionally depend on these types, the rewriter m_rw, and AST construction.

No counterexample was found; failure to verify is not evidence of correctness or of a bug.

## Exclusions
All other changed C++ files (arith_decl_plugin.cpp, arith_rewriter.cpp, sat_solver.cpp, sat/smt arith_*, theory_lra.*, purify_arith_tactic.cpp, tests, api header) and the F* files were not selected: they rely on solver/AST object models and callers that VerCors cannot model within the bound of three functions. F*/Dafny coverage is not claimed.

## Environment
VerCors 2.4.0 (bundled Z3 / Java as shipped at /tmp/gh-aw/vercors). Command pattern: /tmp/gh-aw/vercors/vercors --lang cpp --backend silicon --dev-total-timeout 60 (abs unit.cpp).
