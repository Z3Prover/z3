# F* audit PR #11364 @ cbe33c46

Base 9dc878f0. Source: src/nlsat/nlsat_transcendentals.cpp at head, sha256 7e96ccb1...5645, refine_app lines 295-402 (fetched via contents API, not executed).

## Obligations (all proved, module NlsatRefineApp)
- O1: if the enclosure is sound (f maps [xlo,xhi] into [rlo,rhi]) the lemma clause (arg(xlo \/ arg)xhi \/ val bound) holds for all models val=f(arg).
- O2: if the enclosure excludes current value y and arg in [xlo,xhi], the clause is falsified by the current assignment (progress; no acceptance of a witness merely from a widened enclosure).
- O3: the shrink-loop selection (first candidate whose enclosure excludes y, else the initial unwidened enclosure already checked to exclude y) never contains y and preserves soundness given sound candidates.

## Mapping
int models ordered rationals/algebraic numbers; contains = contains_value; pick = the 64-iteration loop; lemma_holds = the mk_clause lemma. Rewrite fixes the old behavior where the widened enclosure was used to accept (return false) a value.

## Assumptions (not proved)
enclose() soundness (exp/log/atan Taylor brackets, sin_cos_taylor_bracket, interval_eval double enclosure incl. nextafter outward rounding, to_rational exactness) is assumed as a hypothesis `sound`. Manual review needed; note the double path now rounds endpoints outward only when to_rational(d) misses xlo/xhi, and xlo/xhi are then replaced by the double endpoints (still containing the originals).

## Exclusions
nra_solver.cpp (register_transcendentals_with_nlsat bind_var definitions linking monic/term variables; denominators scaling) and tests nla_transcendentals.cpp; not modeled. Only one function audited. Not verification of C++ execution, memory safety, or whole solver.

## Reproduce
fstar.exe 2026.09.27, Z3 4.13.3: fstar.exe --smt (z3) --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out NlsatRefineApp.fst (exit 0). No admit/assume. Inherits F* standard library (FStar.List.Tot).