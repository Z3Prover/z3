# F* audit of PR 11438 at ba170e9d96da994fc7186e342b0924b496e7e215 (base 70f966a79844ea3b18fe35e5711d55754e80460e)

Source: src/ast/rewriter/arith_rewriter.cpp at head (sha256 46164a9cb02b9b0de9a6d29b2b113a0f862d3c80bf8b58169577ac69379be275, fetched via contents API); diff hunks at old lines ~2409, 2473, 2755, 2770.

## Selected functions (bound: 3)
1. arith_rewriter::mk_sin_core (asin and acos branches, now guarded by is_numeral(x,k) && -1<=k<=1)
2. arith_rewriter::mk_cos_core (acos branch, same guard)
3. arith_rewriter::mk_cosh_core (acosh branch, guard k>=1)

## Obligations (module Z3InverseTrigGuards.fst) - all proved
- sin(asin k)=k under guard; the old unguarded rule is unsound: sin bounded by 1 refutes sin(asin 2)=2 in every model (counterexample to the old rule, not to the PR).
- sin(acos k)=sqrt(1-k^2): under guard, s^2=1-k^2 and 1-k^2>=0, s>=0; guard is necessary (1-2*2<0).
- cos(acos k)=k under guard; old rule refuted at k=2.
- cosh(acosh k)=k for k>=1; old rule refuted at k=0 since cosh>=1.
No counterexample to the PR's guards was found.

## Correspondence and assumptions
Guards are modelled over integer numerals k as an abstraction of rational constants; the real-analysis specs of sin/asin/acos/cosh/acosh (e.g. sin(asin k)=k on [-1,1], s>=0 on acos range, s^2+c^2=1, |sin|,|cos|<=1, cosh>=1) are stated as lemma preconditions, i.e. assumed, not derived. Therefore the soundness lemmas are largely restatements of the intended domain facts; the stronger content is the necessity of guards (old-rule refutations) and the sqrt-domain fact. No admit/assume/axioms used. Not mechanized: C++ execution, is_numeral semantics (assumed to return the exact rational value of a numeral), rational comparison, BR_REWRITE_FULL result construction, memory safety, and test code.

## Exclusions
- mk_tanh_core (atanh guard -1<k<1): exceeds the three-function bound; by inspection it is the correct open interval since tanh range is (-1,1).
- src/test/arith_rewriter.cpp (tst_inverse_trig_domains): not audited; test only.
- Unchanged branches (e.g. cos(asin x) placeholder, sin(0), cos(0) paths) and the removal/relocation of `rational k;` declarations (scope hoisted before first use; manually reviewed, no behavior change).
- Residual note: symbolic arguments are no longer simplified (completeness loss, not soundness).

## Reproduce
cd to a work dir containing Z3InverseTrigGuards.fst and run the command in the verification log, with fresh cache/out dirs.
