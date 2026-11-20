# F* audit PR 11705 @ 140c0ffd7e6b9667e4d53d6c888a1be42d30a010 (base 1a1d88dd)

Source: src/opt/opt_curve_certificate.cpp at head (305 lines, decoded sha256 dd07025579e83403c7d0ef88011a88d15febe6a19a9fb851b5f3f9602c6b2ea3), changed region ~lines 247-290.

## Intended property
Evaluating the curve at t=1,2,4,16,...,2^32 and returning false on a violated hard constraint or objective < value at the latest model only rejects curves the original solver queries would also reject.

## Obligations (all proved)
- O1: for every integer t>=0 the sampled basis values h2=t(t+1)/2, h3=h2(t+2)/3 are integral and satisfy the solver's `along` constraints (t>=0, 2*h2=t(t+1), 3*h3=h2(t+2)); each sample is a legitimate point of the query.
- O2: the schedule t0 <- (t0==1?2:t0*t0) gives 1,2,4,16,256,65536,2^32 (num_samples=7), all >=0.
- O3: a rejecting sample is a model of the along-constraints plus the violation / p<p0 condition, so the old check could not return l_false; early return false agrees. (Thin wrapper over O1; the semantic link relies on the assumptions below.)

## Correspondence / assumptions (manually reviewed, not mechanized)
F* h2,h3 model basis[2],basis[3] (degree<=max_degree=3). Exact integer division in F* corresponds to exact rational division in C++ (exactness proved by O1). model_evaluator is assumed to evaluate the substituted formulas faithfully, and at(g)=false implies g is false at the point. Non-numeric sampled objectives are skipped (conservative). Note the is_numeral(p0) check now precedes the hard-constraint solver call; a non-numeral p0 returns false either way. Basis constants other than t/h are substituted by the latest model values.

## Exclusions
Remainder of certify, the caller's curve construction, src/test/opt_bounds.cpp test, header constant, rlimit/termination/performance claims, memory safety.

## Tools
F* 2026.09.27, Z3 4.13.3 (pinned backend), --z3rlimit 10, no admit/assume/lax.
Command: /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir c2 --odir o2 CurveSamples.fst