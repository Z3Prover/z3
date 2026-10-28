# F* audit PR #11419 @ 589c255d

Base 668d5979. Source: src/smt/theory_fpa.cpp (head sha256 9d38c8e2cc72a5ba682f324ae4ab1b299af11762daaf426fe287d7ebfdea2f2d, base e5bdadfaf16459eb6e517ba7d6bd8af89d2d6c342d9b330d9a55f83a159cb81d), relevant_eh lines ~446-455 at head.

## Changed behavior
For n = fp(sgn,exp,sig) the PR asserts (convert(isNaN(n)) => n = NaN) plus side conditions. Previously fp terms got no such link, so congruence closure did not identify NaNs with different bits.

## Obligations (all proved)
1. o1: guard (exp all ones, sig nonzero) => fp(...) = NaN (soundness of the asserted implication under SMT-LIB fp semantics, where all NaN bit patterns denote the single NaN).
2. o2: any two NaN-bit constructions of any sign/payload are equal (the intended congruence property).
3. o3: the lemma does not force NaN for non-NaN bits (no over-constraining); plus concrete regression witnesses 0xffff,0x7e02,0x7c01,0xfe00 (NaN) and 0x3c00,0x4000 (distinct non-NaN).

## Correspondence / assumptions
Model: Float16 (eb=5,sb=11), fp value type NaN|Inf|Fin; is_nan_bits mirrors the converted isNaN condition. Assumes convert(mk_is_nan(n)) is the bit-level NaN predicate (manually reviewed, not mechanized) and that mk_nan(sort) is the SMT-LIB unique NaN. Only standard F* libraries; no base modules imported. No admits/assumes.

## Exclusions / not mechanized
C++ execution, assert_cnstr/m_th_rw behavior, memory safety, mk_side_conditions soundness, generalization to arbitrary eb/sb, interaction with the existing non-fp branch, and the test changes in src/test/fpa.cpp (not audited). Only one function changed; rm-sort exclusion holds as is_fp implies float sort.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit; /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Pr11419NanCongruence.fst