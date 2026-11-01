# F* audit of PR #11513 @ 4f38d9c769688e49cf45f49d0b98ebfc063f87cf (base 9ae0ae763b0c0c60aa63cea4fad58146569d6334)

Scope (partial): one changed function, `dt2bv_proof_converter::insert_enum` (src/tactic/bv/dt2bv_proof_converter.cpp, head blob 9b0a20f4f3ed8bf5930ff82ccf394a98a2376d45, sha256 of file 0ca9d160e4eb...). Three obligations.

## Obligations (all proved, in Dt2BvEncodingAudit.fst)
1. ob1: the ite-chain encoding (n-1 default, wrapped for i=n-2..0 with ite(s=c_i, i, enc)) maps constructor s to numeral s.
2. ob2: encoding is injective on constructors.
3. ob3: under the C++ guard n <= 2^w, every encoded numeral is < 2^w (no wrap). A witness (n=3,w=1) shows the guard's rejected case does wrap, so the guard is necessary; it is a necessity check, not a bug.
No counterexample was found.

## Correspondence / assumptions
Constructors are modelled as distinct indices in [0,n) (assumes datatype constructors are pairwise distinct, from datatype theory, not proven here). Numerals are naturals; bv numeral creation modulo 2^w is justified by ob3. The guard `!m_proofs.empty() ||` clause, duplicate-source check, and arity/sort checks are not modelled.

## Not covered (excluded)
close_encoding_lemmas, substitute_proof_parameters, prove (SMT-certificate synthesis), insert, insert_bound, operator(), translate; dt2bv_tactic.cpp, tactical.cpp, split_clause_tactic.cpp, proof_converter.*, enum2bv_rewriter.*, goal.h, tactic.cpp, tests, and the PR's own fstar/audits files (not imported or trusted). Proof-converter composition, hypothesis/lemma closing and quant-inst parameter substitution are only manually unreviewed. This is not mechanized verification of C++ execution, memory safety, or Z3.

## Tools
F* 2026.09.27, Z3 4.13.3 (pinned release). Inherited: F* standard library/prelude.
Command: fstar.exe --smt (z3) --z3version 4.13.3 --cache_dir cache --odir out --z3rlimit 10 Dt2BvEncodingAudit.fst (fresh cache, exit 0).
