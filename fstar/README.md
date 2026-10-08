# F* Neuro Formal-Verification Audits of Z3 Modules

This directory contains a series of independent F* audits that
formalize and mechanically verify selected rewrite rules of Z3's
rewriter/converter source files. Each audit defines a self-contained,
abstract (never Z3-internal-type-dependent) value-level theory for its
subject area, proves that the corresponding C++ code's symbolic
rewrite shortcuts are equal to evaluating that theory, and explicitly
documents what was judged out of scope (and why).

Toolchain used throughout: [F*](https://github.com/FStarLang/FStar)
`v2026.09.27` (Windows x64) with Z3 `4.13.3` as the SMT backend (F*
pins an exact Z3 version; this is independent of the Z3 binary built
from this repository). Typecheck any file with:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe <File>.fst
```

All `.fst` files in this directory type-check and discharge all
verification conditions. All are free of `admit`/`assume`/axioms,
except `Z3NlArith.fst`, whose 9 `assume`s are explicitly-labeled
real-analysis facts about `exp`/`log`/`sin`/`cos`/`atan2` (see
[`NL_ARITH_REPORT.md`](NL_ARITH_REPORT.md)).

## Audits

| Audit | Report | Theory file(s) | Proof file(s) | Subject |
|---|---|---|---|---|
| Sequences / regex membership / regex algebra / axiom soundness | [`SEQ_REWRITER_REPORT.md`](SEQ_REWRITER_REPORT.md) | [`Z3SeqTheory.fst`](Z3SeqTheory.fst), [`Z3RegexTheory.fst`](Z3RegexTheory.fst) | [`Z3SeqRewrites.fst`](Z3SeqRewrites.fst), [`Z3SeqDerive.fst`](Z3SeqDerive.fst), [`Z3RegexMembership.fst`](Z3RegexMembership.fst), [`Z3RegexRewrites.fst`](Z3RegexRewrites.fst), [`Z3SeqAxioms.fst`](Z3SeqAxioms.fst), [`Z3SeqIndexOf.fst`](Z3SeqIndexOf.fst), [`Z3StoiTheory.fst`](Z3StoiTheory.fst) | `src/ast/rewriter/seq_rewriter.cpp`, `src/ast/rewriter/seq_derive.cpp`, `src/ast/seq/seq_axioms.cpp` |
| Floating point | [`FPA_REPORT.md`](FPA_REPORT.md) | [`Z3FpaTheory.fst`](Z3FpaTheory.fst), [`Z3FpaConverter.fst`](Z3FpaConverter.fst) | [`Z3FpaRewrites.fst`](Z3FpaRewrites.fst), [`Z3FpaConverter.fst`](Z3FpaConverter.fst) | `src/ast/rewriter/fpa_rewriter.cpp`, `src/ast/fpa/fpa2bv_converter.cpp` |
| FP rounding (issue/PR audit) | [`FPA_ROUNDING_AUDIT.md`](FPA_ROUNDING_AUDIT.md) | [`Z3FpaConverter.fst`](Z3FpaConverter.fst) | [`Z3FpaRoundingAudit.fst`](Z3FpaRoundingAudit.fst), [`Z3FpaRoundingBits.fst`](Z3FpaRoundingBits.fst), [`Z3FpaZeroSign.fst`](Z3FpaZeroSign.fst), [`Z3FpaNanCongruence.fst`](Z3FpaNanCongruence.fst), [`Z3FpaNanWrap.fst`](Z3FpaNanWrap.fst), [`Z3FpaToRealSign.fst`](Z3FpaToRealSign.fst) | `mk_to_fp_real`, `mk_to_real`, `theory_fpa::relevant_eh`, and FP/datatype model construction (all tracked issues now closed: #10881/#10931/#9953 via merged PR #10888; #7431 via merged PR #11086; #7842/#10176 via merged PR #11088) |
| MPF library | [`MPF_REPORT.md`](MPF_REPORT.md) | [`Z3MpfTheory.fst`](Z3MpfTheory.fst) | [`Z3MpfTheory.fst`](Z3MpfTheory.fst), [`Z3MpfRound.fst`](Z3MpfRound.fst), [`Z3MpfExact.fst`](Z3MpfExact.fst) | `src/util/mpf.h`/`mpf.cpp` (arbitrary-precision IEEE-754 library) |
| Regex/AST (`rex::info`) | [`REGEX_REPORT.md`](REGEX_REPORT.md) | [`Z3RegexTheory.fst`](Z3RegexTheory.fst), [`Z3AstTheory.fst`](Z3AstTheory.fst), [`Z3RegexExprTheory.fst`](Z3RegexExprTheory.fst) | [`Z3RegexInfo.fst`](Z3RegexInfo.fst) | `src/ast/seq_decl_plugin.cpp`'s `get_info`/`mk_info_rec`/`rex::info` (found and fixed a soundness bug in `info::diff`'s nullable computation) |
| Non-linear arithmetic (NLA) lemmas | [`NL_ARITH_REPORT.md`](NL_ARITH_REPORT.md) | — (lemmas stated directly over `FStar.Real`/`int`) | [`Z3NlArith.fst`](Z3NlArith.fst) | `src/math/lp/nla_basics_lemmas.cpp`, `nla_order_lemmas.cpp`, `nla_monotone_lemmas.cpp`, `nla_tangent_lemmas.cpp`, `nla_powers.cpp`, `nla_divisions.cpp`, `nla_transcendentals.cpp` (47 lemmas verified; unlike the other audits above, 9 rest on explicitly-labeled, standard real-analysis `assume`s for `exp`/`log`/`sin`/`cos`/`atan2`, since those functions aren't part of a decidable SMT theory) |
| Bool/arith rewriters | [`BOOL_ARITH_REWRITER_REPORT.md`](BOOL_ARITH_REWRITER_REPORT.md) | — (lemmas stated directly over `bool`/`int`/`FStar.Real`) | [`Z3BoolRewriter.fst`](Z3BoolRewriter.fst), [`Z3ArithRewriter.fst`](Z3ArithRewriter.fst), [`Z3ArithRewriterPower.fst`](Z3ArithRewriterPower.fst), [`Z3ArithRewriterCast.fst`](Z3ArithRewriterCast.fst), [`Z3ArithRewriterOrder.fst`](Z3ArithRewriterOrder.fst) | `src/ast/rewriter/bool_rewriter.cpp`, `src/ast/rewriter/arith_rewriter.cpp` (66 lemmas verified: AND/OR/NOT/ITE/EQ/DISTINCT/XOR/IMPLIES/NAND/NOR/GE2 propositional identities, div/idiv/mod/rem/abs/power/to_int/to_real/is_int arithmetic identities, and lt/gt/eq2ineq/ite-lifting/to_int-comparison-bridging/is_bound/is_separated comparison-operator identities; the arithmetic lemmas are split across 4 files purely because Z3's combined proof search times out, not because of any change in content) |
| Sequence equation solving (`theory_seq`) | [`SEQ_EQ_SOLVER_REPORT.md`](SEQ_EQ_SOLVER_REPORT.md) | [`Z3SeqTheory.fst`](Z3SeqTheory.fst) | [`Z3SeqEqSolver.fst`](Z3SeqEqSolver.fst) | `src/smt/seq_eq_solver.cpp` (soundness + completeness of `branch_variable_eq`/`find_branch_candidate`'s prefix-guessing case split and `len_based_split`'s length-aligned decomposition; also confirms a historical soundness bug in `propagate_length_coherence`, issue #11013/PR #11015, via a prove-the-fix/disprove-the-bug countermodel) |

See each linked report for the full scope decision, function-by-function
coverage table, notable results, and remaining gaps for that audit.
