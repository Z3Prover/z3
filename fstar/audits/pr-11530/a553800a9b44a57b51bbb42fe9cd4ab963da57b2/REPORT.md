## F* audit PR 11530 (fstar-nfv-audit:a553800a9b44a57b51bbb42fe9cd4ab963da57b2)
Base 4629738b, head a553800a. Head pull_quant.cpp sha256 a2c74409c229f21ca3f484b34b9a2466680bc435189885f6a523d13244c08dd7 (395 lines; change at line 285). Tools: F* 2026.09.27, Z3 4.13.3 (pinned release).

### Change
In reduce_quantifier, exists branch (lines ~281-288): `m.mk_rewrite(old_q,result)` result was discarded; now stored in `result_pr`. Guard: is_exists(old_q); result = not(forall(mk_not(new_body))).

### Obligations (all proved)
1. ob1: ast_util mk_not is semantic negation (incl. double-negation/true/false cases).
2. ob2: exists x. B <=> not forall x. mk_not B (semantic soundness of the rewrite the certificate asserts; the PR_REWRITE fact is thus true).
3. ob3: caller (rewriter_def.h lines 622-636) composes m_pr (q=new_q or null) with pr2 via mk_transitivity; with pr2 non-null, endpoints are q = result. ob3_old shows pre-PR (pr2 null) left endpoint at new_q != result.

### Correspondence/assumptions
Formulas modeled as a small propositional AST with per-bound-value valuations; mk_transitivity modeled on endpoints only (SASSERT fact match assumed, as in the caller). Pattern/weight handling in update_quantifier, de Bruijn indices, AST plumbing, memory safety and the C++ test code (src/test/simplifier.cpp, +58 lines) are manually reviewed only/excluded. The proof does not mechanize C++ execution. The forall branch (pull_quant1_core) and lambda branch are unchanged and excluded.

### Reproduce
`fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3PullQuantExists.fst` (exit 0, fresh cache).