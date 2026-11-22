## Obligations
1. O1 (base refutation): base guard is_uninterp(term) admits term=f(a). With a=b, f(b)=-1 unmarked (does not syntactically contain f(a)), max f(a) with f(a)<=ite(c,1,0) is satisfiable (f(a)=-1) but the rewrite (f(a)=ite(p,1,0), p=>ite(c,1,0)>=1) is unsat. Checked in F* (o1_witness, o1_rewrite_unsat). This is the bug the PR targets; counterexample applies to base 8927ff98, not head.
2. O2 (head guard): is_uninterp_const(term) implies old is_uninterp and excludes applications with args (o2_refines, o2_strict). Proved, so O1 witness shape is not accepted at head.
3. O3 (recfun early exit): simplify_min_max_of_sums returns false when recfun::util(m).has_rec_defs() and is otherwise unchanged (o3_rec, o3_norec). Proved.

## Correspondence
term_kind abstracts app_ref term (UConst=0-arity uninterpreted, UApp=uninterpreted with args). Rewrite and original are modeled with f(a), f(b) as integer values plus functional-congruence constraint a=b ==> fa=fb.

## Assumptions / not mechanized
That mark_occurs only marks syntactically containing ASTs, that has_rec_defs() soundly detects hidden recursive dependencies, and that is_uninterp_const without aliasing through recfun is sufficient for soundness of the remainder of the rewrite are manual review. Not verified: C++ execution, memory safety, AST plumbing, the rest of the rewrite (cardinality thresholds), fresh-constant handling. Only Prims/FStar standard library trusted. No admit/assume.

## Exclusions
src/test/opt_bounds.cpp tests; fstar/audits/pr-11636/2202fc72... files in the PR; include of recfun_decl_plugin.h.

## Reproduce
fstar.exe --smt z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out OptIteBoundPR11636.fst (F* 2026.09.27, Z3 4.13.3). Source hashes: head opt_context.cpp sha256 b8e0493a7b36..., base 3ad24dd268d3....