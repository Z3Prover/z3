# F* audit PR #11439, head 86fadbc8966559117c78967825b7ee00cf0975c1 (base 70f966a79844ea3b18fe35e5711d55754e80460e)

Scope: one changed function, `simplify_inj_axiom` in `src/ast/rewriter/inj_axiom.cpp` (candidate loop, head lines 56-80). Only file changed; nothing excluded besides the unchanged remainder of the function (rebuild logic lines 81-139), which was only read.
Source SHA-256: head file 57dd4a60efa8e7b3daff8da62984567313a9955d5f3ab2e6bdd166699891bde3, base file daa6b7593ef417199a41aa9b112bf8a616b56177fae8a4454ce9ef6885df2079.

## Obligations (module InjAxiomAudit.fst)
1. O1 refutation of BASE behavior / acceptance of fix: for f(x,z,z) vs f(y,z,z) (x=V0,y=V1,z=V2) the base recognizer accepts, head rejects (`o1_base_accepts`, `o1_head_rejects`: PROVED). Semantic witness: model mf x z w = if z=w then x else 0 satisfies the original axiom and a<>b, f(a,a,b)=f(b,a,b) (`orig_ok`, `model_ok`), but falsifies the refined (fresh binder per position) axiom (`refined_fails`); and the refined axiom entails a=b (`refined_contradicts`). So the base rewrite is unsound on this input (counterexample against base, reproduces issue #11435); the head no longer refines it.
2. O2 invariant: whenever head's scan accepts, the list of counted passive variables has no duplicates (`scan_inv`: PROVED).
3. O3: when passive variables are distinct, the original axiom instances give injectivity for all z,w, i.e. the refined axiom's strength (`o3`: PROVED; trivial instantiation).

Verdict for the head: proved for these obligations.

## Correspondence / assumptions
`arg` models var/uninterp-const args; `step`/`scan` model the loop branches (found_vars, c1==c2 guard, is_var, early `return false`). The new check scans f1 args j<i, modelled by `mem c1 seen`; seen contains exactly earlier passive vars (the C++ scans all earlier args, which for earlier positions equal c1 only if c1 passed as a passive var, or c1 == var1/var2 — excluded since c1 != var1,var2). Constants (uninterp consts) are not variables so are unaffected. Not mechanized: C++ execution, hash-consed pointer equality as structural equality, the rebuild code, has_free_vars, pattern/binder construction, other side conditions (e.g. distinctness of passive vars from the equality vars is by the c1!=var1/var2 guard, modelled). Inherited assumptions: F* standard library and Z3 4.13.3 backend only; no base fstar modules imported.
Semantic modelling of the quantifier is by hand-built nat model, not of Z3's engine. Manual review: the fix is conservative (rejects only), so soundness is preserved; completeness loss is limited to repeated-passive-variable axioms.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit && F=/tmp/gh-aw/fstar && $F/bin/fstar.exe --smt $F/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include (base)/fstar --z3rlimit 10 --cache_dir out/cache --odir out InjAxiomAudit.fst
F* 2026.09.27; Z3 4.13.3 (pinned). Fresh cache, exit 0.
