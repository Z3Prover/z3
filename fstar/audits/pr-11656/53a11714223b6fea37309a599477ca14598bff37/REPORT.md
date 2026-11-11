# F* audit: PR #11656 head 53a11714223b6fea37309a599477ca14598bff37 (base 145c0c51570a357cc558ce898ce77573ba9d4fbf)

Scope (partial): one changed function, `recfun_rewriter::mk_app_core` (src/ast/rewriter/recfun_rewriter.cpp, new lines ~92-97; file sha256 head 4fc08dbd057e3dca8c6af08f7b8e4aa4fdcf968907495e9e27eeab4d3d4e3ac0, base 43e00daeaf39739ae032275ff51f7d7cfdbac0eaf397063efe9fd5989053ac12, decoded from contents API). Excluded: src/test/smt_context.cpp (test only), the `#include "ast/occurs.h"`, theory_recfun, and all non-substitution branches of mk_app_core.

Intended property: after var_subst, if the result contains the original call f(args) the rewriter returns BR_FAILED (left to resource-limited theory_recfun); otherwise behaviour is unchanged. Environment assumption: occurs(expr,expr) is structural subterm search (src/ast/occurs.cpp, manual review); hash-consed ASTs make pointer equality = structural equality; f's definition equation holds.

Obligations (model: tiny unary term language, `step` = substitute then guard):
- O1 PROVED: Some r implies r = subst body arg and f(arg) does not occur in r; None implies it occurs.
- O2 PROVED: whenever step returns Some r, r is semantically equal to f(arg) under the defining equation (guard cannot introduce unsoundness; BR_FAILED is the identity).
- O3 witness (disclosed trade-off, NOT a soundness counterexample): g(x)=ite(x>0, g x, 7) on 0 yields None although the self-call branch is dead (g(0)=7 under every interpretation). This is a completeness/simplification regression consistent with the PR description. `o3b` shows a call on different arguments still unfolds.

Findings: no soundness defect established. Not covered (also stated by the PR): non-identical cycles (ite (> x 0) 0 (f (- x 1))) and mutual recursion still can loop at assert time; the guard only detects the syntactically identical call. Termination of the rewrite loop was not proved.

Mapping/limits: F* is a semantic model, not mechanized C++ execution; AST sharing, memory safety, ref counting, the multi-arg case and `occurs` implementation are manually reviewed only.

Reproduce: `timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out RecfunSelfCall.fst` in the audit directory with fresh cache/out. F* 2026.09.27, Z3 4.13.3 (pinned release backend).
