## Scope
Base 605d1d83a461, head d5f8a66a827e. src/solver/solver2tactic.cpp head sha256 (decoded) 1ddcd93a2263e556a163961d843433f17cd920795b0cc841f63cb3370810b36c, lines 104-160 (operator(), l_false case). Prior audit commit modified fstar/audits only; the C++ delta vs audited 4d9f42c3 is solver2tactic.cpp (Update solver2tactic.cpp).

## Obligations (all proved)
- O1 guards: with proofs enabled, reaching the substitution/assert path implies assumptions empty, proof non-null with fact false, and each goal proof fact equals its formula (else throws).
- O2: proof substitution of asserted(clause_i) leaves by goal proofs preserves the root fact (so result is still a proof of false), given per-assertion check.
- O3: lookup (incl. duplicate clauses, insert overwrites) returns a proof whose fact equals the clause.

## Correspondence
proof = ASTs of asserted(f)/node/goal-proof; fact = m.get_fact; subst = expr_safe_replace (replaces asserted leaves only, node facts stored, so unchanged by model); env = clauses[i] <-> in->pr(i). Assumes clauses[i]==in->form(i) (true when no dependency/unsat core, enforced by assumptions.empty() check under proofs; also assumes unsat_core disabled or deps empty).

## Assumptions/limits
Expr_safe_replace is modeled, not verified; it does not re-derive facts of inner nodes that mention replaced subterms (the model treats facts as stored). SASSERT is debug only; release relies on 1-1 clauses/goal, which holds here since extract_clauses pushes one clause per formula. Pure F* model; not C++ verification. Inherits only F* standard library (FStar.List.Tot). Not checked: whether solver proofs contain asserted(clause) in same form (e.g. after solver preprocessing); if not, substitution is silently a no-op and the resulting proof would be unsound-looking, not detected.

## Reproduce
fstar.exe --smt z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out S2tSubst.fst (F* 2026.09.27, Z3 4.13.3)
