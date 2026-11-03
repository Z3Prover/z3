# F* audit of PR 11528 @ 899aabd4c53e7881352c4250c34657fd2b34db59 (base 4629738b)

Scope: PARTIAL, 3 changed behaviors, 1 obligation each, abstract model only.

## Obligations
1. split_clause_tactic::operator() (src/tactic/core/split_clause_tactic.cpp, ~L110-125): `in->add(split_pc)` instead of `in->set`. Property: parent converter composed after split_pc, i.e. parent(split(children)). **proved** (`o1`); old behaviour provably differs (`o1_old_drops_parent`).
2. goal::pc() (src/tactic/goal.h ~L157): inconsistent goal yields concat(m_pc, proof2pc(pr0)) rather than dropping m_pc; null if no pr0. **proved** (`o2`: result = c [p]).
3. Materialization in and_then/par_and_then/repeat/check_sat: apply(m, pc) then clear converter; second boundary applies nothing. **proved** (`o3`) for consistent goals only.

## Correspondence / assumptions
Proof terms are an abstract tree; conv = list proof -> proof mirrors proof_converter::operator(); concat mirrors concat_proof_converter (c2 first, then c1); subgoal_pc mirrors subgoal_proof_converter. No base F* modules imported; only F* stdlib (FStar.List.Tot). Not modeled: ref-counting/lifetimes, the new `subgoal_i->set(nullptr); subgoal_i->set(in->mc())` child-scope reset in split_clause (only reviewed manually; goal copy ctor copies m_pc, so reset is needed for child-local scope), exception paths in check_sat, proof validity (split_pc SASSERT num_source == #args), translate().

## Exclusions
proof_converter.cpp `apply(m, pc)` (trivial null-guard; semantics reflected in apply0), tactic.cpp check_sat exception handling, tests, docs md, api_tactic.cpp / inc_sat_solver.cpp consumers of goal::pc() (now receive concat for inconsistent goals; not audited), par_and_then and repeat beyond the shared pattern.

## Manual-review notes
- goal::pc() allocates a fresh converter on each call for inconsistent goals; repeated calls are fine semantically.
- Inconsistent goal with pr0 and m_pc != null: m_pc is now applied on top of pr0; in and_then the in->reset_all() leaves m_pc intact, so apply(m, in->pc()) composes correctly with new clearing.

Semantic model only; not mechanized C++ verification.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit; F=/tmp/gh-aw/fstar; $F/bin/fstar.exe --smt $F/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3PR11528ProofConverter.fst
Versions: F* 2026.09.27, Z3 4.13.3 (pinned release).
