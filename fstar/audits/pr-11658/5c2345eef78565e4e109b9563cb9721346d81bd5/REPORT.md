# F* audit of PR #11658 @ 5c2345eef78565e4e109b9563cb9721346d81bd5 (base 145c0c51570a357cc558ce898ce77573ba9d4fbf)

PR was open at this head; no prior fstar-nfv-audit comment found.

## Scope (partial)
Audited 1 changed function: context::mk_enode in src/smt/smt_internalizer.cpp (head line 1116, branch e->is_true_eq()). Change: push_eq(e, m_true_enode, eq_justification()) -> eq_justification(literal(v)). The diff base..head of this file is exactly this one line.
Source SHA-256 (base64-decoded GitHub contents API output): base 6b138808d0d6590e387d31b07e689275948cef3d0976c89560d323703f6c8d89, head 07f6bf41ad8a2e8d733b8a390721680745320a5a680806026ca71a3e199f1e2c.
Excluded: src/test/smt_context.cpp (new regression test check_late_equality_justification and a whitespace edit): not formalized, not executed (no PR code was built or run). Consumers of EQUATION justifications in smt_conflict_resolution.cpp (about lines 120, 852, 1158) were read manually only.

## Intended property and assumptions
Property: the explanation attached to the edge e ~ true must entail e = true so conflict clauses derived from it are valid.
Assumptions (read from source, not mechanized): A1 literal(v) is assigned true by the preceding assign(literal(v), eq_propagation_justification(arg0,arg1)); A2 conflict resolution expands an EQUATION justification to the literal as an antecedent (m_antecedents->push_back(js.get_literal()); proof via get_proof(literal)) while AXIOM adds no antecedent.

## Obligations (LateEqJustification.fst, all checked)
1. base_unsound: with an empty (AXIOM) explanation there is a model state (v=false) where the explanation holds but the edge is not entailed. This is an abstract-model witness only, not a reachable concrete Z3 run, hence NOT a counterexample verdict.
2. pr_sound: explanation {literal(v)} entails the edge in the model.
3. pr_complete: whenever the edge holds, the explanation holds.
Caveat (important): the model defines edge_true as v, i.e. it encodes the assumption that the edge's truth is exactly the atom literal's assignment, so obligations 2 and 3 are close to definitional. They support only that the explanation shape matches assumption A1/A2; they do not establish soundness of the C++ or that the lambda/array reproducer is fixed. Hence verdict inconclusive.

## Mapping and limits
st.v = truth of literal(v); edge_true = e merged with true; LitV = EQUATION justification; NoAnte = AXIOM. Not mechanized: C++ execution, enode/egraph plumbing, proof-producing mode correctness, conflict-resolution correctness, the regression test, memory safety. No admit/assume/lax; no base modules imported; standard F* library only.

## Reproduce
cd fstar-audit; /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out LateEqJustification.fst