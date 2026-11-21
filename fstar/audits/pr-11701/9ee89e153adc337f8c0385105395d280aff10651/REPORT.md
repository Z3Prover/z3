## Scope
Head 9ee89e153adc337f8c0385105395d280aff10651, base 1a1d88dde7cc567e2ed6beeea05321aa5a223c8a. F* 2026.09.27, Z3 4.13.3 (pinned independent backend). Source: src/smt/theory_array_full.cpp (lines 794-814, 1034-1090 at head; blob 0de8b182d918aff197205d58098686938b6730cc).

## Obligations
1. (proved, abstract model) Guard in instantiate_default_lambda_def_axiom (large domain -> return false): the removed axiom default(L)=L[eps], combined with store-preserves-default on unbounded domains, is inconsistent whenever L[eps]<>v (lemma removed_axiom_inconsistent, store_preserves_default). So skipping it on large domains is justified; this supports the fix.
2. (proved, abstract model) has_non_beta_as_array new give-up: an observed default on a store chain with no const anchor is underdetermined (lemma underdetermined: negating all defaults satisfies select/store constraints yet changes the default), while a const fixes it (const_fixes_default). Giving up (FC_GIVEUP) rather than FC_DONE is therefore the sound response.
3. (not modelled) has_large_domain signature change from app* to sort*: refactor; reviewed manually, no semantic change evident.

## Assumptions / gaps
Arrays modelled as default plus finite exception list over int domain; large domain means unbounded. Not proved: that the C++ traversal (todo/visited over enodes, parents, relevancy) computes exactly the const/default reachability described, that has_large_domain correctly classifies sorts, that skipping the axiom never loses completeness (only sat/unsat soundness of unsat answers is argued), that m_lambdas/non-large domains behave as before, or memory safety. Test file src/test/smt_context.cpp and theory_array.h/theory_array.cpp plumbing excluded. PR is marked WIP.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3PR11701ArrayDefault.fst

fstar-nfv-audit:9ee89e153adc337f8c0385105395d280aff10651