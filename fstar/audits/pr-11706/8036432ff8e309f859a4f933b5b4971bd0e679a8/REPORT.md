# F* audit PR #11706 @ 8036432f

Base 1a1d88dd. F* 2026.09.27, Z3 4.13.3 (pinned release). Source: src/tactic/core/elim_uncnstr_tactic.cpp at head, sha256 a322984c078a895260b85bceee3c12564a150ddd526e7c1924a2da3dd30f3314; process_seq_app L806-845, reduce_app L868-875, add_defs L139-145.

## Obligations (all proved)
- O1: for n>0 args, model assignment arg0:=z, arg_i:=empty gives concat(args)=z (reconstruction soundness of all-unconstrained concat elimination).
- O2: the new m_seq_concat_only guard only restricts when the rewrite fires.
- O3: with the guard, firing implies all args unconstrained. (O2/O3 are Boolean-level and nearly trivial.)

## Findings
No counterexample. Observation: in seq-concat-only mode the early uncnstr(num,args) check precedes the x ++ (y ++ z) branch, which needs args[1] to be a concat (not a variable), so that branch becomes unreachable. This is an optimization loss, not unsoundness. reduce_app returns BR_FAILED for non-seq-family or non-concat operators in this mode.

## Mapping and assumptions
Lists model sequences and concat as append. The uncnstr predicate, ref counts, fresh-variable creation (mk_fresh_uncnstr_var_for, assumed fresh), model-converter plumbing and rewriter traversal are manually reviewed, not modeled. Not a mechanized proof of C++ execution.

## Exclusions (not audited)
default_tactic.cpp automatic_seq_regular_tactic; seq_regular_simplifier; guard_set; seq_derive; seq_regex_witness; seq_rewriter; theory_nseq and all seq_*_facet files; smt_params validate_string_solver; asserted_formulas; the tactic candidate-skip path in operator(); fstar/*.fst changes; docs and tests; all other files.

## Reproduce
With the base fstar/ directory available: /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --z3rlimit 10 --cache_dir cache --odir out Z3ElimUncnstrSeqConcat.fst