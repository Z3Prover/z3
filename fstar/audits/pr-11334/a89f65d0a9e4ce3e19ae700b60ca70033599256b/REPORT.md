# F* audit PR 11334 @ a89f65d0a9e4ce3e19ae700b60ca70033599256b

Base 9dbe8c83fcadaba50a607236894f72a63959a5da. Source asserted_formulas.cpp at head sha256 6bfcf1bda3c602b8828d0382896ae1aa4fa254a66156a81c153cde2e2d75d19b (decoded contents API), function lines 411-470.

## Obligations (all proved)
1. Distribution (or a (not (or bs))) == conjunction of (or a (mk_not b)) - soundness of the rewrite (C++ loop over to_app(b) args, mk_not lambda).
2. New guard implies old guard (n==1 && m.is_not(e,d) && d->get_ref_count()==1 => n==1): the patch only removes rewrites.
3. Guard reachable/non-vacuous: passes when rc(d)=1, rejects rc(d)=2 and non-negation.
 Plus whole-clause-list rewrite_sound.

## Correspondence
ref count is modelled as a nat; F* does not model C++ ref counting. Model adapted from the earlier audit module (same rewrite, guard changed from rc(e) to rc(d)); module is self-contained.

## Assumptions
The ref count of d is only a heuristic for sharing; soundness of the rewrite does not depend on it (rewrite is valid for any guard). Standard FStar.List.Tot trusted.

## Exclusions
src/test/flatten_clauses.cpp, CMake/main.cpp test registration, fstar/audits files from the previous audit, performance claims (clause counts/memory), ref-count lifetime correctness (d->get_ref_count()==1 could vary with caches; only affects performance), the simplifiers variant, memory safety. Note: m.is_not(b,b) after guard and to_app(b) uses d with refcount semantic; any consequence is performance only.

## Reproduce
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --z3rlimit 10 --cache_dir cache2 --odir out2 FlattenClausesPR11334Head.fst

F* 2026.09.27, Z3 4.13.3 independent backend.