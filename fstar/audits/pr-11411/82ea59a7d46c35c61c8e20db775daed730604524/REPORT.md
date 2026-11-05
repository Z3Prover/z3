## F* audit PR #11411 @ 82ea59a7d46c35c61c8e20db775daed730604524 (base 02f6a7e1)

Changed function: `mk_subterm` in src/ast/datatype_decl_plugin.cpp (+25 lines, ~L468-495). Excluded: the .h comment edit, src/test/parametric_datatype.cpp, and all other code.

### Obligation 1 (proved): no-throw implies no nested/mutual recursion
Property: if the worklist (seeded with non-self accessor ranges of domain[0]) completes without raising, then no sort reachable via accessor ranges of datatypes or sort parameters equals d (by datatype name).
F* model: `run` mirrors the todo/visited loop (raise on s=d, else push successors); `sound` proves an invariant (d not visited, seeds covered, visited closed under succ modulo todo); `no_nested` derives the property using reachability `reach`.

### Correspondence / assumptions
- Sorts abstracted as nat ids; datatype_name equality modelled as id equality; `succ` abstracts accessor ranges plus sort parameters (arbitrary function, so also covers cycles). Fuel exhaustion models as a raise (conservative); the C++ terminates since the visited mark bounds finite sorts.
- Not modelled: the is_declared exception (only adds raises), ast_mark/ptr_vector memory behaviour, get_def exceptions, C++ execution. Manually reviewed only; not a mechanized proof of C++.
- Observation (not verified formally): a visited non-self datatype whose own definition is in an unrelated recursive group terminates via marking. Accessors with range == d at top level are skipped by design (direct recursion allowed).
- Standard F* library assumptions only; no admit/assume.

### Reproduce
`cd /tmp/gh-aw/agent/fstar-audit && /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --cache_dir cache --odir out --z3rlimit 10 SubtermNested.fst`
F* 2026.09.27; Z3 4.13.3.