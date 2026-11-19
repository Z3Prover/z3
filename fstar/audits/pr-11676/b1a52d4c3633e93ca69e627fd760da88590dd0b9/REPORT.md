# F* audit PR #11676 @ b1a52d4c3633e93ca69e627fd760da88590dd0b9

Source: src/ackermannization/ackr_model_converter.cpp at head (sha256 853159d3957452965b964362cc1a842c4d5a22c086b0d79d2e153a92b498eb25), convert_constants, lines ~98-130; changed loop bound at line ~109.

## Obligations (all proved, AckrLoop.fst)
1. Old cached bound (n fixed before loop): witness where constant 0's processing registers constant 1 ends at index 1 < length 2, so constant 1 is never converted (abstract model of issue #11637). Abstract witness; C++ reachability rests on the PR regression test, not mechanized.
2. Live bound: if the loop terminates, final index == final length, so every constant, including appended ones, is visited (lemma live_complete).
3. Same witness under the live bound visits both constants.

## Correspondence / assumptions
Constants are a list of ids; model completion inside add_entry is modelled as an arbitrary function `fresh` that appends constants. Assumes append-only growth with index-stable get_constant(i) (not checked in C++) and finite growth (termination modelled with fuel; not proved for C++). Correctness of converted values (add_entry store/default logic) and validity of the destination model are NOT verified.

## Exclusions
src/test/ackermannize.cpp (regression test); add_entry semantics; memory safety; C++ execution; ackr_info mapping.

F* 2026.09.27 with Z3 4.13.3 (pinned release backend). Not mechanized verification of C++.

Command: /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out AckrLoop.fst
Exit: 0
