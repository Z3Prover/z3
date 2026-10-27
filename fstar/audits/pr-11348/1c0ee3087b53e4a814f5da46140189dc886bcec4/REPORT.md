Head 1c0ee3087b53e4a814f5da46140189dc886bcec4 (previous audit: 4d57120). F* 2026.09.27, Z3 4.13.3 (pinned backend).
Partial scope: 3 functions, 3 obligations (changes since 4d57120 audited; PR has more files).
Functions: seq::axioms::at_axiom (seq_axioms.cpp ~L681-690), theory_seq::fixed_length (theory_seq.cpp ~L556-580), theory_seq::propagate/solve_eqs (m_new_solution handling).
- O1 proved: expansion only for numeral indices <= 1024 (<=1025 nth terms); larger go to the symbolic pre/tail split; small ones unchanged.
- O2 proved (model): if m.inc() fails mid-loop, m_fixed is not marked and false returned, so the element is retried; on completion it is marked before mk_seq_eq as in base.
- O3 proved (abstract flag model): cancelled solve_eqs with pending eqs leaves m_new_solution=true, which propagate no longer clears. Manually reviewed only: that simplify_and_solve_eqs's loop exit on cancel keeps the flag.
Assumptions: m.inc() may be false at any check; booleans model the guards. Not mechanized C++ semantics.
Excluded: rlimit.cpp auto_cancel pop_timeout change (timer/thread semantics), theory_arith_core.h and theory_lra.cpp mk_th_axiom under proofs_enabled, seq_eq_solver.cpp details beyond flag, tests, fstar tools, check_fixed_length loop guard.
Command: fstar.exe --smt .../z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3Pr11348Seq.fst
