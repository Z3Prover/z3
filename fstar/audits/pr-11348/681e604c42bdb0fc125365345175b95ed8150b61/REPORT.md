## Scope
Head 681e604c42bdb0fc125365345175b95ed8150b61 (base aa71a62f). Audited only the new behaviour in `reslimit::auto_cancel` (src/util/rlimit.cpp lines 160-165, sha256 of file 1bd64277...7900; rlimit.h sha256 3814a360...f7e), under POLLING_TIMER.
Change: after `--m_num_timers`, if it reaches 0 call `pop_timeout()` (m_timeout_ms=0), then `dec_cancel()`.

## Obligations (all proved)
- O1: releasing the last timer leaves num=0 and timeout cleared (no stale deadline).
- O2: releasing a non-last timer leaves the timeout armed for remaining timers.
- O3: after `is_timeout` fires (cancel += num, pop_timeout), num releases restore cancel and num=0 (given cancel >= num).

## Correspondence / assumptions
Record {cancel,num,tms} models m_cancel, m_num_timers, m_timeout_ms; dec_cancel clamps at 0 as in C++. Assumes auto_cancel is called only with num>0 (precondition; callers: cancel_eh dtor via scoped_timer sets auto_cancel after push_timeout). Unbalanced release at num=0 would wrap unsigned (shown by wrap witness assert) - not shown reachable. Mutex/threading, children propagation via set_cancel, and timer values are not modelled. This is a semantic model, not verification of C++ execution. Only base F* stdlib assumed.

## Excluded (not reviewed)
theory_lra.cpp and theory_arith_core.h mk_th_axiom under proofs_enabled; seq_eq_solver.cpp, seq_axioms.cpp, theory_seq.cpp m.inc() / m_new_solution changes; qsat.cpp, basic_cmds.cpp (previously audited head 19d5ac84), all fstar/*.fst and OCaml/test changes, tests, CMake.

## Reproduce
`/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3RlimitAutoCancel.fst` (F* 2026.09.27, Z3 4.13.3), fresh cache, exit 0.