## Scope
Head e487449e, base f46b3c58. Audited: (A) cross_nested::report_result in src/math/lp/cross_nested.h; (B) intervals::check_nex try/catch in nla_intervals.cpp (only the exception-to-false mapping).

## Obligations (all proved)
- O1: without cancellation, new report_result == old `m_done = r || ++m_reported > 100` (including short-circuit: counter not bumped when r is true).
- O2: when canceled, m_limit_exceeded is set, m_done and m_reported unchanged (a canceled run is not recorded as done/success).
- O3: check_nex maps interval_limit_exceeded to false (no conflict claimed); normal paths return as before.

## Correspondence
CrossNestedReport.fst models the state (m_done, m_limit_exceeded, m_reported) and boolean results. Not mechanized: C++ execution, reslimit semantics, exception safety/cleanup of scoped_dep_interval and lemma_builder state on throw, memory safety.

## Assumptions
reslimit.is_canceled is an environment boolean at call time; no base F* modules were imported beyond F* standard library.

## Exclusions
horner.cpp loop guard, nla_core.cpp done()/check() cancellation, nla_grobner.cpp guards, nla_intervals.h visibility changes, tests (src/test/horner.cpp, nla_intervals.cpp), has_inf_interval/get_zero_interval_child/interval_of_expr checkpoint() (note: checkpoint uses m_limit.inc(), which also consumes rlimit count, a possible behavior change not analysed). Residual risk: a callback cancelled mid-call may have partially emitted a lemma before throw in check_nex; not analysed.

## Reproduce
fstar.exe --smt z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out CrossNestedReport.fst (F* 2026.09.27, Z3 4.13.3). Marker: fstar-nfv-audit:e487449e53357bf911c48ad1d44d059650919fea