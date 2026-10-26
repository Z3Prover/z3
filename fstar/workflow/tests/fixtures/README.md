# Workflow test fixtures

Small excerpts of real, public Pulse checker artifacts (Z3Prover/z3 Actions), trimmed for tests.

- `pulse-run-40244844124-1/` — rows copied verbatim from the `pulse-checker-report-40244844124-1`
  and `pulse-checker-cherry-report-40244844124-1` artifacts of regression run 40244844124
  (attempt 1). Obligation lists were truncated and `pending`/`families`/`verdict` adjusted to stay
  consistent; the Cherry `smtlib-sample/results.jsonl` ends with a deliberately truncated record to
  exercise interrupted-run tolerance (as `run_checker_regressions.py read_results` allows).
- `build-run-40280393373-1/pulse-checker-build-report/` — `build.json`, `source.json` and a
  `build.log` excerpt (profiling lines and the `Error 19` SMT timeout block, ANSI codes removed)
  from failed build run 40280393373.
- `gh-runs-sample.json` — `gh run list --json` rows for both Pulse workflows as listed on
  2026-10-26, plus one synthetic successful build row (id 40200000000) to cover the success case.

They are test data only; nothing here was produced by running F*, OCaml or Cherry locally.
