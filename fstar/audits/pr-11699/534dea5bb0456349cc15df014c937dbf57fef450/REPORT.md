# F* audit PR #11699 @ 534dea5bb0456349cc15df014c937dbf57fef450 (base 1a1d88dde7cc567e2ed6beeea05321aa5a223c8a)

Scope (partial): one changed function, `horn_tactic::operator()` in src/muz/fp/horn_tactic.cpp (lines 403-411 at head; sha256 of head file b18e458d6aa8...; base f911db80c11d...). Excluded: the test file src/test/smt_context.cpp (check_horn_proof_diagnostic), the imp class, solver wrapping/exception-to-unknown conversion, and other tactics.

Change: pass-through on proofs now only when m_is_simplify (horn-simplify); the full `horn` tactic calls fail_if_proof_generation("horn", in), which throws tactic_exception "horn does not support proof production" when in->proofs_enabled() (src/tactic/tactic.cpp:297-303).

Obligations (all proved in HornProofGuard.fst):
- O1: non-simplify horn with proofs -> Throw; without -> RunImp.
- O2: horn-simplify behaviour identical to base for all proof settings.
- O3: with proofs disabled, behaviour identical to base.
- Witness: base horn with proofs returned PassThrough (goal unchanged, hence unknown); head throws a diagnostic.

Correspondence: boolean model of the three branch outcomes. Assumptions: fail_if_proof_generation throws iff proofs_enabled (read manually); tactic_exception is turned into l_undef with that reason string by the caller (not mechanized; tested by the PR's unit test, not run here). Not covered: C++ execution, memory safety, whether some pipeline relies on full `horn` passing through proofs-enabled goals (behavior change from silent pass-through to exception), and whether unknown-with-diagnostic is the desired fix versus actually supporting proofs.

Tools: F* 2026.09.27, Z3 4.13.3 (pinned independent backend), z3rlimit 10, 120s timeout, fresh cache.
Command: see verification log.