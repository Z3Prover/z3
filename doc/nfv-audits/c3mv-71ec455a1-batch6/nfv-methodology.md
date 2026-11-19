# Stage 1: pinned NFV methodology

Status: complete. This is a local audit following NFV's general Dafny method, NOT execution of the hosted deterministic NFV driver. No official report.json/comment.md or hosted run identity will be fabricated. The user authorizes a new audit report and evidence committed and pushed to c3mv.

## Immutable inputs

- Head: 71ec455a18702fe695d0c924a535ff9f385bd58d (c3mv).
- Master: d738f81eab9af1468394664a812fe4310ae8e1fa (origin/master fetched 2026-11-19).
- Merge base: 437536cd64a544a1c329fc57d83e56e294fdf47c.
- NFV package/source: microsoft/neuro-formal-verification at 599726579274cfeb1c0915414b911371527a9870.
- Branch-introduced delta (merge base to head): 104 files, 158837 additions, 323 deletions.
- Direct master-to-head tree comparison: 107 files, 158838 additions, 397 deletions. Stage 2 MUST examine the extra master-side differences and distinguish missing upstream changes from c3mv-introduced changes. Use both comparison forms accurately in report; do not silently conflate them.
- Worktree was clean after fetch; user's prior modifications are preserved in stash@{0}. Do not touch the stash.

## Authoritative material read

Local .github/workflows/nfv-pr-review.md lines 1-282 and nfv-source-context.md lines 130-178. Package manifest .github/aw/packages/microsoft-neuro-formal-verification-workflow-f129a0ff0f1c.json pins upstream as above.

At that exact upstream revision, read README.md, workflow/README.md, .github/skills/nfv-pr-review/SKILL.md, workflow/src/nfv_workflow/{function_prompt.txt,intent_prompt.txt,general_prompt.txt,proposal_prompt.txt,followup_prompt.txt}, and general_gates.py first 18000 characters. Fetch remaining general_gates.py if needed. Public raw.githubusercontent.com and unauthenticated api.github.com work. gh API access to github/gh-aw returned SAML 403; not relevant to z3 push and not retried. The gh-aw generic debug guide was obtained over public raw HTTP; no workflow changes/dispatch are needed for this audit.

## Selection and translation rules

1. Select at most TEN meaningful changed functions/properties. Read varied production implementations and dependencies, not just tests. Preserve whole properties, not separate checks of each conjunct. Source-inferred hypotheses are allowed by intent_prompt.txt; identify them as hypotheses and quote exact text in the selected changed function. Commit intent may also ground properties. Do not select only suspected failures. No PR was supplied, so do not invent PR claims.
2. One changed function is each entry, with a faithful focused source slice and relevant helper definitions. Source is inspected as text, never executed, built, tested, or imported. Read callers for applicability but do not assume they are the only callers. Do not select a callee property while leaving that same callee's meaningful behavior unconstrained.
3. Keep actual guards, state updates, loops, helper effects and numerical semantics. Model unknown irrelevant call results as disclosed abstract inputs, never convenient constants. Infer only the weakest justified environment contracts. Declare all limitations, aliasing/reference assumptions, arithmetic bounds/overflow modeling, omitted effects and no proved C++/Dafny correspondence.
4. Entry is a body-defined non-ghost top-level method with named int/bool/seq<int>/seq<bool> parameters and at least one such return. All outputs assigned on every path. All helpers have bodies and source-anchored environment metadata. No top-level const/type/newtype declarations. Entry name must not collide with source-tagged declarations.
5. Every code line immediately follows exact // src: path:LINE | trimmed actual source line, or // synth: reason. Synthetic code is restricted to braces, contracts, invariants, asserts, decreases, reads, modifies. Exact multi-line source tags may precede a single computation. Every significant source line in the selected span, including changed anchors, is covered. This is provenance, NOT a translation-equivalence proof.
6. Original ensures encode the WHOLE positive property. Each requires has exactly one metadata entry (origin=inferred; optional=false for actual applicability and optional=true only for removable extra restrictions). Every helper, including specification functions, has metadata and a body. No assume/axioms/includes/imports/modules/bodyless declarations/verification attributes/decreases * or trust escapes. Guards must establish index domains before using indices in contracts.

## Checking and acceptance

- Draft repairs may fix syntax, types and faithful computation/contracts before freeze. Never weaken a property or hide a real input to force success. Save diagnostics and the frozen model hash before proof search.
- First validate model/type/provenance independently of the intended property. Remove only entry ensures for the validity check; preserve computation, domain, helper contracts and well-definedness obligations. A separate concrete domain driver must prove non-vacuous inputs and entry preconditions.
- Verify the original complete property first on the frozen model. Only proof annotations (assert/invariant/decreases) can change later; computation, assumptions, helper contracts, witness and original/negated goal stay frozen.
- A failed proof alone is NOT refutation. Require every-input concrete int/bool/list witness; mechanically negate the complete conjunction of original postconditions with parentheses; add witness pins separately and prove the negated property. Independently prove the concrete driver satisfies input/domain constraints. Never claim a source execution trace.
- Outcomes: verified, refuted, resources exhausted, type-check/audit failure. Report all selected properties and distinguish inability to prove, model invalidity and timeout. Verification/refutation apply ONLY to translated models under stated assumptions; never source-confirmed correctness/bugs.
- For accepted refutations: try deleting optional restrictions with rechecks; seek a shorter property implied by the original with inputs AND outputs free, and separately refute it on the frozen model and original witness. Bounded effort only, no global-minimality claim.
- Candidate fixes, if justified: only entry computation changes; input signature, retained requires, FULL original ensures and all helpers are fixed. Prove complete original property generally and check original witness domain. Clearly distinguish candidate model repair from compiled/tested/source-verified fix. No C++ patch application in this task.
- Publish an independently authored local audit report, not a purported modification of hosted generated comment.md. Include exact revisions, upstream sources, full property/domain metadata, coverage/exclusions, source anchors, verified counterexamples if any, commands/versions, unabridged compact verifier diagnostics and model hashes. No fabricated hosted links.

## Trusted verifier installed in session workspace

Concrete missing-tool check `dafny --version` failed (command not found), authorizing dependency installation. Downloaded official v4.11.0 Windows archive over HTTPS into session files/nfv-tools; did not install globally or alter PATH.

- Archive URL: https://github.com/dafny-lang/dafny/releases/download/v4.11.0/dafny-4.11.0-x64-windows-2022.zip
- GitHub release API asset digest: sha256:3653f05a111ca21e234709ea7b25ce96083fd6c6f10484256ba54110dbc0654d
- Downloaded archive SHA-256: 3653f05a111ca21e234709ea7b25ce96083fd6c6f10484256ba54110dbc0654d (match).
- Dafny: C:\Users\nbjorner\.copilot\session-state\41a24878-0132-4dff-ba04-d7afa4eaaafb\files\nfv-tools\dafny\Dafny.exe
- Observed version: 4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2
- Solver: same directory\z3\bin\z3-4.12.1.exe
- Observed version: Z3 version 4.12.1 - 64 bit.
- Archive also bundles 4.14.1; do NOT accidentally use it. Supply --solver-path explicitly.
- .NET 8.0.34 runtime available.
- Verification command template: & $dafny verify $file --solver-path $z3 --verification-time-limit 30 --cores 2
- Dafny verify --help confirmed these flags. Limit cores to avoid monopolizing shared machine. Use bounded per-property timeouts and report actual limits; do not build/run audited Z3 code.

## Scheduling and remaining stages

Schedule #1 is every 10 seconds, one stage per scheduled turn. Read todos and nfv_audit_state; mark stage in_progress then done. Stage 2 mapping; stage 3 model construction; stage 4 verification; stage 5 report and publication. Use session files for handoffs; report/evidence eventual destination doc\nfv-audits\c3mv-71ec455a1. Final commit includes only audit artifacts and required Copilot trailers. Push c3mv without force and verify remote commit, then stop schedule #1. Preserve unrelated work and stash.
