# F4 derivations through the existing Alethe/PAC pipeline

This change is based on `codex/qf-ff` at `4eda0e5ba`. It adds optional proof
recording to the fixed-width F4 backend and connects it to the existing
standalone certificate command and original-input Alethe/PAC checker pipeline.
The DAG format, PAC export rules and independent checkers are unchanged.

## What is certified

F4 records an input node for each original equation, a multiplication node
for each coefficient/monomial multiple, and an addition node for each row
subtraction. Initial normal-form reduction, matrix materialization, both
accumulator implementations and monic normalization retain these derivations.
Interned dense monomials are translated back to the original variable IDs.
A successful certificate derives the constant polynomial 1 from exactly the
original equations. Dependencies or an UNSAT status alone are never evidence.

Proof recording is optional during ordinary solving. In proof mode, the
backend stops after ideal reasoning: no sampled model, root split, field
closure, implicit disequality witness or cached basis becomes a proof input.
The existing input bridge introduces and checks disequality witnesses before
calling F4. Boolean resolution and ITE lemmas continue through the existing
Boolean pipeline. Independent replay binds the input, DAG and exact Alethe/PAC
bytes before external Carcara/FFPacheck acceptance is counted.

The caller's proof is replaced only on success. SAT/unknown, unsupported
arithmetic, cancellation and resource exhaustion cannot publish a partial DAG.
Proof storage is bounded to 100,000 nodes and an estimated 16 MiB; recording
and multiplier conversion consume the reconstruction's shared work allowance.

## Search controls

```smt2
(ff-certify :backend auto :timeout 10000)
(ff-certify :backend scalar :timeout 10000)
(ff-certify :backend f4 :timeout 10000)
```

`auto` preserves the existing scalar reconstruction and its conflict cores
when successful, then tries F4 after an unavailable scalar result. Both
attempts share the original work/cancellation budget; fallback never replenishes
spent work. A completely exhausted work allowance leaves no room for F4, but
a structural basis/DAG limit can leave enough budget for the alternate search. `scalar` retains the earlier search. `f4` forces F4 with the overall
reconstruction allowance and can report unavailable when scalar could succeed.
Fields unsupported by fixed-width arithmetic use the scalar fallback in auto.

The pipeline exposes the same choice as `--backend auto|scalar|f4`. Its auto
invocation omits the new command option so archived, pre-selector binaries
remain usable as benchmark baselines. Benchmark configurations can set
`certificate_backend` for an ablation without changing the proof format.

```sh
python3 scripts/ff_proof_pipeline.py problem.smt2 --out /tmp/ff-proof \
  --z3 build-ff-cmake/z3 --backend auto \
  --carcara /path/to/carcara --ffpacheck /path/to/ffpacheck
python3 scripts/ff_proof_pipeline.py --check --out /tmp/ff-proof \
  --carcara /path/to/carcara --ffpacheck /path/to/ffpacheck
```

## Scope boundaries

This is standalone reconstruction with proof-producing F4, not native Z3
`get-proof` support or complete certification of the optimized solver.
The uniqueness tactic and tiny-field search do not yet emit checked traces.
Some of their UNSAT answers can be reconstructed independently as ideal
contradictions, but that does not certify those algorithms' own execution.
Finite-field root/closure arguments, bit-uniqueness lemmas, UF/theory combination
and full solver proof composition remain follow-up work. No Lean checking is
claimed. A missing proof remains unavailable and is never counted as checked.

## Validation and measurements

The native suite and the finite-field regression harness in `Z3Prover/z3test`
exercise
proof replay, arithmetic widths, failure atomicity, exhaustive SAT/UNSAT oracles,
and resource recovery. External tests use the pinned checkers documented in
`regressions/finite_field/proof_checkers/README.md` in `Z3Prover/z3test`.

Historical benchmark results and plots are preserved in the
[immutable artifact snapshot](https://github.com/RSoulatIOHK/z3/tree/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/doc/qf-ff-f4-certificates).
Their counts apply to their recorded solver revisions.
