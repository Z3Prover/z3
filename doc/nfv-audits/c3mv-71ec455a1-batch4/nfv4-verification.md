# Batch 4: validity gate blocked all three selected properties

**Result: three translation/audit failures, zero verified properties, zero
refutations.** These are not discovered C++ index errors. No native Z3 source
was executed, built, imported or patched. Source/master/selection/model pins
remain those in `nfv4-model-freeze.json` and the model-stage handoff.

Exactly three verification attempts ran, all property-free validity checks.
Each removed ONLY its entry's three original ensures, retaining every input
requires, helper, helper contract and computation. All three returned exit4
with well-definedness diagnostics. The independent concrete domain checks,
original complete positives, negated goals, shorter consequences and candidate
repairs were NOT RUN after the failed prerequisite. The thirteen examples
therefore remain resolved input candidates, not admitted witnesses.

| Entry | Attempt | Outcome | Reported well-definedness errors |
| --- | --- | --- | --- |
| P20 | 001 | translation/audit failure | `Widths` line294; `Deactivate` line431; two `Rebase` accesses line737 |
| P21 | 002 | translation/audit failure | `Widths` line294 |
| P22 | 003 | translation/audit failure | `Widths` line294, even though interning itself does not use this shared helper |

Locations refer to the exact property-free inputs saved in `nfv4-models\checks`,
not production source lines. The complete original diagnostics are retained
in the adjacent `.log` files, including P21's unusual-indentation warning in
a quantified cache invariant. Individual Dafny verified-declaration totals
are NOT whole-property verdicts. There were no timeouts or MBQI retries.

## Cause and why the gate is not bypassed

The sequence constructors have lambdas with direct indexing, but the lambda
parameters do not carry the domains needed to establish those accesses:

```dafny
{ seq(|rows|, i => |rows[i]|) }
{ seq(|active|, i => active[i] && i!=idx) }
{ seq(|rows|, i => if B(active,i) && tok in rows[i] then Substitute(rows[i],tok,repl) else rows[i]) }
```

These constructor-index obligations arise in helper definitions, independently
of an entry's input state or intended postcondition. The earlier successful
`resolve` operations established typing/resolution only; they did not check
these obligations. Totalization of `I`, `B`, `R` and row decoding did NOT make
every other helper access well-defined. In particular P22's failed auxiliary
definition says nothing about native canonical interning correctness.

Adding a lambda domain or replacing these accesses with totalized helpers is
a translation change beyond this seal's allowed assert/invariant/decreases
annotations. No such change was made; no helper was skipped or admitted,
positive property weakened, optional restriction invented, domain check
assumed, or failure relabeled as a counterexample. Merely switching solver
options cannot justify admitting an unguarded partial lambda. There is no
meaningful original-goal proof or candidate repair to accept at this gate.

## Evidence and continuation

`verify_nfv4.py` is the bounded replay runner. `nfv4-models\checks.json` records
every exact input/log hash, complete command, duration and exit code. Commands
explicitly use Dafny4.11 and bundled Z3 4.12.1 with a30-second per-obligation
limit, two cores, warnings retained and snippets disabled. Total wall time of
the three verifier subprocesses was6.808 seconds. This is separate from the
twenty construction/provenance checks, whose three initial resolve failures
also remain preserved. No existing batch history or sealed model was changed.

`nfv4-results.json` gives the gate-aware outcomes; `nfv4-followups.json` records
the genuine remaining work. Publish this unsuccessful but substantive audit
checkpoint next, then prepare a NEW explicitly identified translation revision
for the SAME three whole-entry intents. Correct the lambda well-definedness
without changing intended evaluated-index behavior, input contracts, original
whole goals or example values; freeze it before its own validity/domain/proof
checks. Do not count this retry as new source-property coverage or overwrite
batch4's failed model evidence. The gpower-chain and temporary-length/cache
candidates remain source-level hypotheses, not accepted model refutations or
native findings. P13 and P18 remain unresolved too.

This remains a manual local NFV-methodology audit, not a hosted driver run or
upstream admission/correspondence proof. Schedule2 remains active; the next
separate scheduled stage is `nfv4-publish`, not a stop condition.
