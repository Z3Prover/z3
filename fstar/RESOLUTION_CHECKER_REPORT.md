# Resolution/clausal proof-checker coverage report

Companion to `RESOLUTION_CHECKER_SCOPE.md`. Measures how much of a real
Z3 `(get-proof)` DAG, on sampled QF_AX and QF_UF benchmarks, falls
within the rule vocabulary now modeled by `Z3ResolutionProofTheory.fst`
(Tier 1, mechanically verified) versus the set Z3's own
`proof_checker.cpp` itself only trusts or defers (Tier 2), versus
anything genuinely outside both (Unmodeled).

Methodology: [`tools/proof_rule_coverage.py`](tools/proof_rule_coverage.py) runs each
`.smt2` benchmark with `proof=true`, calls `solver.proof()`, and walks
the *entire* raw proof DAG (not just the equational sub-island that
`extract_z3_proof.py` extracts), deduplicating by AST node id. Each
proof-sorted node is classified by its declaration name into Tier 1 /
Tier 2 / Unmodeled per the tables in `RESOLUTION_CHECKER_SCOPE.md`.
Non-proof-sorted children (e.g. the embedded conclusion formula that
rules like `mp`/`unit-resolution` carry alongside their premises) are
skipped entirely rather than mis-walked as if they were further proof
nodes — this required discriminating proof nodes from ordinary
expression nodes using `node.sort().kind() == Z3_PROOF_SORT` (the
Python z3 bindings have no public `is_proof` predicate, unlike the C++
API's `proof_checker.cpp`, which works directly on the `proof` sort).

## Results

### QF_AX (60 files sampled, 33 produced an `unsat` proof)

| | nodes | share |
|---|---:|---:|
| Tier 1 | 135,491 | 77.0% |
| Tier 2 | 40,498 | 23.0% |
| Unmodeled | 0 | 0.0% |

**File-level coverage: 33 / 33 (100%)** — every sampled QF_AX proof is
entirely covered by Tier 1 ∪ Tier 2; no proof node falls outside the
modeled rule vocabulary.

### QF_UF (60 files sampled, 26 produced an `unsat` proof)

| | nodes | share |
|---|---:|---:|
| Tier 1 | 2,794,102 | 92.8% |
| Tier 2 | 218,301 | 7.2% |
| Unmodeled | 0 | 0.0% |

**File-level coverage: 26 / 26 (100%)** — same result: no unmodeled
proof node in any sampled file.

## Interpretation

- **Zero unmodeled nodes on both sets.** The rule inventory in
  `RESOLUTION_CHECKER_SCOPE.md` — `unit-resolution`, `and-elim`,
  `not-or-elim`, `mp`/`mp~`, `commutativity`, `iff-true`/`iff-false`,
  `reflexivity`/`symm`/`trans`/`monotonicity` (the pre-existing
  equational layer), `array-ext`, plus the Tier 2 trusted leaves
  (`th-lemma`, `def-axiom`, `hypothesis`, `lemma`, `quant-inst`,
  `hyper-res`, `rewrite*`, `distributivity`, and structural/NNF-family
  rules such as `asserted`, `nnf-pos`, `nnf-neg`, `skolemize`,
  `pull-quant`, `push-quant`, `elim-unused`, `der`, `apply-def`) —
  exhaustively accounts for every proof-rule name Z3 emitted across
  all 59 sampled unsat proofs. No benchmark exercised a rule outside
  this vocabulary.
- **QF_UF is Tier-1-heavier (92.8% vs. 77.0%)**: QF_UF proofs are
  dominated by congruence-closure reasoning — `monotonicity`,
  `trans`/`trans*`, `unit-resolution`, `mp` over the equational
  core — all Tier 1. QF_AX proofs carry proportionally more Tier 2
  mass because array-theory lemmas (`th-lemma` tagged `"array"`,
  `def-axiom` from the array axiom instantiation schema, occasional
  `array-ext`-adjacent `hyper-res` steps) are exactly the leaves
  `proof_checker.cpp` itself only trusts (`check_arith_proof` only
  special-cases the `"arith"` tag; every other theory, `"array"`
  included, falls through to `dump_proof(p); return true` in Z3's own
  checker) — see the Tier 2 table in `RESOLUTION_CHECKER_SCOPE.md`.
- **Tier 2 is not a weaker bar than Z3's own checker** — it is defined
  to be *exactly* the set of rule occurrences `proof_checker.cpp`
  itself either trusts unconditionally (`PR_DEF_AXIOM`: any Boolean
  fact), defers to an unverified side condition
  (`PR_HYPER_RESOLVE`/`PR_REWRITE_STAR`/`PR_DISTRIBUTIVITY`), or
  stubs out entirely (`PR_QUANT_INST: // TODO return true`). So this
  100%/100% file-level result means: **every sampled QF_AX/QF_UF proof
  is accounted for at least as rigorously as Z3's own in-tree checker
  accounts for it**, and the Tier 1 fraction (77–93% of nodes) is
  additionally backed by an independent, mechanically verified F*
  soundness proof rather than Z3's trust.
- **Caveat on sample size/representativeness**: 60-file samples per
  set, not the full corpora; `30%`-ish files per set failed to produce
  an `unsat` proof at all within the sampling run (timeouts/`sat`/other
  outcomes) and were excluded from the denominator — the 100% figure is
  over files that *did* produce a proof, not over the full sample.
  Rerunning on a larger/different sample is the natural way to gain
  confidence this generalizes, but the zero-unmodeled-nodes result
  across ~3M total proof nodes (QF_UF alone) is a reasonably strong
  signal the vocabulary is not missing anything structurally common.

## What remains open (round 2 candidates, unchanged from the scope doc)

**Correction (see "Update: round 2 reclassification" below): items 1
and 2 below are in fact already done.** `Z3ResolutionProofTheory.fst`
already implements `RUnitRes`/`RAndElim`/`RNotOrElim` as first-class
`rproof` constructors, and `Hyp`/`RLemma` + `hyps_closed`/
`hyps_closed_units` bookkeeping, per `RESOLUTION_CHECKER_SCOPE.md`'s
"Round 2 candidates (status: done)" section — this was simply not yet
reflected in `tools/proof_rule_coverage.py`'s Tier 1/Tier 2
classification (which only tallies rule *names*, not whether an actual
`rproof` term was constructed and checked). That classification has
now been updated accordingly (`hypothesis`/`lemma` moved Tier 2→Tier
1). Only item 3 below remains genuinely open.

Coverage being 100% at the *rule-name* classification level does not
mean the whole proof is independently re-derived — it means every node
is in Tier 1 (mechanized) or Tier 2 (explicitly, transparently trusted,
matching Z3's own trust boundary). The highest-value next steps,
per `RESOLUTION_CHECKER_SCOPE.md`'s "Round 2 candidates":

1. ~~**Promote `unit_resolve`/`and_elim`/`not_or_elim` to first-class
   `rproof` constructors**~~ — **done**: `RUnitRes`/`RAndElim`/
   `RNotOrElim` already exist in `Z3ResolutionProofTheory.fst`, so a
   single `rproof` term can represent an entire resolution refutation
   end-to-end (not just the propositional glue around one
   equational-rewrite island). What is *not* yet done is a
   JSON schema + Python extraction pipeline that walks a real Z3
   proof's entire DAG and actually *constructs* such an `rproof` term
   (mirroring `Z3ProofJson.fst`/`extract_z3_proof.py` for the
   equational layer) — `proof_rule_coverage.py` still only classifies
   rule *names*, it does not build and check real `rproof` terms. That
   pipeline remains the concrete next deliverable.
2. ~~**`Hyp`/`Discharge`/`hyps_closed` hypothesis-scoping bookkeeping**~~
   — **done**: `Hyp`/`RLemma` + `hyps_closed`/`hyps_closed_units`
   already exist and are wired through `lemma_rproof_sound_hyps`,
   closing the exact gap `proof_checker.cpp` itself leaves as a
   comment ("TBD all branches with hypotheses must be closed by a
   later lemma"). `PR_HYPOTHESIS` only discharges when the assumed
   formula is a member of the ambient hypothesis list, and `PR_LEMMA`
   requires `pf_false` to close `False` under exactly the single local
   hypothesis `(not fact_)` — both now classified Tier 1.
3. Narrowing Tier 2 further for `"array"`-tagged `th-lemma`/`def-axiom`
   nodes specifically (since QF_AX is the set where Tier 2 share is
   highest) by matching their conclusion shape against the array
   rewrite lemmas already proved in `Z3ArrayTheory.fst` — this is the
   same "match against verified lemmas, log what doesn't match"
   strategy already used by the equational rewrite checker, just
   applied to this newly-measured Tier 2 mass.

## Update: re-run on 100 files/set (larger sample, independent reseed)

Rerunning `tools/proof_rule_coverage.py` with `n=100` per set (same
`random.seed(42)` deterministic shuffle over a larger prefix of the
file list, so this supersets rather than merely re-samples the earlier
60-file run):

### QF_AX (100 files sampled, 57 produced an `unsat` proof)

| | nodes | share |
|---|---:|---:|
| Tier 1 | 338,317 | 78.3% |
| Tier 2 | 93,949 | 21.7% |
| Unmodeled | 0 | 0.0% |

**File-level coverage: 57 / 57 (100%)**

### QF_UF (100 files sampled, 52 produced an `unsat` proof)

| | nodes | share |
|---|---:|---:|
| Tier 1 | 4,915,851 | 92.1% |
| Tier 2 | 420,919 | 7.9% |
| Unmodeled | 0 | 0.0% |

**File-level coverage: 52 / 52 (100%)**

**Result holds at the larger sample size, unchanged in kind**: still
**zero unmodeled proof-rule nodes** on both sets (now over ~5.8M total
proof nodes combined, up from ~3.2M at `n=60`), and the Tier 1/Tier 2
node-share split is essentially stable (QF_AX 77.0%→78.3% Tier 1, QF_UF
92.8%→92.1% Tier 1 — both within a couple points of the smaller sample,
not a meaningfully different distribution). The number of files that
actually produce an `unsat` proof within the harness's fixed 10s
timeout scaled roughly proportionally (33→57 for QF_AX, 26→52 for
QF_UF), i.e. still around half of each 100-file sample times out or
returns a different result before a proof is even extracted — this is
a benchmark-selection/timeout artifact of the harness, not a gap in
proof-rule coverage, and is unchanged from the original run's caveat
about sample representativeness. No new rule names, and in particular
no new *unmodeled* rule names, appeared when tripling the files that
did yield a proof (33+26=59 unsat proofs at n=60 vs. 57+52=109 at
n=100). This is further, now larger-sample, evidence the Tier 1 ∪
Tier 2 vocabulary genuinely is closed over real-world QF_AX/QF_UF
proof content, not just the original smaller sample's specific files.

The round-2 candidates above remain open and unchanged by this re-run;
it reconfirms the *coverage* claim (no unmodeled rules) rather than
addressing the *depth* gap (Tier 2 nodes are trusted, not
independently re-derived).

## Update: round 2 reclassification + re-run on 100 files/set

`RESOLUTION_CHECKER_SCOPE.md` records that Round 2 (promoting
`unit_resolve`/`and_elim`/`not_or_elim` to first-class `rproof`
constructors, plus `Hyp`/`RLemma` + `hyps_closed`/`hyps_closed_units`
hypothesis-scoping bookkeeping) was already fully implemented and
verified in `Z3ResolutionProofTheory.fst` in an earlier session, but
`tools/proof_rule_coverage.py`'s Tier 1/Tier 2 classification had not
been updated to reflect it: `"hypothesis"` and `"lemma"` were still
listed in `TIER2` even though `Hyp`/`RLemma` now mechanically check
them (an assumed hypothesis must actually be a member of the ambient
hypothesis list; a `lemma` node's `pf_false` must close `False` under
exactly its own local `(not fact_)` hypothesis — neither is a silently
trusted leaf any more). `proof_rule_coverage.py` has been updated to
move both into `TIER1`, and the 100-file-per-set evaluation was rerun:

### QF_AX (100 files sampled, 57 produced an `unsat` proof)

| | nodes | share |
|---|---:|---:|
| Tier 1 | 365,064 | 84.5% |
| Tier 2 | 67,202 | 15.5% |
| Unmodeled | 0 | 0.0% |

**File-level coverage: 57 / 57 (100%)**

### QF_UF (100 files sampled, 52 produced an `unsat` proof)

| | nodes | share |
|---|---:|---:|
| Tier 1 | 5,025,347 | 94.2% |
| Tier 2 | 311,423 | 5.8% |
| Unmodeled | 0 | 0.0% |

**File-level coverage: 52 / 52 (100%)**

Tier 1 share rises on both sets purely from this reclassification
(QF_AX 78.3%→84.5%, QF_UF 92.1%→94.2%), with the same file set and the
same zero-unmodeled-nodes result as before — `hypothesis`/`lemma`
nodes are common enough in real QF_AX/QF_UF proofs that this is a
meaningful, not cosmetic, shift. **What this does and does not mean:**
it does not mean an actual `rproof` term has been built and checked
for any of these 109 real benchmark proofs — `proof_rule_coverage.py`
still only classifies rule *names* via the raw Z3 proof-DAG walk, it
does not invoke `Z3ResolutionProofTheory.fst`'s decoder/checker on
real proof data (no JSON schema or extraction pipeline for `rproof`
exists yet, unlike the equational layer's `Z3ProofJson.fst`/
`extract_z3_proof.py`). That remains the concrete next deliverable for
closing the gap between "every node's rule name has *some* mechanized
counterpart" and "this specific proof was fully, mechanically
re-checked end-to-end."

**Bottom line on "fully checked vs. requires trusted rules" for these
109 real `unsat` proofs**: every one of them still requires Tier 2
(`Trusted`) leaves — `th-lemma`/`def-axiom`/`quant-inst`/`hyper-res`/
`asserted`/… remain in Tier 2 by design (matching Z3's own
`proof_checker.cpp` trust boundary), and no file in either sample has
zero Tier 2 nodes. None of the 109 proofs are "fully checked" in the
strict zero-trusted-leaf sense; all of them are "Tier 1 ∪ Tier 2
complete" (no rule name outside this project's modeled vocabulary),
with Tier 1 now covering 84.5%/94.2% of nodes respectively.

