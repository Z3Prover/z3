# QF_FF certificates: first v2 milestone and remaining contract

The first v2 milestone implements standalone polynomial refutation certificates,
including arbitrary-precision prime fields. It uses an explicit reconstruction
command; normal solving and `get-proof` retain their existing behavior. The
optimized QF_FF solver does not yet record a complete proof of its own execution.
V1 dependency sets still identify premises only, and cannot replace a derivation.

The second milestone adds the [original-input Alethe/PAC pipeline](QF_FF_PROOF_PIPELINE.md),
including checked disequality witnesses and real Carcara/FFPacheck runs. The
first-milestone format and shell command described below remain supported.
The [third milestone](QF_FF_BOOLEAN_PROOFS.md) adds checked Boolean resolution,
field/Boolean ITEs and an iterative shared-term front end to that pipeline.

## Implemented: polynomial refutations from original equations

Use `(ff-certify)` instead of `(check-sat)` for a single-field conjunction of
positive equations when producing a standalone certificate file. The
shell command reads the current assertions directly, expands field arithmetic,
and runs bounded scalar basis reconstruction. It does not use `ff-simplify`,
model sampling, native equality-engine facts, root reasoning or a previous SAT
answer. A successful object proves **1 belongs to the ideal of the original
polynomial equations**. Lack of such a derivation reports
`(ff-certificate-unavailable no-polynomial-refutation)`, never SAT. Exhaustion
reports `(ff-certificate-unavailable budget)`. Unsupported input reports an
explicit error. This command does not alter assertions or the solver result.

The initial interface is shell-only. The reusable C++ `ff::certify` API takes
polynomial equations; no C/Python solver API or Z3 native proof rule is added.
Its output object is replaced only on success, including after cancellation.
The ordinary solver has no new recording branch or per-polynomial proof data.

```sh
build-ff-cmake/z3 z3test/regressions/finite_field/fixtures/certificates/large-prime.smt2 > /tmp/large.ffcert
python3 scripts/ff_certificate.py z3test/regressions/finite_field/fixtures/certificates/large-prime.smt2 \
  /tmp/large.ffcert --export-alethe /tmp/large.alethe
python3 scripts/ff_certificate.py z3test/regressions/finite_field/fixtures/certificates/large-prime.smt2 \
  /tmp/large.alethe --alethe
```

The Python checker uses only the standard library and integer arithmetic. It
independently parses the original SMT-LIB equations, checks their normalization,
then evaluates the derivation DAG. It does not import Z3 or rerun Groebner search.
The standalone input profile supports field constants, nullary sort aliases and
function definitions, simultaneous `let`, `:named`, conjunctions and field
addition/multiplication/negation/bitsum. It rejects push/pop/reset, nonconstant
UFs, disequalities, general Boolean structure and mixed-field equations. To
check a lemma from a larger computation, supply its exact assumptions as a
standalone problem; merely checking that lemma does not certify the larger run.

Default producer bounds are 2M arithmetic operations, 4096 terms per polynomial,
100K DAG nodes, 16 MiB estimated DAG storage, 256 basis rows, 4096 input equations
and a ten-second command timeout. Set `:max_steps`, `:max_terms`, `:max_nodes`
and `:timeout` on `ff-certify`; the node and DAG-storage ceilings remain absolute.
The profile bounds moduli to 4096 bits and monomials to degree 1024. The checker
has separate work/size limits and can refuse an otherwise valid large proof.
The producer's storage estimate is not a total-process memory bound.

### Evidence DAG version 1

The serialized `ff-certificate` object has exactly `:version`, `:modulus`,
`:variables`, `:inputs`, `:nodes` and `:root`. Input polynomials are lists of
`(coefficient variable-id...)` terms, with nonzero canonical coefficients and
sorted variable multisets. Variable names must resolve to declarations in the
original problem, and every supplied input must equal the independent
normalization of its corresponding original equation, including conjunction
projection. IDs are zero-based list indices.

- `(input i)` denotes the normalized left side minus right side of equation i.
- `(mul j c (v...))` denotes node j multiplied by the scalar c and monomial v....
- `(add j k)` denotes the polynomial sum of nodes j and k.

All node references must point backward. Each derived polynomial is asserted
equal to zero. The selected root must be exactly the constant polynomial 1.
Scaling, reduction and S-polynomials record their actual multipliers; moving
an irreducible term to a remainder is bookkeeping and introduces no assumption.
Subderivations are shared by ID; expanded combinations of the original inputs
are never materialized by the producer. Search pair ordering and skipped pairs
are outside the trust boundary: only the explicit contradiction is checked.

This slice uses ring identities only. Checking a refutation modulo p >= 2 does
not require a primality certificate: a checked identity 1 = sum(q_i*f_i) is
already contradictory over Z/pZ. Future root/no-zero-divisor/Frobenius rules
need the stronger field assumptions listed below.

### Alethe extension, not stock-checker compatibility

The export uses Alethe's `assume` and `step` syntax with four explicitly custom
`ff-poly-v1` rules. All equations and multiplier terms have the same field sort.
No `hole`, trusted step or unasserted assumption is accepted by our checker.

| Rule | Premises / arguments | Checked conclusion |
| --- | --- | --- |
| `ff_poly_input` | One original assertion; zero-based conjunct index | Normalize the selected equality to P = 0, expanding supported lets/definitions |
| `ff_poly_add` | P = 0 and Q = 0; no arguments | R = 0 with R = P + Q modulo p |
| `ff_poly_mul` | P = 0; multiplier term M | R = 0 with R = M*P modulo p |
| `ff_poly_contra` | 1 = 0; no arguments | Empty clause |

Each algebraic conclusion is printed explicitly. Alethe output can therefore
be larger than the internal DAG. The exporter first checks the DAG, and the CLI
checks the exported Alethe derivation through a separate rule-replay path before
writing it. `--alethe` also checks an existing extension proof directly against
the original problem. The checker requires an explicit final empty clause.

This is **an experimental extension**, not a claim of compatibility with
unmodified Carcara, SMTCoq or Isabelle. The [Alethe specification](https://verit.loria.fr/documentation/alethe-spec.pdf)
distinguishes the language from its proof rules. [cvc5's current Alethe documentation](https://cvc5.github.io/docs-ci/docs-main/proofs/output_alethe.html)
does not list finite fields among its supported theories (checked 2026-09-24).
These rules need agreement and implementation in the target consumer before
interoperability can be claimed. The FMCAD 2026 artifact already extends Alethe/Carcara
for finite fields through a PAC backend, despite the general cvc5 documentation
omitting FF. The separate `ff_proof_pipeline.py` exporter now targets that
interface and has been tested with pinned public companion checkers; see
[QF_FF_PROOF_PIPELINE.md](QF_FF_PROOF_PIPELINE.md) for its mandatory independent
input binding, checker patch, scope and measurements. The legacy rules in this
section are retained for regression compatibility.

A Z3-native certificate **file format** is not required for this export. Native
proof objects or another complete Boolean/equality proof interface will be
needed to compose field lemmas into a checked mixed-theory Z3 proof. The DAG
is deliberately independent of either serialization. The next integration
step is to attach it to an FF theory lemma with exact premises, then certify
preprocessing, disequality witnesses and finite-field root reasoning.

For validation and bounded cost measurements, see
[QF_FF_CERTIFICATES_MILESTONE1.md](https://github.com/RSoulatIOHK/z3/blob/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/doc/QF_FF_CERTIFICATES_MILESTONE1.md).
The remainder of this document is the contract for full v2, not a claim that
these additional obligations are implemented.

## Boundary with Blaster

The general simplifier supports constant folding, zero/one identities, double
negation, combining like terms, additive cancellation in equalities, and
nonzero constant coefficient elimination. `ff-simplify` additionally propagates
constants and acyclic wire definitions across assertions while preserving model
conversion, and recovers zero/nonzero-test indicators from both defining
constraints. None of these
field-specific steps currently provides a certificate reconstructible in Lean.
Polynomial normalization and equality elimination also occur inside the solver.

Reconstructing a result in Lean will require both the Boolean proof and field
justifications. A list of assumptions sufficient for a conflict cannot replace
these justifications. Any future simplification API should return either a
checkable equality proof or an explicit obligation with its premises.

## Objects and obligations

Use stable identifiers for fields, variables, input literals, and derived
polynomials. A polynomial is a sparse list of canonical modular coefficients
and monomials with sorted variable identifiers. Every referenced object carries
its field identifier; mixed-field derivations are rejected by the checker.

| Transformation | Required justification |
| --- | --- |
| Modulus and constants | Prime modulus certificate, or an explicit primality assumption; integer reduction modulo that modulus |
| Constant and symbolic rewriting | Equality between original and replacement terms, with field axioms and any side conditions |
| Normalization | Checked correspondence between the input expression DAG and its sparse polynomial |
| Linear combination / basis reduction | Polynomial multipliers whose combination of premise equations equals the derived equation |
| Variable elimination | A nonzero pivot, its inverse, and the substitution identity; dependencies and reconstruction map |
| Compact polynomial encoding | Fresh internal field variables with acyclic defining equations; checked correspondence to the original expression DAG; eliminate these definitions from exported conflicts and reconstruct original models |
| Acyclic circuit elimination | Definition equalities, an acyclic dependency order, and a model reconstruction map; shared DAG normalization identities |
| Zero/nonzero-test recovery | Both the annihilation and inverse-witness premises; case split on the tested expression being zero |
| Bounded bit enumeration | Booleanity of every remaining free variable (or characteristic two), and exhaustive coverage of all assignments for UNSAT |
| Disequality witness | Fresh variable declaration and `f != 0` iff an inverse witness satisfies `f*t = 1` |
| Recognized factors and square roots | Checked normalization from the original guarded equality; no-zero-divisors justification for product splits and A²-B²=(A-B)(A+B); r²=-c/a with a nonzero pivot for direct quadratic roots; zero/characteristic-two deduplication without division by two |
| Root reasoning | Field-membership argument using `X^p-X`, gcd identities, and complete factorization or exhaustive roots for UNSAT branching |
| Booleanity | Derivation of `b*(b-1)=0`, hence `b` is 0 or 1 in a field |
| Binary decomposition | Booleanity for every bit, exact coefficients, explicit integer bound excluding modular wraparound, and the equality of sums |
| Boolean search | Resolution steps, with each theory clause linked to a checked field conflict |
| BV fallback | Range-constrained equivalence of each translation step, including widened arithmetic before modular reduction |
| Native theory combination | Checked algebraic conflict under its exact SMT equality/disequality premises; equality-engine justifications; acyclic wire substitutions and model extension; ordinary SAT case splits for candidate-model shared equalities, never treating a sampled equality as an unconditional theorem |
| Combination fallback | Fresh per-field encode/decode functions, canonical range bounds, and decode(encode(t))=t; congruence transports equalities in both directions, preserving finite cardinality and original UF/array/datatype signatures |

SAT output needs a total field assignment checked against the original formula.
Model reconstruction through substitutions and eliminated ITEs must preserve
the meaning of original variables. This can be checked independently of search.

## Recording strategy

Keep proof recording optional so ordinary solving does not accumulate polynomial
multipliers. Record normalization, scaled addition, multiplication, substitution,
and reduction at the algebra boundary. Derived bit constraints additionally need
their Booleanity and no-wrap premises; ideal-combination provenance alone is
insufficient for this integer interpretation step.

Sampling may establish SAT only after witness verification. Failed samples must
never produce a contradiction certificate. Budget exhaustion likewise produces
no UNSAT proof. A standalone checker should verify the trace without rerunning
Gröbner search or trusting the SAT engine.

Before v2 is accepted, corrupt coefficients, missing premises, invalid inverses,
cross-field references, incomplete root lists, and omitted no-wrap guards must
all be rejected by checker tests. The full-v2 proof format and Lean reconstruction API
still need agreement with Blaster; the experimental profile above does not freeze
the eventual full-v2 serialization.

The public [FMCAD 2026 finite-field proof artifact](https://zenodo.org/records/20133205)
provides an Alethe/Carcara/FFPacheck pipeline and a separate Lean-SMT/CPC
pipeline. Its published results and our fresh 390-input certificate coverage
screen are recorded in [QF_FF_FMCAD_PROOF_BENCHMARK.md](https://github.com/RSoulatIOHK/z3/blob/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/doc/QF_FF_FMCAD_PROOF_BENCHMARK.md).
That screen is historical: the [second milestone](QF_FF_PROOF_PIPELINE.md) now
checks 135/390 inputs with the public companion Carcara/FFPacheck sources. The
artifact image's exact binaries and the CPC/Lean path remain unevaluated.

Round 7 keeps coefficient normalization, geobucket reductions and sparse matrix
operations at the same ideal-combination boundary. A certificate recorder must
retain each reducer multiplier even when accumulator terms cancel. Sugar degree,
divisibility masks, pair scheduling and substitution-cost estimates are search
heuristics, not proof premises. Pair criteria need not certify search completeness
when checking an explicit contradiction identity; an untrusted skipped pair can
never substitute for that identity. The compact-encoding retry restarts from the
original goal with fresh definitional variables and retains the failed attempt's
resource charges. Failed attempts contribute no logical justification.

Round 8 separates quotient minimal-polynomial completion from witness probing.
For a derived univariate relation, a future recorder must retain both the
normal-form reductions of successive powers and the linear-dependence row
operations, yielding an explicit combination of original equations. The
zero-dimensionality guard and degree cap control search; the checked identity
justifies the resulting relation independently of those heuristics.

Reduced Frobenius facts additionally require the prime-field axiom `x^p-x=0`.
Record the repeated-squaring congruences and reductions against the input basis,
then check that their remainder is zero over the prime field using that axiom.
These facts need not preserve solutions over the algebraic closure, so an
ordinary ideal-combination trace without the field axiom is insufficient.
Conflict dependencies alone do not record this distinction. Adaptive symbolic
matrix admission changes resource policy only; its reducer multiples and row
operations retain the existing ideal-combination certificate obligations.
