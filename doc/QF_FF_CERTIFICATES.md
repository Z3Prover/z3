# Certificate contract for v2

This is a design contract, not implemented proof reconstruction. V1's dependency
sets identify input constraints used by a conflict; they do not justify the
algebra. Proof-producing QF_FF checks remain explicitly unsupported.

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
all be rejected by checker tests. The proof format and Lean reconstruction API
still need agreement with Blaster; this document does not freeze a serialized
format.

The public [FMCAD 2026 finite-field proof artifact](https://zenodo.org/records/20133205)
also advertises proof checking in Pacheck and Lean. It is a relevant reference
for the v2 design; its checker and proof format have not been evaluated or
integrated in this branch.

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
