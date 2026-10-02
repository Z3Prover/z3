# Minimal cross-solver regression

`cvc5-split-f3-sat.smt2` is SAT over F3, uniquely at a = b = 1.
Its assertions are `(a + 2)(b + 1) = 0` and `b + 2 = 0`.

cvc5 `--ff-solver=split` returns incorrect UNSAT, while `--ff-solver=gb`
returns SAT. Reproduced on 1.3.4, 1.4.0, and main at
`72f647eb75c0241d82bc24ecf1f4092ff0f683f7` (macOS ARM64).
The 1.4.0 and main rechecks each use three fresh processes per backend.
Independent enumeration of all nine assignments confirms the witness.

Reduced from the public CAV 2024 artifact, https://zenodo.org/records/10917330,
member `experiments/benchmarks/smt2/small_field/craft/r_3_32_32_system13.smt2`.
The original SHA-256 is
`7664b9fa2577c47a8008e4ded3a004f0fecbb82f589cae6a39871c3fa6b555d3`.

The full local evidence is preserved under
`tests/finite_field/results/paper-artifacts/disagreements/<original hash>/`.
An upstream report is prepared but submission is pending GitHub authentication.
