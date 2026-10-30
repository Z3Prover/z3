# Verified bit-vector invertibility conditions

`Z3BvInvertibilityComplete.lemma_invertibility` proves, for **every positive
width**, every operator below, every relation below, and all width-fitting
parameters `s,t`:

```fstar
condition op r s t <==>
  (exists (x:bv n). Z3BvInvertibility.holds r (apply op s x) t)
```

All **160 same-width conditions** are proved in both directions. The theorem's
exhaustive matches cover the complete operator and relation types; there is no
width bound, admission, assumed invertibility rule, or unchecked fallback.

`Z3BvInvertibilityComplete.lemma_concat_invertibility` additionally proves
**20 mixed-width concatenation families**: both `concat x s` and `concat s x`,
with all ten relations and independently arbitrary positive widths for `x`
and `s`. Its target is any bit vector of the combined width. The conditions,
constructive witnesses, and verified target decomposition are defined in
`Z3BvInvertibilityConcat.fst`.

## Paper and source inventory

Ha Truong, Jordin Palmeri, Liam Secrist, Jacob Schuckman, Arjun Viswanathan,
and Yoni Zohar, **LLM-Assisted Formal Verification of Bit-vector Invertibility
Conditions in Rocq**, LPAR-26, EPiC Series in Computing 112, pp. 80-90.
[Paper](https://easychair.org/publications/paper/MjQR),
[DOI: 10.29007/xtl7](https://doi.org/10.29007/xtl7).

The condition inventory comes from
[`yoni206/invertibility`](https://github.com/yoni206/invertibility/tree/83bcf258bbd0d7ccc083ceb96ddba53973396847),
commit `83bcf258bbd0d7ccc083ceb96ddba53973396847`, specifically the
`verify-ic/check_<relation>_<operator>_65bit.smt2` definitions. Width-dependent
constants are parameterized by `n`, rather than kept at 65 bits. The seven
bounded shift disjunctions are represented recursively over shift amounts
`0..n`, with a proof that larger amounts add no outputs.

The paper's corrected conditions are taken from its
[LPAR Rocq artifact](https://github.com/HaTruong05/invCondProofs/tree/c91e27a181816c918a98a06d6c4c501641706d05),
commit `c91e27a181816c918a98a06d6c4c501641706d05`.
The F* proofs are independent proofs, not imported Rocq proof certificates.

The source directory also contains 40 concatenation samples:
`check_<relation>_bvconcat<0|1>_<1|65>_65bit.smt2`. These sample variable
widths 1 and 65, with the fixed operand at width 65. The 20 general
concatenation families cover both sampled widths, and all other positive
width pairs. Together with the 160 same-width families, this covers all
200 sampled 65-bit inventory files, not 200 distinct operator/relation families.

## Complete coverage

Every cell below is an arbitrary-width equivalence proof. `All` means all ten
relations: `=`, `!=`, `<u`, `>u`, `<=u`, `>=u`, `<s`, `>s`, `<=s`, `>=s`.

| Operator | Expression | Verified relations |
|---|---|---|
| Negate | `-x` | All |
| Complement | `~x` | All |
| Conjoin | `x & s` | All |
| Disjoin | `x \| s` | All |
| ShiftLeftValue | `x << s` | All |
| ShiftLeftAmount | `s << x` | All |
| ShiftRightValue | `x >> s` | All |
| ShiftRightAmount | `s >> x` | All |
| ArithmeticRightValue | `x >>a s` | All |
| ArithmeticRightAmount | `s >>a x` | All |
| Add | `x + s` | All |
| Multiply | `x * s` | All |
| Dividend | `x /u s` | All |
| Divisor | `s /u x` | All |
| RemainderValue | `x %u s` | All |
| RemainderDivisor | `s %u x` | All |
| Concatenation, variable high part | `concat x s` | All |
| Concatenation, variable low part | `concat s x` | All |

`Z3BvInvertibilityConditions.fst` contains the same-width executable conditions;
`Z3BvInvertibilityConcat.fst` contains the mixed-width conditions.
`Z3BvInvertibilityComplete.fst` dispatches each cell to its proof:

| Modules | Proof content |
|---|---|
| `Invertibility`, `Proofs` | Bijections, projections, shift saturation, zero and division endpoints |
| `Bits`, `Signed`, `Carry` | Signed bitwise extrema, prefix-inductive AND/OR sum, carry witnesses |
| `Arithmetic`, `Division`, `Dividend`, `Remainder` | Quotient/remainder bounds, attainable extrema, exact division images |
| `Shifts`, `Logical`, `Final` | Signed/unsigned shift extrema and reconstruction |
| `Factors`, `Multiply` | Power-of-two factorization, constructive odd inverses, modular multiplication image |
| `ConcatOrder`, `ConcatProofs` | Signed/unsigned lexicographic order, target decomposition, necessity and constructive sufficiency |

The suffixes `Proofs`, `Bits`, etc. abbreviate `Z3BvInvertibilityProofs`,
`Z3BvInvertibilityBits`, etc.; `Invertibility` means `Z3BvInvertibility`.

For concatenation, `ConcatProofs.lemma_invertibility` states the equivalence
with a target split into `tx` and `ts`, matching the source conditions.
`lemma_invertibility_value` and the complete-module entry point remove that
restriction using verified extraction and reconstruction. Signed comparisons
use signed order on the high part and unsigned order on the low part.
The proofs include width-one and asymmetric-width cases without exceptions.

## Width-one corrections

Three original `s /u x` conditions need special handling at width one:

| Relation | Correct width-one condition |
|---|---|
| `!=` | `(s & t) = 0` |
| `>s` | `s >s t` |
| `>=s` | `s >=s t` |

The original conditions give false positives at `(s,t)=(1,1)` for `!=` and
`>s`, and at `(1,0)` for `>=s`. The specification uses the corrected conditions;
the complete theorem includes width one.

## Semantics and trust boundary

Bit vectors are refined mathematical integers in `[0,2^n)`, using the existing
`FStar.UInt` library. Arithmetic wraps modulo `2^n`. Division by zero returns
all ones; remainder by zero returns the dividend. Signed order interprets the
high bit as a two's-complement sign. Shifts at or above the width saturate.

This work also fixes two pre-existing errors in the F* semantics: arithmetic
right shift must zero-fill nonnegative inputs, and sign extension must
zero-extend nonnegative inputs. Negative inputs retain sign-filling behavior.
No native Z3 C++ semantics are changed. The new proofs establish large-shift
behavior and signed-value preservation under sign extension.

Verification trusts F*, its standard library, and its SMT discharge through the
explicitly selected Z3 executable. These proofs do not use native solver calls
as assumptions. The independent native differential tests additionally exercise
the extraction/runtime boundary; they are tests, not the all-width proofs.

## Reproducing verification and executable tests

The runner uses a **fresh cache**, treats every F* warning as an error, and
checks one module per invocation. It verifies all 21 modules, including the
corrected foundation and both complete theorems. It then extracts the four
computational modules and compiles the native tests with strict OCaml warnings.

Use F* with its standard library, Python 3, and Z3 built and installed from
this checkout. Native tests additionally require OCaml, `ocamlfind`, Zarith,
and the official OCaml Z3 bindings installed from this checkout. The existing
`tools/build_ocaml_checker.ps1` documents and prepares that native installation.

Windows with WSL, from the repository root:

```powershell
python fstar\tools\test_bv_invertibility.py `
  --fstar C:\fstar\fstar\bin\fstar.exe `
  --z3 C:\z3\build\install\bin\z3.exe `
  --wsl --opam-switch fstar53 `
  --ocaml-install '~/z3-native-ffi-build/install' `
  --output-dir C:\z3\build\invertibility-test-results
```

On Linux, use the same runner with native executable paths and installation
prefix, omitting `--wsl`. An already active OCaml environment does not need
`--opam-switch`. `--verify-only` skips extraction/native tests and does not
require `--ocaml-install`. `--max-width` controls only the executable tests,
not the theorem: its default is 8.

The native suite exhaustively checks all 160 conditions at widths 1-8:
**13,980,800 condition instances**. It compares all operator operands with
native Z3 at widths 1-4 and checks boundary operands at widths
1, 2, 17, 32, 64, 65, and 257, including sign extension.

It additionally checks **204,000 mixed-width condition and witness instances**
exhaustively for independently chosen operand widths 1-4, comparing every
concatenation with native Z3 and checking both target-extraction directions.
Native signed/unsigned relation tests cover asymmetric width pairs including
1/65, 65/1, 17/32, 32/17, 64/65, 65/64, 1/257, and 257/1, as well as
257/257. These exercise positive and negative conditions and their canonical
witnesses against native Z3.

The complete theorem and its proof dependencies are also registered in
verification order in `tools/checker_modules.json`, so the existing checker
build's `-RunTests` path strictly verifies every module, not only the dispatcher.
