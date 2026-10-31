"""End-to-end direct SMT-LIB tests; no Python Z3 binding or proof transport."""
import os
import re
from pathlib import Path
import subprocess
import queue
import tempfile
import threading
import unittest


NEGATIVE_NNF_CASES = (
    ("existential", "(declare-fun p (Int) Bool)"
     "(assert (not (exists ((x Int)) (p x))))(assert (p 0))"),
    ("conjunction", "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)"
     "(assert (not (exists ((x Int)) (and (p x) (q x)))))"
     "(assert (p 0))(assert (q 0))"),
    ("disjunction", "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)"
     "(assert (not (exists ((x Int)) (or (p x) (q x)))))(assert (p 0))"),
    ("mixed-sort", "(declare-fun p (Int Real) Bool)"
     "(assert (not (exists ((x Int) (y Real)) (p x y))))(assert (p 3 4.5))"),
    ("boolean-context", "(declare-fun p (Int) Bool)(declare-const q Bool)"
     "(assert (not (and (exists ((x Int)) (p x)) q)))(assert (p 0))(assert q)"),
    ("implication", "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)"
     "(assert (not (exists ((x Int)) (=> (p x) (q x)))))(assert (not (p 0)))"),
    ("xor", "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)"
     "(assert (not (exists ((x Int)) (xor (p x) (q x)))))"
     "(assert (p 0))(assert (not (q 0)))"),
    ("ite", "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)"
     "(declare-fun r (Int) Bool)"
     "(assert (not (exists ((x Int)) (ite (p x) (q x) (r x)))))"
     "(assert (p 0))(assert (q 0))"),
)

# The nnf tactic Skolemizes a block even when none of its variables occurs in the body. Only
# `under-binder` has an ambient bound variable (a de Bruijn index); the others use free constants.
UNUSED_SKOLEM_CASES = (
    ("constant-false", "(assert (exists ((a Int)) false))(assert (forall ((b Int)) false))"
     "(check-sat-using nnf)"),
    ("only-existential", "(assert (exists ((a Int)) false))(check-sat-using nnf)"),
    ("free-constant", "(declare-const p Bool)(assert (exists ((a Int)) p))(assert (not p))"
     "(check-sat-using (then nnf smt))"),
    ("multi-binder", "(declare-const p Bool)(assert (exists ((a Int) (b Real)) p))"
     "(assert (not p))(check-sat-using (then nnf smt))"),
    ("ground-application", "(declare-fun p (Int) Bool)(assert (exists ((a Int)) (p 0)))"
     "(assert (not (p 0)))(check-sat-using (then nnf smt))"),
    ("negative-universal", "(declare-const p Bool)(assert (not (forall ((a Int)) p)))"
     "(assert p)(check-sat-using (then nnf smt))"),
    ("under-binder", "(declare-fun p (Int) Bool)"
     "(assert (forall ((z Int)) (exists ((a Int)) (p z))))(assert (not (p 0)))"
     "(check-sat-using (then nnf smt))"),
)

# The arithmetic rewriter factors p REL 0 when a term divides every monomial of p
# (factor_le_ge_eq). These are the first queries of z3test nl12, nl49, nl33, and nl57.
FACTOR_SIGN_CASES = (
    ("int-le", "(declare-const x1 Int)(declare-const x2 Int)(declare-const x3 Int)"
     "(assert (and (> (+ (* x1 x2) x3) 0) (<= x1 (- 1)) (>= x1 (- 1)) (= x2 x3)))"),
    ("int-eq", "(declare-const x1 Int)(declare-const x2 Int)(declare-const x3 Int)"
     "(declare-const x4 Int)(declare-const x5 Int)"
     "(assert (and (<= x4 x5) (<= x5 x4) (= x2 (+ x3 x5))"
     " (not (= (* x1 x2) (+ (* x1 x3) (* x1 x4))))))"),
    ("real-ge", "(declare-const x Real)(assert (and (< 1.0 x) (not (< x (* x x)))))"),
    ("real-lt", "(declare-const x Real)(declare-const y Real)"
     "(assert (and (<= 0.0 x) (<= (- 1.0) y) (< (+ (* x y) x) 0.0)))"),
)

# The arithmetic rewriter lifts a conditional with a numeral branch out of a comparison
# with a numeral (mk_le_ge_eq_core), also after moving a numeral addend across
# (1 + (ite c 0 -1) >= 1). real-guarded-division is z3test z3.12; the shapes of
# both-numerals and shifted-numerals occur in z3test issue-963 and string6.
ITE_COMPARISON_CASES = (
    ("real-guarded-division",
     "(define-fun mydiv ((x Real) (y Real)) Real (if (not (= y 0.0)) (/ x y) 0.0))"
     "(declare-const a Real)(declare-const b Real)"
     "(assert (>= (mydiv a b) 1.0))(assert (= b 0.0))"),
    ("int-then-false", "(declare-const c Bool)(declare-const x Int)"
     "(assert (>= (ite c 0 x) 1))(assert c)"),
    ("int-else-false", "(declare-const c Bool)(declare-const x Int)"
     "(assert (>= (ite c x 0) 1))(assert (not c))"),
    ("int-le-then-true", "(declare-const c Bool)(declare-const x Int)"
     "(assert (<= (ite c 1 x) 2))(assert (not (<= x 2)))(assert (not c))"),
    ("real-le-then-true", "(declare-const c Bool)(declare-const x Real)"
     "(assert (<= (ite c 1.0 x) 2.0))(assert (not c))(assert (> x 2.0))"),
    ("int-shifted", "(declare-const c Bool)(declare-const x Int)"
     "(assert (>= (+ 1 (ite c 0 x)) 0))(assert (not c))(assert (< x (- 1)))"),
    ("both-numerals", "(declare-sort U 0)(declare-const u U)(declare-const v U)"
     "(assert (>= (ite (= u v) 1 (- 1)) 0))(assert (not (= u v)))"),
    ("shifted-numerals", "(declare-sort U 0)(declare-const u U)(declare-const v U)"
     "(assert (>= (+ 1 (ite (= u v) 0 (- 1))) 1))(assert (not (= u v)))"),
)

# The bit-vector rewriter moves an extraction into a sum or product of the low bits and into
# both branches of a conditional (mk_extract), composing an extraction of an extraction. The
# sum of a numeral and a conditional is the shape of z3test 6079-8.
BV_EXTRACT_CASES = (
    ("add-low", "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"
     "(assert (not (= ((_ extract 3 0) (bvadd x y))"
     " (bvadd ((_ extract 3 0) x) ((_ extract 3 0) y)))))"),
    ("mul-low", "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"
     "(assert (not (= ((_ extract 3 0) (bvmul x y))"
     " (bvmul ((_ extract 3 0) x) ((_ extract 3 0) y)))))"),
    ("add-ternary", "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"
     "(declare-const z (_ BitVec 8))(assert (not (= ((_ extract 2 0) (bvadd x y z))"
     " (bvadd ((_ extract 2 0) x) ((_ extract 2 0) y) ((_ extract 2 0) z)))))"),
    ("add-numeral-ite", "(declare-const c Bool)(declare-const k (_ BitVec 7))"
     "(assert (not (= ((_ extract 4 0) (bvadd #b0000001 (ite c k #b0000000)))"
     " (bvadd #b00001 (ite c ((_ extract 4 0) k) #b00000)))))"),
    ("mul-composed", "(declare-const u (_ BitVec 16))(declare-const x (_ BitVec 8))"
     "(assert (not (= ((_ extract 3 0) (bvmul ((_ extract 11 4) u) x))"
     " (bvmul ((_ extract 7 4) u) ((_ extract 3 0) x)))))"),
    ("ite-composed", "(declare-const p Bool)(declare-const u (_ BitVec 16))"
     "(declare-const x (_ BitVec 8))"
     "(assert (not (= ((_ extract 1 1) (ite p ((_ extract 9 2) u) x))"
     " (ite p ((_ extract 3 3) u) ((_ extract 1 1) x)))))"),
    ("ite-composed-66", "(declare-const m (_ BitVec 66))(declare-const n (_ BitVec 66))"
     "(declare-const w (_ BitVec 80))"
     "(assert (not (= ((_ extract 6 0) (ite (= m n) ((_ extract 65 0) w) m))"
     " (ite (= m n) ((_ extract 6 0) w) ((_ extract 6 0) m)))))"),
)

# An extraction of a concatenation (mk_extract) is the bits of the low argument, of the high
# argument, or a concatenation of the bits of both, with extractions of extractions composed.
# The last three are the shapes of z3test 6079-8.
BV_EXTRACT_CONCAT_CASES = (
    ("low", "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"
     "(assert (not (= ((_ extract 5 2) (concat x y)) ((_ extract 5 2) y))))"),
    ("high", "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"
     "(assert (not (= ((_ extract 14 9) (concat x y)) ((_ extract 6 1) x))))"),
    ("across", "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"
     "(assert (not (= ((_ extract 9 4) (concat x y))"
     " (concat ((_ extract 1 0) x) ((_ extract 7 4) y)))))"),
    ("high-composed", "(declare-const u (_ BitVec 16))(declare-const b (_ BitVec 1))"
     "(assert (not (= ((_ extract 14 14) (concat ((_ extract 15 2) u) b)) ((_ extract 15 15) u))))"),
    ("across-composed", "(declare-const u (_ BitVec 16))(declare-const b (_ BitVec 1))"
     "(assert (not (= ((_ extract 2 0) (concat ((_ extract 7 2) u) b))"
     " (concat ((_ extract 3 2) u) b))))"),
    ("across-numeral-ite", "(declare-const p Bool)(declare-const x (_ BitVec 8))"
     "(declare-const y (_ BitVec 8))"
     "(assert (not (= ((_ extract 8 1) (concat #b0 (ite p x y)))"
     " (concat #b0 ((_ extract 7 1) (ite p x y))))))"),
)

PULL_QUANT_CASES = (
    ("nested-exists", "(declare-fun p (Int Int) Bool)"
     "(assert (not (exists ((x Int)) (exists ((y Int)) (p x y)))))"
     "(assert (p 0 1))"),
    ("nested-forall", "(declare-fun p (Int Int) Bool)"
     "(assert (forall ((x Int)) (forall ((y Int)) (p x y))))"
     "(assert (not (p 0 1)))"),
    ("nested-mixed-sort", "(declare-fun p (Int Real) Bool)"
     "(assert (not (exists ((x Int)) (exists ((y Real)) (p x y)))))"
     "(assert (p 0 1.5))"),
    ("three-blocks", "(declare-fun p (Int Real Int) Bool)"
     "(assert (not (exists ((x Int)) (exists ((y Real))"
     "  (exists ((z Int)) (p x y z))))))"
     "(assert (p 0 1.5 2))"),
)

RULE_EXTENSION_CASES = (
    ("unused-binders", "(declare-fun p (Int) Bool)"
     "(assert (forall ((x Int) (unused Real)) (p x)))(assert (not (p 0)))"),
    ("push-forall", "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)"
     "(assert (forall ((x Int)) (and (p x) (q x))))(assert (not (p 0)))"),
    ("der-forall", "(declare-fun p (Int) Bool)"
     "(assert (forall ((x Int)) (or (not (= x 3)) (p x))))(assert (not (p 3)))"),
    ("der-exists", "(declare-fun p (Int) Bool)"
     "(assert (exists ((x Int)) (and (= x 3) (p x))))(assert (not (p 3)))"),
    ("lambda-constant", "(assert (not (= ((as const (Array Int Int)) 3)"
     " (lambda ((x Int)) 3))))"),
    ("lambda-beta", "(assert (not (= (select (lambda ((x Int)) (+ x 1)) 5) 6)))"),
    ("constant-read", "(assert (not (= (select ((as const (Array Int Int)) 3) 5) 3)))"),
    ("datatype-injectivity", "(declare-datatype T ((C (field Int)) (D (other Int))))"
     "(declare-const a Int)(declare-const b Int)"
     "(assert (= (C a) (C b)))(assert (not (= a b)))"),
    ("datatype-selector", "(declare-datatype T ((C (field Int))))"
     "(declare-const a Int)(assert (not (= (field (C a)) a)))"),
    ("bv-idempotence", "(declare-const v (_ BitVec 8))"
     "(assert (not (= (bvand v v) v)))"),
    ("bv-wrap", "(assert (not (= (bvadd #xff #x01) #x00)))"),
)

# Rewrite steps of the Pulse QF_FF certificates (z3test generator, seed 40244844124).
# Their proofs contain only `rewrite` steps decided by polynomial arithmetic modulo p, or by
# comparing an ite with a numeral.
def finite_field(prime, assertion):
    return (f"(set-logic QF_FF)(define-sort F () (_ FiniteField {prime}))"
            f"(declare-const x F)(declare-const y F)(assert {assertion})")


FINITE_FIELD_CASES = (
    ("ff-17-bitsum-folding", finite_field(17,
     "(and (= (ff.mul (ff.bitsum x (as ff2 F)) (ff.bitsum (as ff-3 F) x))"
     " (ff.bitsum (ff.mul x x) (ff.bitsum x y)))"
     " (= (ff.bitsum (as ff24 F) (as ff19 F)) (as ff19 F)))")),
    ("ff-17-cancellation", finite_field(17,
     "(and (= (ff.bitsum x (ff.mul y y))"
     " (ff.bitsum (ff.mul x (as ff24 F)) (ff.bitsum x (as ff31 F))))"
     " (= (ff.neg (ff.add y (as ff5 F))) (ff.neg y)))")),
    ("ff-2-numeral-disequality", finite_field(2,
     "(or (= (as ff3 F) (as ff0 F)) (not (= x x)))")),
    ("ff-5-negative-numerals", finite_field(5,
     "(and (= (ff.mul (as ff-2 F) (ff.add (as ff3 F) (as ff8 F))) (as ff4 F))"
     " (= (ff.bitsum y (ff.neg y)) (ff.bitsum (ff.bitsum y x) (ff.neg x))))")),
    ("ff-5-conditional-atom", finite_field(5,
     "(and (= (ff.neg (ff.mul (as ff5 F) x)) y)"
     " (= (ite (= x y) (as ff1 F) (ff.neg y)) x))")),
    ("ff-5-numeral-square", finite_field(5,
     "(and (= (ff.mul y y) (ff.bitsum (as ff1 F) (ff.mul (as ff-7 F) (as ff-6 F))))"
     " (= y (ff.neg (as ff4 F))))")),
    ("ff-5-double-negation", finite_field(5,
     "(and (not (= (ff.neg (ff.neg (as ff1 F))) (as ff-4 F)))"
     " (not (= (ite (= x y) (ite (= x y) y x) (ff.add y y))"
     " (ff.mul (ff.neg y) (ff.bitsum (as ff-8 F) x)))))")),
    ("ff-7-negated-product", finite_field(7,
     "(and (= (ff.mul y (ff.neg (as ff0 F))) (ff.neg (ff.neg x)))"
     " (= (as ff5 F) (ff.bitsum (as ff6 F) (ff.bitsum x (as ff8 F)))))")),
    ("ff-7-zero-product", finite_field(7,
     "(and (= (ff.mul (ff.mul y y) x) (ff.add (ff.add x x) (ff.bitsum y x)))"
     " (= (ff.mul (ff.add (as ff7 F) y) (ff.mul y (as ff7 F))) (as ff-10 F)))")),
    ("ff-7-rescaled-equation", finite_field(7,
     "(and (= (ff.mul (ite (= x y) (as ff-4 F) y) (ff.add x x))"
     " (ff.add (ff.neg (as ff-7 F)) (ff.bitsum x (as ff11 F))))"
     " (= x (ff.mul (ff.neg x) (ff.bitsum (as ff7 F) (as ff-3 F)))))")),
    # An ite compared with a numeral (field-3/case-02, field-7/case-01): a branch that differs
    # from the numeral by a nonzero constant is dropped and the condition selects the other.
    ("ff-3-ite-equal-numeral", finite_field(3,
     "(and (= (ite (= x y) (ff.neg (as ff1 F)) (ff.bitsum y y)) (as ff1 F))"
     " (= y (ite (= x y) (ff.add x y) (ff.mul (as ff5 F) y))))")),
    ("ff-7-ite-equal-numeral", finite_field(7,
     "(and (= (ff.bitsum (as ff2 F) (ff.neg y)) (ff.neg (ff.bitsum y y)))"
     " (= (ite (= x y) (ff.neg (as ff9 F)) (as ff-13 F)) (as ff-4 F)))")),
)
RULE_EXTENSION_CASES += FINITE_FIELD_CASES

# The remaining Pulse QF_FF certificates, verbatim: their `th-lemma` steps are decided by
# evaluating the clause under every assignment of residues to its leaves (at most 4096).
FINITE_FIELD_THEORY_LEMMA_CASES = (
    ("ff-17-case-02", finite_field(17,
     "(and (= (ff.add (ff.bitsum x (as ff19 F)) (as ff-26 F)) (ff.add (ff.mul (as ff-11 F) x) y))"
     " (= (ite (= x y) (ff.mul x y) (ff.bitsum y y)) (ff.mul x (ite (= x y) (as ff-6 F) x))))")),
    ("ff-17-case-03", finite_field(17,
     "(and (= (as ff-23 F) (ff.bitsum (ff.neg y) (ff.add x x)))"
     " (= (ff.bitsum (ite (= x y) y x) (ff.neg (as ff-16 F))) (ff.mul (ff.add x (as ff6 F)) (ff.add x y))))")),
    ("ff-17-case-05", finite_field(17,
     "(and (= x (as ff29 F)) (= (ff.mul (ff.add y x) (ff.mul y x)) (as ff25 F)))")),
    ("ff-2-case-02", finite_field(2,
     "(and (not (= y (ff.mul (ff.add (as ff0 F) x) (ff.bitsum y x))))"
     " (= (ff.bitsum (ff.mul x y) (ff.bitsum y y)) y))")),
    ("ff-2-case-03", finite_field(2,
     "(and (not (= (ff.mul (ff.mul x x) (as ff-3 F)) (ff.neg (as ff2 F))))"
     " (= (ff.mul x (ff.bitsum x y)) (ff.mul y (ff.mul y (as ff-4 F)))))")),
    ("ff-2-case-04", finite_field(2,
     "(and (= (ite (= x y) (as ff3 F) (ff.mul x y)) (ff.neg (ff.mul x x)))"
     " (= y (ff.mul (as ff3 F) (as ff2 F))))")),
    ("ff-2-case-05", finite_field(2,
     "(and (= (ff.add (ff.mul x (as ff2 F)) (ff.add y (as ff2 F))) (ff.bitsum (ff.add y y) (ff.bitsum y (as ff2 F))))"
     " (not (= (ff.mul x x) (ff.bitsum (ff.bitsum x y) (ff.add y x)))))")),
    ("ff-3-case-03", finite_field(3,
     "(and (= x (ite (= x y) (ff.neg y) y)) (= (ff.neg (ff.bitsum x (as ff2 F))) (as ff1 F)))")),
    ("ff-3-case-04", finite_field(3,
     "(and (= (ff.mul (ite (= x y) (as ff5 F) (as ff1 F)) (ff.mul x y)) (ff.add x (ff.neg (as ff-5 F))))"
     " (= (ff.bitsum (ff.neg (as ff3 F)) x) (ff.add (ff.add (as ff-4 F) (as ff5 F)) (ff.mul x y))))")),
    ("ff-3-case-05", finite_field(3,
     "(and (= (ff.add (ff.bitsum x y) (ff.mul y y)) y)"
     " (= (ff.mul (ff.bitsum (as ff-1 F) x) (ff.bitsum (as ff4 F) (as ff-4 F)))"
     " (ff.add (ite (= x y) y (as ff3 F)) (ff.add x x))))")),
    ("ff-5-case-04", finite_field(5,
     "(and (= (as ff8 F) (ff.mul (ff.mul x x) (ff.neg x)))"
     " (= (ff.add (as ff3 F) y) (ff.add (as ff-9 F) (ite (= x y) (as ff-8 F) y))))")),
    ("ff-7-case-02", finite_field(7,
     "(and (= (ff.add (ff.add (as ff-8 F) (as ff-9 F)) (ff.neg x)) (ite (= x y) (ff.neg (as ff-8 F)) x))"
     " (= (ff.add (ff.neg (as ff-7 F)) (ff.bitsum y y)) (ff.bitsum (ff.mul x x) (as ff-6 F))))")),
)
RULE_EXTENSION_CASES += FINITE_FIELD_THEORY_LEMMA_CASES


# x*y = 1 and x*(y+1) = x+2 have no common root; Z3 refutes them with a `th-lemma`.
def unit_ideal(prime):
    return finite_field(prime,
        "(and (= (ff.mul x y) (as ff1 F)) (= (ff.mul x (ff.add y (as ff1 F))) (ff.add x (as ff2 F))))")


@unittest.skipUnless(os.environ.get("Z3_FSTAR_CHECKER"),
                     "Set Z3_FSTAR_CHECKER to the built native checker")
class DirectCheckerTests(unittest.TestCase):
    def run_checker(self, source, *args):
        checker = os.environ["Z3_FSTAR_CHECKER"]
        distribution = os.environ.get("Z3_FSTAR_WSL_DISTRO")
        wsl = ["wsl"] + (["-d", distribution] if distribution else [])
        command = ([*wsl, "-e", "bash", "-c", checker + ' "$@"', "checker", *args]
                   if os.name == "nt" else [os.path.expanduser(checker), *args])
        return subprocess.run(command, input=source, text=True, capture_output=True, timeout=30)

    def test_zero_extension_refutations_and_counterexamples(self):
        for width, extra in ((1, 0), (1, 1), (8, 24), (65, 65), (1, 4095)):
            declarations = f"(declare-const x (_ BitVec {width}))"
            extension = f"((_ zero_extend {extra}) x)"
            target = f"(concat (_ bv0 {extra}) x)" if extra else "x"
            source = declarations + f"(assert (not (= {extension} {target})))"
            for interactive in (False, True):
                with self.subTest(width=width, extra=extra, interactive=interactive):
                    args = ["--diagnostics"]
                    if interactive:
                        args.append("--interactive")
                    result = self.run_checker(source + ("(check-sat)" if interactive else ""), *args)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertIn("; proof-check ACCEPT" if interactive else "ACCEPT", result.stdout)
                    self.assertNotIn("obligation\t", result.stderr)
        for assertion in (
                "(not (= ((_ zero_extend 24) #xff) #x000000ff))",
                "(= ((_ zero_extend 24) #xff) #xffffffff)"):
            result = self.run_checker(f"(assert {assertion})", "--diagnostics")
            self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                             result.stdout + result.stderr)
        for source in (
                "(declare-const x (_ BitVec 8))"
                "(assert (not (= ((_ zero_extend 24) x) (concat (_ bv1 24) x))))",
                "(declare-const x (_ BitVec 1))"
                "(assert (not (= ((_ zero_extend 1) x) (concat x #b0))))"):
            result = self.run_checker(source, "--diagnostics")
            self.assertEqual((result.returncode, result.stdout.strip()), (4, "SAT"),
                             result.stdout + result.stderr)

    def test_checked_boolean_equality_and_array_refutations(self):
        for source in (
                "(assert false)",
                "(declare-const p Bool)(assert p)(assert (not p))",
                "(declare-sort U 0)(declare-const x U)(declare-const y U)"
                "(declare-fun f (U) U)(assert (= x y))(assert (not (= (f x) (f y))))",
                "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
                "(assert (or (and p q) r))(assert (not p))(assert (not r))",
                "(declare-const a (Array Int Int))(declare-const i Int)(declare-const v Int)"
                "(assert (not (= (select (store a i v) i) v)))"):
            with self.subTest(source=source):
                result = self.run_checker(source, "--stats")
                self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                                 result.stderr)
                self.assertRegex(result.stderr, r"marshal_ms=\d+\.\d+")
                self.assertRegex(result.stderr, r"expressions=\d+")

    def test_unsigned_bv_reflexivity_in_both_modes(self):
        for comparison, negated in (("bvule", True), ("bvuge", True),
                                    ("bvult", False)):
            term = f"({comparison} x x)"
            if negated:
                term = f"(not {term})"
            source = f"(declare-const x (_ BitVec 27))(assert {term})"
            for interactive in (False, True):
                with self.subTest(comparison=comparison, interactive=interactive):
                    result = self.run_checker(
                        source + ("(check-sat)" if interactive else ""),
                        *(["--interactive"] if interactive else []))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    if interactive:
                        self.assertIn("unsat\n; proof-check ACCEPT", result.stdout)
                    else:
                        self.assertEqual(result.stdout.strip(), "ACCEPT", result.stderr)

    def test_uf_allows_a_user_sort_named_set_in_both_modes(self):
        source = ("(set-logic UF)(declare-sort Set 0)(declare-const x Set)"
                  "(declare-fun p (Set) Bool)(assert (p x))(assert (not (p x)))")
        direct = self.run_checker(source)
        self.assertEqual((direct.returncode, direct.stdout.strip()), (0, "ACCEPT"),
                         direct.stderr)
        interactive = self.run_checker(source + "(check-sat)", "--interactive")
        self.assertEqual(interactive.returncode, 0, interactive.stderr)
        self.assertIn("unsat\n; proof-check ACCEPT", interactive.stdout)

    def test_linear_arithmetic_is_fully_checked(self):
        result = self.run_checker(
            "(declare-const x Real)(declare-const y Real)"
            "(assert (<= (+ x y) 0))(assert (> x 0))(assert (> y 0))")
        self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                         result.stderr)

    def test_integer_rounding_certifies_qf_lia_ring_benchmarks(self):
        # SMT-LIB 2025 QF_LIA ring benchmarks (Alberto Griggio), verbatim. Their carry lemmas hold over
        # the integers but not over the rationals, and z3 labels them `arith unsupported`: each lemma
        # needs rounding a row whose coefficients share a factor (after fixed variables are
        # substituted), then a Farkas refutation.
        repair = Path(__file__).resolve().parent.parent / "benchmarks" / "repair"
        for name in ("ring_2exp4_6vars_3ite_unsat.smt2", "ring_2exp8_6vars_2ite_unsat.smt2"):
            source = (repair / name).read_text()
            with self.subTest(name=name, interactive=False):
                result = self.run_checker(source, "--diagnostics")
                self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                                 result.stdout + result.stderr)
                self.assertNotIn("obligation\t", result.stderr)
            with self.subTest(name=name, interactive=True):
                result = self.run_checker(source, "--interactive")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT", result.stdout)

    def test_bounded_bv_evaluation_certifies_qf_abv_egt_benchmarks(self):
        # SMT-LIB QF_ABV/egt/egt-0160.smt2, egt-0218.smt2 and egt-4297.smt2 (Vijay Ganesh, Clark Barrett),
        # verbatim. Their pending rewrites and bit-vector theory lemmas range over one 8-bit leaf
        # (select packet #x000000f1) and are decided by evaluating them under all 256 values of the leaf.
        repair = Path(__file__).resolve().parent.parent / "benchmarks" / "repair"
        for name in ("egt-0160.smt2", "egt-0218.smt2", "egt-4297.smt2"):
            source = (repair / name).read_text()
            with self.subTest(name=name, interactive=False):
                result = self.run_checker(source, "--diagnostics")
                self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                                 result.stdout + result.stderr)
                self.assertNotIn("obligation\t", result.stderr)
            with self.subTest(name=name, interactive=True):
                result = self.run_checker(source, "--interactive")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT", result.stdout)
        source = (repair / "egt-0160.smt2").read_text()
        # A satisfiable variant (bound 400 instead of 547) has no proof to certify.
        satisfiable = source.replace("(bvule ?v_0 (_ bv547 32))", "(bvule ?v_0 (_ bv400 32))")
        self.assertNotEqual(satisfiable, source)
        result = self.run_checker(satisfiable, "--diagnostics")
        self.assertEqual((result.returncode, result.stdout.strip()), (4, "SAT"), result.stdout + result.stderr)
        # egt-6871's only lemma needs signed `bvsle` and `bit2bool`, which the native bridge leaves opaque.
        source = (repair / "egt-6871.smt2").read_text()
        result = self.run_checker(source, "--diagnostics")
        self.assertEqual((result.returncode, result.stdout.strip()), (3, "PARTIAL 1"),
                         result.stdout + result.stderr)
        self.assertIn("obligation\tth-lemma\t1\t", result.stderr)

    def test_bv_sum_normalization_removes_pending_qf_abv_rewrites(self):
        # SMT-LIB QF_ABV benchmarks of the pulse reports, verbatim: egt-1341, egt-1513 and egt-4119
        # (Vijay Ganesh, Clark Barrett; bench run 40723098000) and try4_difret_functions_disjunctions_mv.hash_pjw
        # (Ivan Jager; z3 run 40718873785). Their rewrite steps bvadd(bvadd(c1, t), c2) = bvadd(c3, t) (c3 =
        # c1 + c2 modulo 2^32, over an uninterpreted constant or an 8-bit read zero-extended to 32 bits), the
        # same with a bare t when the numerals cancel, and the n-ary forms bvadd(bvadd(c1, t0, t1), c2) =
        # bvadd(c3, t0, t1), bvadd(bvadd(c1, t0), bvadd(c2, t1)) = bvadd(c3, t0, t1) and bvadd(c1, bvadd(c2, t0,
        # t1)) = bvadd(c3, t0, t1) are decided by the modular normalization of Z3BvAddNormalize. None of the four
        # is a full ACCEPT: the other rewrites and the bit-vector theory lemmas stay pending, so the checks are the
        # exact number of pending steps and the absence of the re-association fingerprints.
        repair = Path(__file__).resolve().parent.parent / "benchmarks" / "repair"
        reassociation = "eq(bvadd:U(bvadd:U("
        for name, pending, families in (
                ("egt-1513.smt2", 4, 4),
                ("egt-4119.smt2", 3, 3),
                ("egt-1341.smt2", 4, 4),
                ("try4_difret_functions_disjunctions_mv.hash_pjw.il.disjunctions_0.smt2", 39, 20)):
            with self.subTest(name=name):
                source = (repair / name).read_text()
                result = self.run_checker(source, "--diagnostics")
                self.assertEqual((result.returncode, result.stdout.strip()), (3, f"PARTIAL {pending}"),
                                 result.stdout + result.stderr)
                self.assertIn(f"diagnostic\tchecked\tpending={pending}\tfamilies={families}\n", result.stderr)
                self.assertNotIn(reassociation, result.stderr)
        # The bound 300 instead of 547 makes egt-1513 satisfiable: there is no proof to certify.
        source = (repair / "egt-1513.smt2").read_text()
        satisfiable = source.replace("(_ bv547 32)", "(_ bv300 32)")
        self.assertNotEqual(satisfiable, source)
        result = self.run_checker(satisfiable, "--diagnostics")
        self.assertEqual((result.returncode, result.stdout.strip()), (4, "SAT"), result.stdout + result.stderr)

    def test_underspecified_arithmetic_aliases_do_not_leave_open_hypotheses(self):
        source = (
            "(declare-fun a () Real)"
            "(assert (< (/ 1 0 a) 1))"
            "(assert (forall ((b Real)) (= (/ (/ 0 (- b)) 0) 0)))"
            "(assert (forall ((c Real)) (forall ((d Real)) (forall ((e Real))"
            "  (>= (* e c) 2 (* d (/ 1 c) (/ 0 c)))))))")
        for solver in (2, 6):
            for interactive in (False, True):
                with self.subTest(solver=solver, interactive=interactive):
                    text = f"(set-option :smt.arith.solver {solver})" + source
                    args = ["--diagnostics", "--timeout-ms", "10000"]
                    if interactive:
                        text += "(check-sat)"
                        args.append("--interactive")
                    result = self.run_checker(text, *args)
                    self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
                    if interactive:
                        self.assertRegex(result.stdout,
                                         r"unsat\n; proof-check PARTIAL [1-9][0-9]*\n")
                    else:
                        self.assertRegex(result.stdout.strip(), r"^PARTIAL [1-9][0-9]*$")
                    self.assertNotIn("stage=open-root", result.stderr)

    def test_sorted_core_certifies_boolean_and_euf_proofs_in_both_modes(self):
        for source in (
                "(declare-const p Bool)(assert p)(assert (not p))",
                "(declare-sort U 0)(declare-const x U)(declare-const y U)"
                "(declare-fun f (U) U)(assert (= x y))(assert (not (= (f x) (f y))))"):
            with self.subTest(source=source):
                result = self.run_checker(source, "--sorted-core", "--diagnostics", "--stats")
                self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                                 result.stderr)
                self.assertIn("semantics=sorted-core", result.stderr)
                self.assertIn("diagnostic\tchecked\tpending=0", result.stderr)
                interactive = self.run_checker(
                    source + "(check-sat)", "--interactive", "--sorted-core")
                self.assertEqual(interactive.returncode, 0, interactive.stdout + interactive.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT", interactive.stdout)
                self.assertIn("semantics=sorted-core", interactive.stdout)

    def test_sorted_core_does_not_fall_back_to_legacy_arithmetic(self):
        source = ("(declare-const x Real)(declare-const y Real)"
                  "(assert (<= (+ x y) 0))(assert (> x 0))(assert (> y 0))")
        result = self.run_checker(source, "--sorted-core", "--diagnostics", "--stats")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertRegex(result.stdout.strip(), r"^PARTIAL [1-9][0-9]*$")
        self.assertIn("semantics=sorted-core", result.stderr)
        interactive = self.run_checker(source + "(check-sat)", "--interactive", "--sorted-core")
        self.assertEqual(interactive.returncode, 3, interactive.stdout + interactive.stderr)
        self.assertIn("; proof-check PARTIAL ", interactive.stdout)
        self.assertIn("semantics=sorted-core", interactive.stdout)

    def test_contextual_datatype_proofs_in_both_modes(self):
        for source in (
                "(declare-datatype T ((C) (D)))(declare-const x T)"
                "(assert (not ((_ is C) x)))(assert (not ((_ is D) x)))",
                "(declare-datatype T ((C (field Int)) (D)))(declare-const x T)"
                "(assert ((_ is C) x))(assert (not (= x (C (field x)))))"):
            with self.subTest(source=source):
                result = self.run_checker(source, "--diagnostics", "--stats")
                self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                                 result.stderr)
                self.assertIn("semantics=sorted-datatype", result.stderr)
                self.assertIn("diagnostic\tchecked\tpending=0", result.stderr)
                interactive = self.run_checker(source + "(check-sat)", "--interactive")
                self.assertEqual(interactive.returncode, 0,
                                 interactive.stdout + interactive.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT", interactive.stdout)
                self.assertIn("semantics=sorted-datatype", interactive.stdout)

    def test_contextual_datatypes_do_not_fall_back_to_legacy_arithmetic(self):
        result = self.run_checker(
            "(declare-datatype T ((C (field Int)) (D)))(declare-const x T)"
            "(assert (> (field x) 0))(assert (< (field x) 0))",
            "--diagnostics", "--stats")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertRegex(result.stdout.strip(), r"^PARTIAL [1-9][0-9]*$")
        self.assertIn("semantics=sorted-datatype", result.stderr)

    def test_datatype_operations_named_like_connectives(self):
        # Z3 lets user datatypes name accessors and constructors `and`, `or`, `not`, `=>`, `true` and `false`
        # (with argument sorts the builtin connectives do not take); the bridge marshals them with those names
        # and the datatype kind tags. They are datatype operations, never connectives: refutations that need
        # their datatype meaning are certified, and a satisfiable input is never certified unsat.
        accessors = ("(declare-datatypes ((T 0)) (((mk (|and| Bool) (|or| Bool) (|not| Bool)"
                     " (bits (_ BitVec 2))))))")
        constants = "(declare-datatypes ((U 0)) (((mkU (|true| Bool) (|false| Bool) (|=>| Bool)))))(declare-const v U)"
        constructors = ("(declare-datatypes ((R 0)) (((|true| (val Int)) (|false| (other Int)))))"
                        "(declare-const r R)(declare-const q R)")
        for source, expected in (
                (accessors + "(declare-const t T)(assert (|and| t))(assert (not (|and| t)))", (0, "ACCEPT")),
                (accessors + "(assert (|and| (mk false true true #b01)))", (0, "ACCEPT")),
                ("(declare-datatypes ((S 0)) (((|or| (left Int) (right Int)) (|not| (inner Int)))))"
                 "(declare-const s S)(assert (= s (|or| 1 2)))(assert (= s (|not| 3)))", (0, "ACCEPT")),
                (accessors + "(declare-const t T)(assert (|and| t))(assert (|or| t))(assert (not (|not| t)))",
                 (4, "SAT")),
                (constants + "(assert (|true| v))(assert (not (|true| v)))", (0, "ACCEPT")),
                (constants + "(assert (not (|true| v)))(assert (|false| v))(assert (not (|=>| v)))", (4, "SAT")),
                (constructors + "(assert (= r (|true| 1)))(assert (= r (|false| 1)))", (0, "ACCEPT")),
                (constructors + "(assert (= r (|true| 1)))(assert (not (= q (|true| 1))))", (4, "SAT"))):
            with self.subTest(source=source):
                result = self.run_checker(source, "--diagnostics")
                self.assertEqual((result.returncode, result.stdout.strip()), expected,
                                 result.stdout + result.stderr)

    def test_long_sort_names_in_binder_certificates(self):
        # The binder scope guard charges sort names by their length before comparing them. A
        # 300,000-character name exceeds the guard's budget and stays pending; the Cherry checker
        # counted it with a recursion as deep as the name and overflowed its native stack.
        for length, expected in ((1000, "ACCEPT"), (300_000, "PARTIAL")):
            name = "S" * length
            source = (f"(declare-sort {name} 0)(declare-fun p ({name}) Bool)(declare-const c {name})"
                      f"(assert (forall ((x {name})) (and (p x) true)))(assert (not (p c)))")
            with self.subTest(length=length):
                result = self.run_checker(source, "--diagnostics")
                if expected == "ACCEPT":
                    self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                                     result.stdout + result.stderr)
                else:
                    self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
                    self.assertRegex(result.stdout.strip(), r"^PARTIAL [1-9][0-9]*$")

    def test_rule_extensions_in_batch_and_interactive_modes(self):
        for name, source in RULE_EXTENSION_CASES:
            with self.subTest(case=name):
                result = self.run_checker(source, "--diagnostics")
                self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                                 result.stderr)
                interactive = self.run_checker(source + "(check-sat)", "--interactive")
                self.assertEqual(interactive.returncode, 0,
                                 interactive.stdout + interactive.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT\n", interactive.stdout)

    def test_finite_field_theory_lemmas_are_checked_within_the_bound(self):
        # 17^2 assignments are evaluated. Over a 31-bit prime the same refutation has more
        # than 4096; its `th-lemma` step is checked by replaying the recorded ideal certificate.
        result = self.run_checker(unit_ideal(17), "--diagnostics")
        self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"), result.stderr)
        for prime in (2147483647, 2305843009213693951, 170141183460469231731687303715884105727):
            with self.subTest(prime=prime):
                source = unit_ideal(prime)
                result = self.run_checker(source, "--diagnostics")
                self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                                 result.stderr)
                interactive = self.run_checker(source + "(check-sat)", "--interactive")
                self.assertIn("unsat\n; proof-check ACCEPT\n", interactive.stdout)

    def test_finite_field_inverse_witnesses_remain_unchecked(self):
        # A certificate that uses the inverse witness of a disequality needs a prime modulus;
        # its `th-lemma` step stays an unmet obligation, alone or next to a checked one.
        for assertions, pending in (
                ("(assert (= (ff.mul x x) (as ff0 F)))(assert (not (= x (as ff0 F))))", 1),
                ("(assert (= (ff.mul x y) (as ff1 F)))(assert (= (ff.mul x x) (as ff0 F)))", 1)):
            with self.subTest(assertions=assertions):
                source = ("(set-logic QF_FF)(define-sort F () (_ FiniteField 2147483647))"
                          "(declare-const x F)(declare-const y F)" + assertions)
                result = self.run_checker(source, "--diagnostics")
                self.assertEqual((result.returncode, result.stdout.strip()), (3, f"PARTIAL {pending}"),
                                 result.stderr)
                self.assertRegex(result.stderr, r"obligation\tth-lemma\t")
                interactive = self.run_checker(source + "(check-sat)", "--interactive")
                self.assertIn(f"unsat\n; proof-check PARTIAL {pending}\n", interactive.stdout)

    def test_quantified_rewrites_are_certified_in_both_modes(self):
        for source in (
                "(assert (not (forall ((x Int)) (= (+ x 0) x))))",
                "(declare-fun p (Int) Bool)"
                "(assert (not (forall ((x Int)) (or (p (+ x 0)) (not (p x))))))",
                "(assert (exists ((x Int)) (not (= (+ x 0) x))))",
                "(assert (not (forall ((x Int)) (forall ((y Real))"
                "(and (= (+ x 0) x) (= (+ y 0.0) y))))))",
                "(declare-fun p (Int) Bool)"
                "(assert (forall ((x Int)) (p (+ x 0))))(assert (not (p 3)))",
                "(declare-fun p (Int Real) Bool)"
                "(assert (forall ((x Int) (y Real)) (! (p x y) :pattern ((p x y)))))"
                "(assert (not (p 3 4.5)))"):
            with self.subTest(source=source):
                direct = self.run_checker(source, "--diagnostics")
                self.assertEqual((direct.returncode, direct.stdout.strip()), (0, "ACCEPT"),
                                 direct.stderr)
                interactive = self.run_checker(source + "(check-sat)", "--interactive")
                self.assertEqual(interactive.returncode, 0, interactive.stdout + interactive.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT\n", interactive.stdout)
                self.assertRegex(interactive.stdout, r"binder_nodes=\d+ binder_edges=\d+")
                if source.startswith("(assert (not (forall"):
                    self.assertRegex(interactive.stdout, r"binder_nodes=[1-9]\d*")

    def test_quantified_arithmetic_avoids_asserted_false_proofs(self):
        source = ("(assert (forall ((a Real)) (exists ((b Real))"
                  " (and (>= (+ a b) 0.0) (<= b 0.0)))))")
        direct = self.run_checker(source, "--diagnostics")
        self.assertIn(direct.returncode, (0, 3), direct.stdout + direct.stderr)
        self.assertRegex(direct.stdout.strip(), r"^(ACCEPT|PARTIAL [1-9][0-9]*)$")
        self.assertIn("diagnostic\tchecked\tpending=", direct.stderr)
        interactive = self.run_checker(
            source + "(check-sat-using smt)(check-sat)", "--interactive", "--diagnostics")
        self.assertIn(interactive.returncode, (0, 3), interactive.stdout + interactive.stderr)
        self.assertEqual(interactive.stdout.splitlines().count("unsat"), 2)
        self.assertEqual(interactive.stdout.count("; proof-check "), 2)
        self.assertIn("; proof-check ACCEPT", interactive.stdout)
        self.assertNotIn("; proof-check REJECT", interactive.stdout)

    def test_qsat_refuses_unsupported_proof_production(self):
        result = self.run_checker(
            "(assert (forall ((a Real)) (exists ((b Real))"
            " (and (>= (+ a b) 0.0) (<= b 0.0)))))"
            "(check-sat-using qsat)(get-info :reason-unknown)",
            "--interactive")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.splitlines()[0], "unknown")
        self.assertIn("qsat does not support proof production", result.stdout + result.stderr)
        self.assertNotIn("; proof-check ", result.stdout)
        self.assertNotIn("unsat", result.stdout.splitlines())

    def test_uncertified_nonlinear_arithmetic_remains_partial(self):
        result = self.run_checker(
            "(declare-const x Real)"
            "(assert (= (* x x) 2))(assert (= (* x x x) 3))")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertRegex(result.stdout.strip(), r"^PARTIAL [1-9][0-9]*$")

    def test_negative_nnf_binder_is_certified(self):
        for name, source in NEGATIVE_NNF_CASES:
            with self.subTest(case=name):
                result = self.run_checker(source, "--diagnostics")
                self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                                 result.stderr)
                self.assertIn("diagnostic\tchecked\tpending=0", result.stderr)
                interactive = self.run_checker(source + "(check-sat)", "--interactive")
                self.assertEqual(interactive.returncode, 0, interactive.stdout + interactive.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT", interactive.stdout)

    def test_nested_quantifier_pulling_is_certified(self):
        for name, source in PULL_QUANT_CASES:
            with self.subTest(name=name):
                result = self.run_checker(source, "--diagnostics")
                self.assertEqual((result.returncode, result.stdout.strip()),
                                 (0, "ACCEPT"), result.stderr)
                self.assertIn("diagnostic\tchecked\tpending=0", result.stderr)
                interactive = self.run_checker(source + "(check-sat)", "--interactive")
                self.assertEqual(interactive.returncode, 0,
                                 interactive.stdout + interactive.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT", interactive.stdout)

    def test_quantifier_push_through_demorgan_body(self):
        result = self.run_checker(
            "(assert (forall ((a Real)) (exists ((b Real))"
            " (and (>= (+ a b) 0.0) (<= b 0.0)))))"
            "(check-sat-using bv)(check-sat-using smt)(check-sat)",
            "--interactive", "--diagnostics")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.splitlines().count("unsat"), 3)
        self.assertEqual(result.stdout.count("; proof-check ACCEPT"), 3)
        self.assertEqual(result.stderr.count("diagnostic\tchecked\tpending=0"), 3)

    def test_unused_skolem_block_is_certified(self):
        for name, source in UNUSED_SKOLEM_CASES:
            with self.subTest(case=name):
                interactive = self.run_checker(source, "--interactive", "--diagnostics")
                self.assertEqual(interactive.returncode, 0, interactive.stdout + interactive.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT\n", interactive.stdout)
                self.assertNotIn("obligation\t", interactive.stderr)
                if name == "under-binder":
                    self.assertRegex(interactive.stdout, r"binder_nodes=[1-9]\d*")

    def test_factored_sign_rewrites_are_certified(self):
        for name, source in FACTOR_SIGN_CASES:
            with self.subTest(case=name):
                interactive = self.run_checker(
                    source + "(check-sat)", "--interactive", "--diagnostics")
                self.assertEqual(interactive.returncode, 0, interactive.stdout + interactive.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT\n", interactive.stdout)
                self.assertNotIn("obligation\t", interactive.stderr)
        satisfiable = self.run_checker(
            "(declare-const x Real)(assert (and (< 1.0 x) (< x (* x x))))(check-sat)",
            "--interactive")
        self.assertEqual(satisfiable.returncode, 0, satisfiable.stdout + satisfiable.stderr)
        self.assertEqual(satisfiable.stdout.strip(), "sat")

    def test_conditional_comparison_rewrites_are_certified(self):
        for name, source in ITE_COMPARISON_CASES:
            with self.subTest(case=name):
                interactive = self.run_checker(
                    source + "(check-sat)", "--interactive", "--diagnostics")
                self.assertEqual(interactive.returncode, 0, interactive.stdout + interactive.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT\n", interactive.stdout)
                self.assertNotIn("obligation\t", interactive.stderr)
        satisfiable = self.run_checker(
            "(declare-const c Bool)(declare-const x Int)"
            "(assert (>= (ite c 0 x) 1))(assert (not c))(check-sat)",
            "--interactive")
        self.assertEqual(satisfiable.returncode, 0, satisfiable.stdout + satisfiable.stderr)
        self.assertEqual(satisfiable.stdout.strip(), "sat")

    def test_bv_extract_rewrites_are_certified(self):
        for name, source in BV_EXTRACT_CASES:
            with self.subTest(case=name):
                interactive = self.run_checker(
                    source + "(check-sat)", "--interactive", "--diagnostics")
                self.assertEqual(interactive.returncode, 0, interactive.stdout + interactive.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT\n", interactive.stdout)
                self.assertNotIn("obligation\t", interactive.stderr)
        # Bits above the lowest are not a sum of the extracted bits (carries).
        satisfiable = self.run_checker(
            "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"
            "(assert (not (= ((_ extract 4 1) (bvadd x y))"
            " (bvadd ((_ extract 4 1) x) ((_ extract 4 1) y)))))(check-sat)",
            "--interactive")
        self.assertEqual(satisfiable.returncode, 0, satisfiable.stdout + satisfiable.stderr)
        self.assertEqual(satisfiable.stdout.strip(), "sat")

    def test_bv_extract_concat_rewrites_are_certified(self):
        for name, source in BV_EXTRACT_CONCAT_CASES:
            with self.subTest(case=name):
                interactive = self.run_checker(
                    source + "(check-sat)", "--interactive", "--diagnostics")
                self.assertEqual(interactive.returncode, 0, interactive.stdout + interactive.stderr)
                self.assertIn("unsat\n; proof-check ACCEPT\n", interactive.stdout)
                self.assertNotIn("obligation\t", interactive.stderr)
        # Bits of x offset by one, and the two parts in the other order, are other bits.
        for name, source in (
                ("offset", "(assert (not (= ((_ extract 14 9) (concat x y)) ((_ extract 7 2) x))))"),
                ("order", "(assert (not (= ((_ extract 9 4) (concat x y))"
                          " (concat ((_ extract 7 4) y) ((_ extract 1 0) x)))))")):
            with self.subTest(case=name):
                satisfiable = self.run_checker(
                    "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"
                    + source + "(check-sat)", "--interactive")
                self.assertEqual(satisfiable.returncode, 0,
                                 satisfiable.stdout + satisfiable.stderr)
                self.assertEqual(satisfiable.stdout.strip(), "sat")

    def test_sat_is_not_certified_unsat(self):
        result = self.run_checker("(declare-const x Int)(assert (> x 0))")
        self.assertEqual((result.returncode, result.stdout.strip()), (4, "SAT"), result.stderr)

    def test_timeout_is_not_certified_unsat(self):
        n = 20
        terms = ["(declare-const p%d_%d Bool)" % (i, j)
                 for i in range(n) for j in range(n - 1)]
        terms.extend("(assert (or %s))" % " ".join("p%d_%d" % (i, j) for j in range(n - 1))
                     for i in range(n))
        terms.extend("(assert (or (not p%d_%d) (not p%d_%d)))" % (i, j, k, j)
                     for j in range(n - 1) for i in range(n) for k in range(i))
        result = self.run_checker("\n".join(terms), "--timeout-ms", "1")
        self.assertEqual(result.returncode, 5, result.stdout + result.stderr)
        self.assertRegex(result.stdout, r"^UNKNOWN .*timeout")

    def test_malformed_input_and_arguments_report_errors(self):
        for source, args in (
                ("(assert missing)", ()),
                ('{"format":"resolution-v1","root":0}', ()),
                ("(assert false)", ("--smt2",)),
                ("(assert false)", ("--check-original-assertions",)),
                ("(assert false)", ("--timeout-ms", "-1")),
                ("(assert false)", ("--timeout-ms", "not-a-number")),
                ("(assert false)", ("--timeout-ms", "4294967296"))):
            with self.subTest(source=source, args=args):
                result = self.run_checker(source, *args)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertTrue(result.stderr.strip())
                self.assertNotIn("ACCEPT", result.stdout)

    def test_version_reports_embedded_solver_without_solving_input(self):
        result = self.run_checker("(assert missing)", "--version")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertRegex(result.stdout, r"^\d+\.\d+\.\d+\.\d+\n$")
        self.assertEqual(result.stderr, "")

    def test_help_describes_only_smtlib_input(self):
        result = self.run_checker("", "--help")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("input.smt2", result.stdout)
        self.assertNotIn("JSON", result.stdout)
        self.assertNotIn("--smt2", result.stdout)

    def test_diagnostics_preserve_results_and_count_typed_obligations(self):
        for source in (
                "(assert false)",
                "(declare-const x Real)(declare-const y Real)"
                "(assert (<= (+ x y) 0))(assert (> x 0))(assert (> y 0))",
                "(declare-const x Real)(declare-const y Real)(declare-const p Bool)"
                "(assert (or p (<= x (- 6.0))))(assert (=> p (>= (+ x y) 1.5)))"
                "(assert (< y (/ 1.0 3.0)))(assert (> x 0.0))(assert (<= x 1.0))",
                "(declare-const x Real)"
                "(assert (= (* x x) 2))(assert (= (* x x x) 3))"):
            with self.subTest(source=source):
                plain = self.run_checker(source)
                diagnostic = self.run_checker(source, "--diagnostics", "--stats")
                self.assertEqual((diagnostic.returncode, diagnostic.stdout),
                                 (plain.returncode, plain.stdout), diagnostic.stderr)
                rows = [line.split("\t") for line in diagnostic.stderr.splitlines()
                        if line.startswith("obligation\t")]
                expected = int(plain.stdout.split()[1]) if plain.returncode == 3 else 0
                self.assertEqual(sum(int(row[2]) for row in rows), expected)
                self.assertIn("diagnostic\tchecked\tpending=%d\t" % expected, diagnostic.stderr)
                self.assertRegex(diagnostic.stderr, r"diagnose_ms=\d+\.\d+")
                if expected:
                    renamed = self.run_checker(source.replace("x", "a").replace("y", "b"),
                                               "--diagnostics")
                    shapes = lambda result: [(row[1], row[2], row[4]) for row in
                        (line.split("\t") for line in result.stderr.splitlines()
                         if line.startswith("obligation\t"))]
                    self.assertEqual(shapes(diagnostic), shapes(renamed))

    def test_file_mode_creates_no_proof_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.smt2"
            path.write_text("(assert false)", encoding="ascii")
            native_path = str(path)
            if os.name == "nt":
                native_path = "/mnt/" + path.drive[0].lower() + "/" + str(path)[3:].replace("\\", "/")
            result = self.run_checker("", native_path)
            self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"), result.stderr)
            self.assertEqual(list(Path(directory).iterdir()), [path])

    def test_interactive_checks_scoped_assumptions_and_tactics(self):
        result = self.run_checker(
            "(declare-const p Bool)(assert p)(check-sat)(get-model)\n"
            "(check-sat-assuming ((not p)))\n"
            "(push)(assert (not p))(check-sat-using smt)(pop)(check-sat)\n"
            "(reset-assertions)(assert false)(check-sat)(exit)\n",
            "--interactive", "--stats", "--diagnostics")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.splitlines().count("sat"), 2)
        self.assertEqual(result.stdout.splitlines().count("unsat"), 3)
        self.assertEqual(result.stdout.count("; proof-check ACCEPT"), 3)
        self.assertIn("define-fun p", result.stdout)
        self.assertEqual(result.stderr.count("marshal_ms="), 3)
        self.assertEqual(result.stderr.count("diagnostic\tchecked\tpending=0"), 3)

    def test_clause_proofs_in_batch_and_interactive_modes(self):
        sources = (
            "(declare-const p Bool)(declare-const q Bool)"
            "(assert (or p q))(assert (or p (not q)))"
            "(assert (or (not p) q))(assert (or (not p) (not q)))",
            "(declare-sort U 0)(declare-const x U)(declare-const y U)"
            "(declare-fun f (U) U)(assert (= x y))(assert (not (= (f x) (f y))))",
            "(declare-const x Real)(declare-const y Real)"
            "(assert (<= (+ x y) 0))(assert (> x 0))(assert (> y 0))",
            "(declare-const a (Array Int Int))(declare-const i Int)"
            "(assert (not (= (select (store a i 1) i) 1)))",
            "(declare-sort I 0)(declare-sort E 0)(declare-const a (Array I E))"
            "(declare-const i I)(declare-const j I)(declare-const v E)"
            "(assert (distinct i j))"
            "(assert (distinct (select (store a i v) j) (select a j)))",
        )
        for source in sources:
            for flags in ((), ("--sorted-core",)) if source == sources[0] else ((),):
                with self.subTest(source=source, flags=flags):
                    result = self.run_checker(source, "--clause-proofs", *flags)
                    self.assertEqual((result.returncode, result.stdout.strip()),
                                     (0, "ACCEPT"), result.stderr)
                    result = self.run_checker(source + "(check-sat)",
                                              "--interactive", "--clause-proofs", *flags)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertIn("unsat\n; proof-check ACCEPT", result.stdout)

    def test_clause_proofs_across_scopes_assumptions_and_resets(self):
        result = self.run_checker(
            "(declare-const p Bool)(declare-const q Bool)(assert (or p q))"
            "(push)(assert (not p))(assert (not q))(check-sat)(pop)"
            "(check-sat)(check-sat-assuming ((not p) (not q)))"
            "(push)(assert (or p (not q)))(assert (or (not p) q))"
            "(assert (or (not p) (not q)))(check-sat-using smt)(pop)"
            "(check-sat)(reset)(assert false)(check-sat)",
            "--interactive", "--clause-proofs")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.count("; proof-check ACCEPT"), 4)
        self.assertEqual(result.stdout.splitlines().count("sat"), 2)

    def test_clause_proofs_preserve_disjunction_literals(self):
        source = "(declare-const p Bool)(declare-const q Bool)" \
                 "(declare-const r Bool)(declare-const s Bool)" \
                 "(declare-const a Bool)(declare-const b Bool)" \
                 "(assert (or (or p q) a))(assert (or (or p q) (not a)))" \
                 "(assert (or (or r s) b))(assert (or (or r s) (not b)))" \
                 "(assert (or (not (or p q)) (not (or r s))))"
        for flags in ((), ("--sorted-core",)):
            with self.subTest(flags=flags):
                result = self.run_checker(source, "--clause-proofs", *flags)
                self.assertEqual((result.returncode, result.stdout.strip()),
                                 (0, "ACCEPT"), result.stderr)

    def test_clause_proofs_with_nontrivial_learning_and_simplification(self):
        source = "".join("(declare-const p%d_%d Bool)" % (p, h)
                         for p in range(5) for h in range(4))
        source += "".join("(assert (or %s))" % " ".join("p%d_%d" % (p, h)
                                                       for h in range(4))
                          for p in range(5))
        source += "".join("(assert (or (not p%d_%d) (not p%d_%d)))" % (p, h, q, h)
                          for h in range(4) for p in range(5) for q in range(p))
        result = self.run_checker(source, "--clause-proofs")
        self.assertEqual((result.returncode, result.stdout.strip()),
                         (0, "ACCEPT"), result.stderr)

    def test_interactive_frames_multiline_strings_comments_and_quoted_symbols(self):
        result = self.run_checker(
            '; comment with ) and "\n'
            '(echo "a ""quoted (value)"" ; text")\n'
            '(declare-const |p(;)| Bool)\n(assert\n |p(;)|\n)\n'
            '(assert (not ; ignored closing )\n |p(;)|)) (check-sat)\n',
            "--interactive")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('quoted (value)', result.stdout)
        self.assertIn("unsat\n; proof-check ACCEPT\n", result.stdout)

    def test_interactive_reset_and_named_assertions(self):
        result = self.run_checker(
            "(assert false)(check-sat)(reset)"
            "(set-option :produce-unsat-cores true)"
            "(declare-const p Bool)(assert (! p :named A))"
            "(assert (! (not p) :named B))(check-sat)(get-unsat-core)",
            "--interactive")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.count("; proof-check ACCEPT"), 2)
        self.assertIn("(A B)", result.stdout)

    def test_interactive_redundant_global_declarations_options(self):
        for option in ("global-decls", "global-declarations"):
            with self.subTest(option=option):
                result = self.run_checker(
                    f"(set-option :{option} false)"
                    "(declare-const p Bool)"
                    f"(set-option :{option} false)"
                    "(assert p)(assert (not p))(check-sat)(reset)"
                    f"(set-option :{option} false)"
                    "(assert false)(check-sat)",
                    "--interactive")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout.count("; proof-check ACCEPT"), 2)
                self.assertNotIn("(error", result.stdout)

    def test_interactive_global_declarations_changes_preserve_scope(self):
        result = self.run_checker(
            "(declare-const p Bool)(set-option :global-decls true)"
            "(push)(declare-const q Bool)(pop)(assert q)"
            "(assert false)(check-sat)",
            "--interactive")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("cannot be modified after initialization", result.stdout)
        self.assertIn("unknown constant q", result.stdout)
        self.assertIn("unsat\n; proof-check ACCEPT\n", result.stdout)

    def test_interactive_partial_is_not_a_certificate(self):
        result = self.run_checker(
            "(declare-const x Real)"
            "(assert (= (* x x) 2))(assert (= (* x x x) 3))(check-sat)",
            "--interactive")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertRegex(result.stdout, r"unsat\n; proof-check PARTIAL [1-9][0-9]*")
        self.assertNotIn("ACCEPT", result.stdout)
        pending = next(line.split()[-1] for line in result.stdout.splitlines()
                       if line.startswith("; proof-check PARTIAL "))
        self.assertIn("pending=" + pending, result.stdout)

    def test_interactive_reports_per_check_proof_statistics(self):
        result = self.run_checker(
            "(assert false)(check-sat)(reset)"
            "(declare-const p Bool)(assert p)(check-sat-assuming ((not p)))",
            "--interactive")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        rows = [dict(field.split("=", 1) for field in line.split()[2:])
                for line in result.stdout.splitlines() if line.startswith("; proof-stats ")]
        self.assertEqual(len(rows), 2, result.stdout)
        self.assertEqual([int(row["assertions"]) for row in rows], [1, 2])
        self.assertEqual(int(rows[0]["proof_nodes"]), 1)
        self.assertEqual(int(rows[0]["proof_edges"]), 0)
        self.assertGreater(int(rows[1]["proof_nodes"]), 1)
        self.assertGreater(int(rows[1]["proof_edges"]), 0)
        for row in rows:
            self.assertEqual(row["pending"], "0")
            for key in ("expressions", "declarations"):
                self.assertGreater(int(row[key]), 0)
            for key in ("solve_ms", "marshal_ms", "check_ms"):
                self.assertGreaterEqual(float(row[key]), 0)
        self.assertEqual(result.stderr, "")

    def test_interactive_errors_do_not_disable_certification(self):
        result = self.run_checker(
            "(set-option :produce-proofs false)"
            "(assert missing)(assert false)(check-sat)",
            "--interactive")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("interactive mode requires", result.stdout)
        self.assertIn("unknown constant missing", result.stdout)
        self.assertIn("unsat\n; proof-check ACCEPT\n", result.stdout)

    def test_interactive_exit_unknown_and_incomplete_input(self):
        result = self.run_checker("( ; comment\n exit )\n(assert missing)", "--interactive")
        self.assertEqual((result.returncode, result.stdout), (0, ""), result.stderr)
        result = self.run_checker(
            "(declare-const p Bool)(assert p)(check-sat-using skip)", "--interactive")
        self.assertEqual((result.returncode, result.stdout), (0, "unknown\n"), result.stderr)
        for source in ("(assert", '(echo "unfinished', "(assert |unfinished"):
            result = self.run_checker(source, "--interactive")
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn("incomplete SMT-LIB command", result.stderr)
        result = self.run_checker("", "--interactive", "unused.smt2")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)

    def test_interactive_replies_before_stdin_closes(self):
        checker = os.environ["Z3_FSTAR_CHECKER"]
        distribution = os.environ.get("Z3_FSTAR_WSL_DISTRO")
        wsl = ["wsl"] + (["-d", distribution] if distribution else [])
        command = ([*wsl, "-e", "bash", "-c", checker + ' "$@"',
                    "checker", "--interactive"]
                   if os.name == "nt" else [os.path.expanduser(checker), "--interactive"])
        process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, text=True)
        replies = queue.Queue()
        reader = threading.Thread(
            target=lambda: replies.put([process.stdout.readline() for _ in range(3)]),
            daemon=True)
        try:
            reader.start()
            process.stdin.write("(assert false)(check-sat)\n")
            process.stdin.flush()
            lines = replies.get(timeout=15)
            self.assertEqual(lines[:2], ["unsat\n", "; proof-check ACCEPT\n"])
            self.assertTrue(lines[2].startswith("; proof-stats "), lines)
            _, error = process.communicate("(exit)\n", timeout=15)
            self.assertEqual(process.returncode, 0, error)
        finally:
            if process.poll() is None:
                process.kill()
                process.communicate()
            reader.join(timeout=5)


@unittest.skipUnless(os.environ.get("Z3_FSTAR_CHECKER"),
                     "Set Z3_FSTAR_CHECKER to the built native checker")
class ReadableDiagnosticsTests(unittest.TestCase):
    """--readable adds bounded, lossless pending conditions after the unchanged machine diagnostics."""
    run_checker = DirectCheckerTests.run_checker
    NONLINEAR = "(declare-const x Real)(assert (= (* x x) 2))(assert (= (* x x x) 3))"
    REPAIR = Path(__file__).resolve().parent.parent / "benchmarks" / "repair"

    def run_utf8(self, source, *args):
        checker = os.environ["Z3_FSTAR_CHECKER"]
        distribution = os.environ.get("Z3_FSTAR_WSL_DISTRO")
        wsl = ["wsl"] + (["-d", distribution] if distribution else [])
        command = ([*wsl, "-e", "bash", "-c", checker + ' "$@"', "checker", *args]
                   if os.name == "nt" else [os.path.expanduser(checker), *args])
        result = subprocess.run(command, input=source.encode("utf-8"), capture_output=True, timeout=30)
        return subprocess.CompletedProcess(result.args, result.returncode,
                                           result.stdout.decode("utf-8"), result.stderr.decode("utf-8"))

    def conclusion(self, stderr):
        return re.search(r"(?m)^  conclusion: (.*)$", stderr).group(1)

    def test_flag_changes_neither_verdicts_nor_the_machine_rows_it_extends(self):
        accepted = "(assert false)"
        satisfiable = "(declare-const x Int)(assert (> x 0))"
        sources = {"accepted": accepted, "satisfiable": satisfiable, "real": self.NONLINEAR,
                   "bit-vector": (self.REPAIR / "egt-6871.smt2").read_text(),
                   "finite-field": ("(set-logic QF_FF)(define-sort F () (_ FiniteField 2147483647))"
                                    "(declare-const x F)(assert (= (ff.mul x x) (as ff0 F)))"
                                    "(assert (not (= x (as ff0 F))))")}
        for name, source in sources.items():
            for interactive in (False, True):
                args = ("--interactive",) if interactive else ()
                text = source + "(check-sat)" if interactive else source
                with self.subTest(source=name, interactive=interactive):
                    plain = self.run_checker(text, *args)
                    diagnostic = self.run_checker(text, "--diagnostics", *args)
                    readable = self.run_checker(text, "--readable", *args)
                    both = self.run_checker(text, "--diagnostics", "--readable", *args)
                    # `; proof-stats` carries timings; everything else on stdout is the protocol.
                    protocol = lambda result: (result.returncode, re.sub(r"(?m)^; proof-stats .*\n?", "", result.stdout))
                    self.assertEqual(protocol(readable), protocol(plain), readable.stderr)
                    self.assertEqual(protocol(diagnostic), protocol(plain), diagnostic.stderr)
                    self.assertEqual(readable.stderr, both.stderr)
                    self.assertTrue(readable.stderr.startswith(diagnostic.stderr), readable.stderr)
                    for line in readable.stderr[len(diagnostic.stderr):].splitlines():
                        self.assertTrue(line.startswith(("readable\t", "  ")), line)
                    self.assertEqual("readable\t" in readable.stderr, name not in ("satisfiable",))

    def test_pending_real_conditions_show_values_sorts_and_declaration_identity(self):
        for interactive in (False, True):
            with self.subTest(interactive=interactive):
                text = self.NONLINEAR + ("(check-sat)" if interactive else "")
                result = self.run_checker(text, "--readable", *(("--interactive",) if interactive else ()))
                self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
                stderr = result.stderr
                self.assertRegex(stderr, r"(?m)^readable\tquery=1\tverdict=PARTIAL 1\tpending=1\tfamilies=1\tshown=1$")
                self.assertRegex(stderr, r"(?m)^readable\tfamily=1/1\trule=th-lemma\tcount=1\tmembers=1"
                                         r"\tnode=0\tnode-pending=1$")
                conclusion = self.conclusion(stderr)
                self.assertRegex(conclusion, r"\(\* x#\d+:Real x#\d+:Real x#\d+:Real\) 3:Real\)")
                self.assertRegex(conclusion, r"\(\* x#\d+:Real x#\d+:Real\) 2:Real\)")
                self.assertIn("\n  source formula: same as conclusion\n", stderr)
                self.assertTrue(stderr.endswith("readable\tend\tquery=1\n"), stderr)

    def test_bit_vector_values_widths_and_array_sorts_are_kept(self):
        result = self.run_checker((self.REPAIR / "egt-6871.smt2").read_text(), "--readable")
        self.assertEqual((result.returncode, result.stdout.strip()), (3, "PARTIAL 1"), result.stderr)
        conclusion = self.conclusion(result.stderr)
        for expected in ("(_ bv308 32)", "(_ bv241 32)", "concat[24,8]:BV32", "bvadd[32]", "(Array BV32 BV8)"):
            self.assertIn(expected, conclusion)
        self.assertRegex(conclusion, r"\(bvsle#\d+:Bool \(_ bv308 32\)")
        self.assertRegex(conclusion, r"\(bit2bool#\d+:Bool \(select:BV8 packet#\d+:\(Array BV32 BV8\) \(_ bv241 32\)\)\)")
        machine = [line for line in result.stderr.splitlines() if line.startswith("obligation\t")]
        self.assertEqual(len(machine), 1)
        self.assertNotIn("308", machine[0])

    def test_multi_index_arrays_and_same_named_functions_stay_distinguishable(self):
        arrays = ("(declare-const a (Array Int Int Real))(assert (= (* (select a 1 2) (select a 1 2)) 2))"
                  "(assert (= (* (select a 1 2) (select a 1 2) (select a 1 2)) 3))")
        result = self.run_checker(arrays, "--readable")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertRegex(self.conclusion(result.stderr), r"\(select:Real a#\d+:\(Array Int Int Real\) 1 2\)")
        overloaded = ("(declare-fun f (Int) Real)(declare-fun f (Real) Real)"
                      "(assert (= (* (f 1) (f 1.0)) 2))(assert (= (* (f 1) (f 1.0) (f 1) (f 1.0)) 5))")
        result = self.run_checker(overloaded, "--readable")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        conclusion = self.conclusion(result.stderr)
        self.assertEqual(len(set(re.findall(r"\bf#(\d+):Real", conclusion))), 2, conclusion)
        self.assertRegex(conclusion, r"\(f#\d+:Real 1\)")
        self.assertRegex(conclusion, r"\(f#\d+:Real 1:Real\)")

    def test_datatype_accessor_named_like_a_connective_is_marked(self):
        source = ("(declare-datatypes ((T 0)) (((mk (|and| Real)))))(declare-const t T)"
                  "(assert (= (* (|and| t) (|and| t)) 2))(assert (= (* (|and| t) (|and| t) (|and| t)) 3))")
        result = self.run_checker(source, "--readable")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertRegex(result.stderr, r"\(and@accessor\[\d+,\d+,0\]:Real t#\d+:T#\d+\)")

    def test_premises_come_from_the_document_node_of_the_obligation(self):
        source = ("(declare-const x Real)(assert (exists ((a Real)) (and (= (* a a) x) (> a 1))))"
                  "(assert (< (* x x) 1))")
        result = self.run_checker(source, "--readable")
        self.assertEqual((result.returncode, result.stdout.strip()), (3, "PARTIAL 1"), result.stderr)
        family = re.search(r"(?m)^readable\tfamily=1/1\trule=arith/farkas\t.*\tnode=(\d+)\t", result.stderr)
        self.assertTrue(family, result.stderr)
        node = re.search(r"(?m)^  node (\d+): premises: #(\d+) #(\d+)$", result.stderr)
        self.assertTrue(node, result.stderr)
        self.assertEqual(node.group(1), family.group(1))
        for premise in node.group(2, 3):
            self.assertRegex(result.stderr, r"(?m)^  premise #%s: holds\(" % premise)
        self.assertRegex(result.stderr, r"(?m)^  premise #%s: holds\(\(not \(<= a!2#\d+:Real 1:Real\)\)\)$" % node.group(2))

    def test_interactive_queries_are_numbered_like_proof_callbacks(self):
        script = ("(declare-const x Real)"
                  "(push)(assert (= (* x x) 2))(assert (= (* x x x) 3))(check-sat)(pop)"
                  "(push)(assert (> x 0))(check-sat)(pop)"
                  "(push)(assert (= (* x x) 3))(assert (= (* x x x x) 5))(check-sat)(pop)")
        result = self.run_checker(script, "--interactive", "--readable")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        verdicts = re.findall(r"(?m)^; proof-check (.*)$", result.stdout)
        self.assertEqual(len(verdicts), 2, result.stdout)
        self.assertEqual(result.stdout.count("\nsat\n") + result.stdout.startswith("sat\n"), 1, result.stdout)
        headers = re.findall(r"(?m)^readable\tquery=(\d+)\tverdict=(.*?)\tpending=", result.stderr)
        self.assertEqual(headers, [("1", verdicts[0]), ("2", verdicts[1])], result.stderr)
        self.assertEqual(result.stderr.count("readable\tend\tquery="), 2)

    def test_accepted_proofs_have_an_empty_block_and_satisfiable_inputs_none(self):
        accepted = self.run_checker("(assert false)", "--readable")
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertEqual(accepted.stderr,
                         "diagnostic\tchecked\tpending=0\tfamilies=0\n"
                         "readable\tquery=1\tverdict=ACCEPT\tpending=0\tfamilies=0\tshown=0\n"
                         "readable\tend\tquery=1\n")
        satisfiable = self.run_checker("(declare-const x Int)(assert (> x 0))", "--readable")
        self.assertEqual((satisfiable.returncode, satisfiable.stdout.strip(), satisfiable.stderr), (4, "SAT", ""))

    def test_large_conclusions_are_truncated_with_markers(self):
        count = 1500
        declarations = "".join("(declare-const y%d Real)" % i for i in range(count))
        arguments = " ".join("y%d" % i for i in range(count))
        source = (declarations + "(declare-fun f (%s) Real)" % " ".join(["Real"] * count) +
                  "(assert (= (* (f %s) (f %s)) 2))(assert (= (* (f %s) (f %s) (f %s)) 3))" % ((arguments,) * 5))
        result = self.run_checker(source, "--readable")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        conclusion = self.conclusion(result.stderr)
        self.assertRegex(conclusion, r"<\.\.\.(chars|nodes)>$")
        self.assertLessEqual(len(conclusion), 4096 + 40)

    def test_unicode_names_are_quoted_and_kept(self):
        source = ("(declare-const |h\u00e9llo \u2603| Real)"
                  "(assert (= (* |h\u00e9llo \u2603| |h\u00e9llo \u2603|) 2))"
                  "(assert (= (* |h\u00e9llo \u2603| |h\u00e9llo \u2603| |h\u00e9llo \u2603|) 3))")
        result = self.run_utf8(source, "--readable")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertRegex(self.conclusion(result.stderr), r"\|h\u00e9llo \u2603\|#\d+:Real")

    def test_constant_arrays_keep_the_array_sort_their_arguments_do_not_carry(self):
        # `(const 0)` alone cannot say which array it is: the domain sorts of a constant array occur nowhere in its arguments, so a
        # printer that drops the range makes two different conditions read the same (it was byte-identical for these two inputs).
        def source(domain):
            term = "(f ((as const (Array %s Int)) 0))" % domain
            return ("(declare-fun f ((Array %s Int)) Real)(assert (= (* %s %s) 2))(assert (= (* %s %s %s) 3))"
                    % (domain, term, term, term, term, term))
        conclusions = {}
        for domain in ("Int", "Real"):
            with self.subTest(domain=domain):
                result = self.run_checker(source(domain), "--readable")
                self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
                conclusions[domain] = self.conclusion(result.stderr)
                self.assertRegex(conclusions[domain], r"\(f#\d+:Real \(const:\(Array %s Int\) 0\)\)" % domain)
        self.assertEqual(len(conclusions), 2)
        self.assertNotEqual(conclusions["Int"], conclusions["Real"])
        # both arrays in one document: same-named overloads stay apart by id, and each argument keeps its own array sort
        int_term, real_term = "(g ((as const (Array Int Int)) 0))", "(g ((as const (Array Real Int)) 0))"
        overloaded = ("(declare-fun g ((Array Int Int)) Real)(declare-fun g ((Array Real Int)) Real)"
                      "(assert (= (* %s %s) 2))(assert (= (* %s %s %s %s) 5))"
                      % (int_term, real_term, int_term, real_term, int_term, real_term))
        result = self.run_checker(overloaded, "--readable")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        conclusion = self.conclusion(result.stderr)
        ids = {domain: re.search(r"\(g#(\d+):Real \(const:\(Array %s Int\) 0\)\)" % domain, conclusion)
               for domain in ("Int", "Real")}
        self.assertTrue(all(ids.values()), conclusion)
        self.assertNotEqual(ids["Int"].group(1), ids["Real"].group(1))

    @staticmethod
    def pigeonhole(n=20):
        """Unsatisfiable, and far beyond a 1 ms solver budget: the same instance as test_timeout_is_not_certified_unsat."""
        terms = ["(declare-const p%d_%d Bool)" % (i, j) for i in range(n) for j in range(n - 1)]
        terms.extend("(assert (or %s))" % " ".join("p%d_%d" % (i, j) for j in range(n - 1)) for i in range(n))
        terms.extend("(assert (or (not p%d_%d) (not p%d_%d)))" % (i, j, k, j)
                     for j in range(n - 1) for i in range(n) for k in range(i))
        return "\n".join(terms)

    @staticmethod
    def observed(result):
        return result.returncode, result.stdout, result.stderr

    def test_unknown_results_and_timeouts_have_no_block_and_keep_the_protocol(self):
        # An UNKNOWN answer has no proof, so there is nothing to render: the flag changes neither stdout, the exit status nor stderr.
        source = self.pigeonhole()
        runs = [self.run_checker(source, *flags, "--timeout-ms", "1") for flags in ((), ("--diagnostics",), ("--readable",))]
        self.assertEqual(runs[0].returncode, 5, runs[0].stdout + runs[0].stderr)
        self.assertRegex(runs[0].stdout, r"^UNKNOWN .*timeout")
        self.assertEqual(runs[0].stderr, "")
        for run in runs[1:]:
            self.assertEqual(self.observed(run), self.observed(runs[0]))
        # interactive: a solver timeout and a tactic that gives up are both plain `unknown` replies, with no block either
        for script, args in ((source + "(check-sat)", ("--timeout-ms", "1")),
                             ("(declare-const p Bool)(assert p)(check-sat-using skip)", ())):
            with self.subTest(script=script[-24:], args=args):
                plain = self.run_checker(script, "--interactive", *args)
                readable = self.run_checker(script, "--interactive", "--readable", *args)
                self.assertEqual(self.observed(readable), self.observed(plain))
                self.assertEqual(plain.returncode, 0, plain.stdout + plain.stderr)
                self.assertEqual(plain.stdout, "unknown\n")
                self.assertEqual(plain.stderr, "")

    def test_a_query_without_a_proof_does_not_consume_a_query_number(self):
        # Queries are numbered like the `; proof-check` lines: the 2nd proof is query 2 even when an UNKNOWN reply lies between.
        script = ("(declare-const x Real)"
                  "(push)(assert (= (* x x) 2))(assert (= (* x x x) 3))(check-sat)(pop)"
                  "(push)(assert (> x 0))(check-sat-using skip)(pop)"
                  "(push)(assert (= (* x x) 3))(assert (= (* x x x x) 5))(check-sat)(pop)")
        plain = self.run_checker(script, "--interactive", "--diagnostics")
        readable = self.run_checker(script, "--interactive", "--readable")
        self.assertEqual(readable.returncode, 3, readable.stdout + readable.stderr)
        self.assertEqual((readable.returncode, re.sub(r"(?m)^; proof-stats .*\n?", "", readable.stdout)),
                         (plain.returncode, re.sub(r"(?m)^; proof-stats .*\n?", "", plain.stdout)))
        self.assertEqual(readable.stdout.count("unknown\n"), 1, readable.stdout)
        verdicts = re.findall(r"(?m)^; proof-check (.*)$", readable.stdout)
        self.assertEqual(len(verdicts), 2, readable.stdout)
        headers = re.findall(r"(?m)^readable\tquery=(\d+)\tverdict=(.*?)\tpending=", readable.stderr)
        self.assertEqual(headers, [("1", verdicts[0]), ("2", verdicts[1])], readable.stderr)
        # each block follows the machine row of its own query and agrees with it (the two proofs may differ between runs of the OCaml
        # checker, so the rows are compared within the readable run, not with the run without the flag)
        rows = [line for line in readable.stderr.splitlines() if line.startswith(("diagnostic\tchecked\t", "readable\tquery="))]
        self.assertEqual(len(rows), 4, readable.stderr)
        for diagnostic, header in zip(rows[0::2], rows[1::2]):
            counts = re.fullmatch(r"diagnostic\tchecked\t(pending=\d+)\t(families=\d+)", diagnostic)
            self.assertTrue(counts, diagnostic)
            self.assertRegex(header, r"\t%s\t%s\t" % counts.groups())

    def test_errors_and_malformed_input_are_unchanged_by_the_flag(self):
        # A REJECT verdict is reserved for a malformed proof document and no SMT-LIB input produces one (the reports in the repository
        # and the replayed F* corpus contain none); the rejected-document report is therefore covered by the unit-level goldens (bridge tests
        # readable-obligation-diagnostics and readable-edge-conditions, tests.cpp readable_edge_cases). Parse errors, protocol errors and
        # unusable arguments reach the driver before any proof is rendered: stdout, exit status and stderr must be exactly the flag-less ones.
        for source, args in (("(assert missing)", ()),
                             ("(assert", ()),
                             ('{"format":"resolution-v1","root":0}', ()),
                             ("(assert false)", ("--timeout-ms", "not-a-number")),
                             ("(assert false)", ("--timeout-ms", "4294967296")),
                             ("(assert false)", ("--smt2",)),
                             ("", ("--interactive", "unused.smt2")),
                             ("(assert", ("--interactive",)),
                             ('(echo "unfinished', ("--interactive",)),
                             ("(assert |unfinished", ("--interactive",))):
            with self.subTest(source=source, args=args):
                plain = self.run_checker(source, *args)
                readable = self.run_checker(source, "--readable", *args)
                self.assertEqual(plain.returncode, 2, plain.stdout + plain.stderr)
                self.assertTrue(plain.stderr.strip())
                self.assertEqual(self.observed(readable), self.observed(plain))
                self.assertNotIn("readable\t", readable.stderr)

    def test_an_interactive_command_error_leaves_the_stdout_protocol_and_numbers_the_next_proof(self):
        script = "(set-option :produce-proofs false)(assert missing)(assert false)(check-sat)"
        plain = self.run_checker(script, "--interactive", "--diagnostics")
        readable = self.run_checker(script, "--interactive", "--readable")
        self.assertEqual(plain.returncode, 2, plain.stdout + plain.stderr)
        self.assertIn("(error", plain.stdout)
        self.assertEqual((readable.returncode, re.sub(r"(?m)^; proof-stats .*\n?", "", readable.stdout)),
                         (plain.returncode, re.sub(r"(?m)^; proof-stats .*\n?", "", plain.stdout)))
        self.assertTrue(readable.stderr.startswith(plain.stderr), readable.stderr)
        self.assertEqual(readable.stderr[len(plain.stderr):],
                         "readable\tquery=1\tverdict=ACCEPT\tpending=0\tfamilies=0\tshown=0\n"
                         "readable\tend\tquery=1\n")

    def test_help_lists_the_flag(self):
        result = self.run_checker("", "--help")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertRegex(result.stdout, r"--readable\b")
        self.assertIn("--diagnostics", result.stdout)


class ReadableTagTests(unittest.TestCase):
    def test_cherry_renderer_uses_the_bit_vector_numeral_tag_of_the_f_star_source(self):
        # The extracted Cherry checker exports the datatype and rational tags, not this one.
        root = Path(__file__).resolve().parent.parent
        tag = re.search(r"let op_numeral : decl_kind = (\d+)",
                        (root / "Z3BvLemma.fst").read_text(encoding="utf-8")).group(1)
        header = (root / "cherry_runtime" / "readable.h").read_text(encoding="utf-8")
        self.assertRegex(header, r"bv_numeral_op\(\) \{ return CHERRY_INT_SMALL\(%s\); \}" % tag)

    def test_the_printers_cannot_call_the_checker(self):
        # --readable renders the diagnostic the one diagnosed check produced; a second check would double the work and could not be
        # told from the first by a verdict. The printers (OCaml Readable module, Cherry readable.h and readable_report) never reference
        # a checking or marshaling entry point, and each driver has exactly one diagnosed-check call site.
        root = Path(__file__).resolve().parent.parent
        header = (root / "cherry_runtime" / "readable.h").read_text(encoding="utf-8")
        main = (root / "cherry_runtime" / "main.cpp").read_text(encoding="utf-8")
        report = main[main.index("static std::string readable_report("):main.index("struct Report {")]
        for text in (header, report):
            self.assertNotRegex(text, r"Z3Cherry_(check|diagnose|marshal)\b")
        self.assertEqual(len(re.findall(r"Z3Cherry_diagnose\(", main)), 1)
        self.assertEqual(len(re.findall(r"Z3Cherry_check\(", main)), 1)
        ocaml = (root / "ocaml_runtime" / "Z3NativeMain.ml").read_text(encoding="utf-8")
        printer = ocaml[ocaml.index("module Readable = struct"):ocaml.index("let check_proof ")]
        self.assertNotRegex(printer, r"check_document|diagnose_document|check_proof|Z3SortedProof|Z3NativeProof")
        self.assertEqual(len(re.findall(r"check_document_diagnosed", ocaml)), 2)
        self.assertEqual(len(re.findall(r"Readable\.report\b", ocaml)), 1)


if __name__ == "__main__":
    unittest.main()
