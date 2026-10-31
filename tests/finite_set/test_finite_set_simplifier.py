import os
import shutil
import subprocess
import unittest

from finite_set_simplifier import FiniteSetSimplifier
from sleec import Translator, emit, parse


CVC5 = os.environ.get("CVC5") or shutil.which("cvc5")


class FiniteSetSimplifierTests(unittest.TestCase):
    declarations = """
        (declare-datatypes ((Time 0)) (((mk-time (time-value Int)))))
        (declare-const s (FiniteSet Time))
        (declare-const t Int)
        (declare-const b Bool)
    """

    def simplify(self, declarations, formula):
        commands = parse(declarations + f"(assert {formula})")
        simplifier = FiniteSetSimplifier()
        result = simplifier.simplify(commands)
        return result[-1][1], simplifier.stats

    def test_point_interval_becomes_membership(self):
        formula = """(not (= (set.filter (lambda ((x Time))
            (and (>= (time-value x) (+ t 0)) (<= (time-value x) t))) s)
            (as set.empty (FiniteSet Time))))"""
        result, stats = self.simplify(self.declarations, formula)
        self.assertEqual(result, ["set.in", ["mk-time", "t"], "s"])
        self.assertEqual(stats["fixed_point"], 1)

    def test_nonzero_interval_and_partial_record_are_not_points(self):
        for declarations, sort, field in [
            (self.declarations, "Time", "time-value"),
            (self.declarations + """
             (declare-datatypes ((Record 0)) (((mk-record (key Int) (flag Bool)))))
             (declare-const records (FiniteSet Record))""", "Record", "key"),
        ]:
            domain = "s" if sort == "Time" else "records"
            hi = "(+ t 1)" if sort == "Time" else "t"
            formula = f"""(not (= (set.filter (lambda ((x {sort}))
                (and (>= ({field} x) t) (<= ({field} x) {hi}))) {domain})
                (as set.empty (FiniteSet {sort}))))"""
            result, stats = self.simplify(declarations, formula)
            self.assertIn("set.filter", emit(result))
            self.assertEqual(stats["fixed_point"], 0)

    def test_unused_binder_preserves_emptiness_guard(self):
        all_formula = "(= (set.filter (lambda ((x Time)) b) s) s)"
        some_formula = """(not (= (set.filter (lambda ((x Time)) b) s)
                            (as set.empty (FiniteSet Time))))"""
        all_result, _ = self.simplify(self.declarations, all_formula)
        some_result, _ = self.simplify(self.declarations, some_formula)
        self.assertEqual(emit(all_result), "(or (= s (as set.empty (FiniteSet Time))) b)")
        self.assertEqual(emit(some_result), "(and (not (= s (as set.empty (FiniteSet Time)))) b)")

    def test_real_bound_is_not_used_as_integer_record_field(self):
        declarations = self.declarations + "(declare-const r Real)"
        for bound in ("r", "0.5"):
            formula = f"""(not (= (set.filter (lambda ((x Time))
                (and (>= (time-value x) {bound}) (<= (time-value x) {bound}))) s)
                (as set.empty (FiniteSet Time))))"""
            result, stats = self.simplify(declarations, formula)
            self.assertIn("set.filter", emit(result))
            self.assertEqual(stats["fixed_point"], 0)

    def test_overloaded_function_result_is_not_guessed(self):
        declarations = self.declarations + """
            (declare-fun f (Int) Real)
            (declare-fun f (Bool) Int)
        """
        formula = """(not (= (set.filter (lambda ((x Time))
            (and (>= (time-value x) (f 0)) (<= (time-value x) (f 0)))) s)
            (as set.empty (FiniteSet Time))))"""
        result, stats = self.simplify(declarations, formula)
        self.assertIn("set.filter", emit(result))
        self.assertEqual(stats["fixed_point"], 0)

    def test_substitution_renames_captured_binder(self):
        declarations = """
            (declare-const s (FiniteSet Int))
            (declare-const u (FiniteSet Int))
            (declare-const y Int)
        """
        formula = """(not (= (set.filter (lambda ((x Int))
            (and (= x y) (not (= (set.filter (lambda ((y Int)) (> y x)) u)
                (as set.empty (FiniteSet Int)))))) s)
            (as set.empty (FiniteSet Int))))"""
        result, stats = self.simplify(declarations, formula)
        self.assertIn("(lambda ((__fspp_1 Int)) (> __fspp_1 y))", emit(result))
        self.assertIn("(set.in y s)", emit(result))
        self.assertEqual(stats["fixed_point"], 1)

    def test_quoted_alias_is_not_mistaken_for_unused_binder(self):
        formula = """(= (set.filter (lambda ((x Time)) (> (time-value |x|) t)) s) s)"""
        result, stats = self.simplify(self.declarations, formula)
        self.assertIn("set.filter", emit(result))
        self.assertEqual(stats["unused_binder"], 0)

    def test_independent_existential_guard_is_factored(self):
        formula = """(not (= (set.filter (lambda ((x Time))
            (and b (>= (time-value x) t))) s) (as set.empty (FiniteSet Time))))"""
        result, stats = self.simplify(self.declarations, formula)
        self.assertIn("(lambda ((x Time)) (>= (time-value x) t))", emit(result))
        self.assertEqual(stats["independent_guard"], 1)

    def test_translator_opt_in_and_idempotence(self):
        source = """
            (declare-const s (Set (Tuple Int)))
            (assert (set.some (lambda ((x (Tuple Int)))
                (and (>= ((_ tuple.select 0) x) 0)
                     (<= ((_ tuple.select 0) x) 0))) s))
            (check-sat)
        """
        default = Translator().translate(parse(source))
        prototype = Translator(simplify_finite_sets=True).translate(parse(source))
        self.assertIn("set.filter", default)
        self.assertNotIn("set.filter", prototype)
        self.assertIn("(set.in (__sleec_T0_mk 0) s)", prototype)
        again = FiniteSetSimplifier().simplify(parse(prototype))
        self.assertEqual(prototype, "\n".join(map(emit, again)) + "\n")
        self.assertIn("(FiniteSet __sleec_T0)", prototype)

    @unittest.skipUnless(CVC5, "set CVC5 to enable independent equivalence checks")
    def test_reference_equivalences(self):
        point = """(and (>= (time-value x) (+ t 0)) (<= (time-value x) t))"""
        point_extra = f"(and {point} b (<= (time-value x) (+ t 1)))"
        cases = []
        for body in ("b", "true", "false", point, point_extra):
            filtered = f"(set.filter (lambda ((x Time)) {body}) s)"
            cases.extend([
                (self.declarations, f"(= {filtered} s)"),
                (self.declarations, f"(not (= {filtered} (as set.empty (FiniteSet Time))))"),
            ])
        cases.extend([
            (self.declarations,
             "(= (set.filter (lambda ((x Time)) (=> b (> (time-value x) t))) s) s)"),
            (self.declarations,
             """(not (= (set.filter (lambda ((x Time)) (and b (>= (time-value x) t))) s)
                 (as set.empty (FiniteSet Time))))"""),
            (self.declarations,
             """(not (= (set.filter (lambda ((x Time)) (= (time-value x) t))
                  (as set.empty (FiniteSet Time))) (as set.empty (FiniteSet Time))))"""),
            (self.declarations,
             """(= (set.filter (lambda ((x Time))
                (not (= (set.filter (lambda ((y Time))
                    (= (time-value y) (time-value x))) s)
                    (as set.empty (FiniteSet Time))))) s) s)"""),
            (self.declarations,
             """(not (= (set.filter (lambda ((x Time))
                (and (= (time-value x) t)
                    (= (set.filter (lambda ((y Time)) (>= (time-value y) (time-value x))) s) s))) s)
                (as set.empty (FiniteSet Time))))"""),
        ])
        declarations = """
            (declare-const s (FiniteSet Int)) (declare-const u (FiniteSet Int))
            (declare-const y Int)
        """
        for body in [
            """(and (= x y) (not (= (set.filter (lambda ((y Int)) (> y x)) u)
                                    (as set.empty (FiniteSet Int)))))""",
            "(and (= x y) (let ((y x)) (> y 0)))",
            "(and (= x y) (not (= (set.filter (lambda ((x Int)) (> x 0)) u)"
            " (as set.empty (FiniteSet Int)))))",
            "(and (= x y) (= x (+ y 1)))",
        ]:
            cases.append((declarations,
                          f"(not (= (set.filter (lambda ((x Int)) {body}) s)"
                          " (as set.empty (FiniteSet Int))))"))
        for declarations, formula in cases:
            with self.subTest(formula=formula):
                result, _ = self.simplify(declarations, formula)
                query = ("(set-logic HO_ALL)(set-option :sets-exp true)"
                         + declarations + f"(assert (not (= {formula} {emit(result)})))(check-sat)")
                query = query.replace("FiniteSet", "Set").replace("(set.in ", "(set.member ")
                proc = subprocess.run(
                    [CVC5, "--lang=smt2", "--tlimit=5000"],
                    input=query, capture_output=True, text=True, timeout=7)
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                self.assertEqual(proc.stdout.strip(), "unsat", proc.stdout + proc.stderr)


if __name__ == "__main__":
    unittest.main()
