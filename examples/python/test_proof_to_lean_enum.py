############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for enumeration datatypes (declare-datatype(s) with nullary
# constructors only) in the Lean reconstruction. An enumeration is one more
# sort of the carrier _m.U: its constructors are the family _m.ctors, and
# the interpretation states that two constructors of one enumeration differ
# (enum_distinct) and that every constant and function value of the sort is
# one of them (enum_cases_i, enum_fcases_j). The clause log's datatype hints
# (the datatype solver's case splits) are proved by grind from those fields.
# Validation without Lean, and end-to-end checks through the clause-log core
# that need the z3 executable and the pinned Lean toolchain.
############################################
import copy
from pathlib import Path
import random
import sys
import tempfile
import unittest

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
import lean_test_support
import proof_to_lean
from test_proof_to_lean_lia import _STANDARD_AXIOMS, _hints, _z3_available

_COLOR = "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"

# Documented inputs: each refutation needs what an enumeration is, its
# constructors being distinct, its values being among them, or both.
ENUM_INPUTS = {
    # Four pairwise distinct values of a three-constructor enumeration. Z3
    # used to refute a root distinct with more arguments than the sort has
    # values by an empty clause with an empty tseitin hint, which crashed the
    # clause log; with proofs it now adds the pairwise disequalities and the
    # datatype solver's case splits refute them.
    "pigeonhole": _COLOR + """(declare-const a Color)
(declare-const b Color)
(declare-const c Color)
(declare-const d Color)
(assert (distinct a b c d))
(check-sat)
""",
    # A value that is none of the constructors (exhaustiveness alone).
    "none_of_the_constructors": _COLOR + """(declare-const a Color)
(assert (not (= a red)))
(assert (not (= a green)))
(assert (not (= a blue)))
(check-sat)
""",
    # Two constructors are distinct (blue is never mentioned, yet its
    # constructor is part of the encoding).
    "constructor_clash": _COLOR + """(declare-const a Color)
(assert (= a red))
(assert (= a green))
(check-sat)
""",
    # A function into the enumeration takes four distinct values: the
    # exhaustiveness of its results over every argument list (enum_fcases).
    "function_into_enumeration": _COLOR + """(declare-sort U 0)
(declare-fun f (U) Color)
(declare-const x U)
(declare-const y U)
(declare-const z U)
(declare-const w U)
(assert (distinct (f x) (f y) (f z) (f w)))
(check-sat)
""",
    # A transition function over a state enumeration: two steps from any
    # state but idle reach done.
    "state_machine": """(declare-datatype State ((idle) (busy) (done)))
(declare-fun next (State) State)
(declare-const s0 State)
(declare-const s1 State)
(declare-const s2 State)
(assert (= (next idle) busy))
(assert (= (next busy) done))
(assert (= (next done) done))
(assert (= s1 (next s0)))
(assert (= s2 (next s1)))
(assert (not (= s2 done)))
(assert (not (= s0 idle)))
(check-sat)
""",
    # An enumeration next to Int arithmetic (qf_uflia): a level per mode.
    "mode_levels": """(declare-datatype Mode ((off) (low) (high)))
(declare-fun level (Mode) Int)
(declare-const m Mode)
(declare-const k Int)
(assert (= (level off) 0))
(assert (= (level low) 1))
(assert (= (level high) 2))
(assert (= k (level m)))
(assert (> k 2))
(check-sat)
""",
    # Two enumerations, one the result of a function over the other.
    "two_enumerations": _COLOR + """(declare-datatype Bit ((zero) (one)))
(declare-fun g (Color) Bit)
(declare-const a Color)
(declare-const b Color)
(declare-const c Color)
(assert (distinct (g a) (g b)))
(assert (distinct (g b) (g c)))
(assert (distinct (g a) (g c)))
(check-sat)
""",
    # z3test regressions/smt2/t198.smt2: recognizers, ((_ is A) x) is (= x A),
    # in the SMT-LIB 2.5 declaration syntax.
    "recognizers": """(declare-datatypes () ((T A B)))
(declare-const x T)
(assert ((_ is A) x))
(assert ((_ is B) x))
(check-sat)
""",
    # Recognizers and an equality over an application, a case split away.
    "recognizer_split": _COLOR + """(declare-fun f (Color) Color)
(declare-const a Color)
(assert (not ((_ is red) (f a))))
(assert (not ((_ is green) (f a))))
(assert (not (= (f a) blue)))
(check-sat)
""",
    # SMT-LIB 2.5's is-c recognizers (a declaration of their own in Z3, which
    # the clause log prints as (_ is c)).
    "old_style_recognizers": """(declare-datatypes () ((T A B C)))
(declare-fun f (T) T)
(declare-const x T)
(assert (is-A (f x)))
(assert (not (= (f x) A)))
(assert (or (is-B x) (is-C x)))
(assert (= (f x) x))
(check-sat)
""",
    # A one-constructor enumeration has a single value.
    "single_constructor": """(declare-datatype One ((only)))
(declare-const a One)
(declare-const b One)
(assert (not (= a b)))
(check-sat)
""",
    # An enumeration next to an uninterpreted predicate and an ite over the
    # enumeration: whichever branch is taken, P holds of a constructor.
    "predicate_and_ite": _COLOR + """(declare-fun P (Color) Bool)
(declare-const c Color)
(declare-const p Bool)
(assert (P red))
(assert (P green))
(assert (P blue))
(assert (not (P (ite p c red))))
(check-sat)
""",
}


# z3test regressions/smt2/z3.14.smt2: the second query, four distinct values
# of a three-constructor enumeration, crashed the clause log (see pigeonhole).
Z3_14 = """(set-option :auto-config true)
(set-option :produce-models true)

(declare-datatypes () ((S A B C)))
(declare-const x S)
(declare-const y S)
(declare-const z S)
(declare-const u S)
(assert (distinct x y z))
(check-sat)
(assert (distinct x y z u))
(check-sat)
"""


def random_enum_instance(seed, variables=3, constraints=12, depth=2, integer=False):
    """A random input over two enumerations, an uninterpreted sort, and (with integer) Int, or None if sat.

    Color (three constructors) and Bit (two) constants, functions between
    them and from the sort (f, g, h), a predicate (P), Boolean constants,
    ite terms over Color, recognizers, and with integer a function from
    Color into Int compared with an Int constant.
    """
    rng = random.Random(seed)
    lines = ["(set-logic ALL)",
             "(declare-datatypes ((Color 0)) (((red) (green) (blue))))",
             "(declare-datatype Bit ((zero) (one)))",
             "(declare-sort U 0)", "(declare-const u U)", "(declare-const v U)",
             "(declare-const p Bool)", "(declare-const q Bool)"]
    lines += ["(declare-const c%d Color)" % i for i in range(variables)]
    lines += ["(declare-const b%d Bit)" % i for i in range(variables)]
    lines += ["(declare-fun f (Color) Color)", "(declare-fun g (U) Color)", "(declare-fun h (Color Bit) Bit)",
              "(declare-fun P (Color) Bool)"]
    if integer:
        lines += ["(declare-fun level (Color) Int)", "(declare-const n Int)"]

    def condition():
        return rng.choice(["p", "q", "(P %s)" % color(0), "(= %s %s)" % (bit(0), bit(0))])

    def color(d=depth):
        roll = rng.random()
        if d == 0 or roll < 0.35:
            return "c%d" % rng.randrange(variables)
        if roll < 0.55:
            return rng.choice(["red", "green", "blue"])
        if roll < 0.75:
            return "(f %s)" % color(d - 1)
        if roll < 0.85:
            return "(g %s)" % rng.choice(["u", "v"])
        return "(ite %s %s %s)" % (condition(), color(d - 1), color(d - 1))

    def bit(d=depth):
        roll = rng.random()
        if d == 0 or roll < 0.4:
            return "b%d" % rng.randrange(variables)
        if roll < 0.6:
            return rng.choice(["zero", "one"])
        return "(h %s %s)" % (color(d - 1), bit(d - 1))

    def atom():
        roll = rng.random()
        if roll < 0.4:
            return "(= %s %s)" % (color(), color())
        if roll < 0.55:
            return "(distinct %s %s %s)" % (color(), color(), color())
        if roll < 0.7:
            return "(= %s %s)" % (bit(), bit())
        if roll < 0.75:
            return "(P %s)" % color()
        if roll < 0.8:
            return "((_ is %s) %s)" % (rng.choice(["red", "green", "blue"]), color())
        if integer and roll < 0.9:
            return "(%s (level %s) %s)" % (rng.choice(["<=", "<", "="]), color(),
                                           rng.choice(["n", "0", "1", "(+ n 1)"]))
        return rng.choice(["p", "q", "(= u v)"])

    def formula():
        roll = rng.random()
        if roll < 0.5:
            return atom()
        if roll < 0.8:
            return "(or %s %s)" % (atom(), atom())
        return "(not %s)" % atom()

    lines += ["(assert %s)" % formula() for _ in range(constraints)]
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("timeout", 10000)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Pinned unsatisfiable seeds over recognizers, ite terms, and applications:
# (keyword arguments, seed). On iteration 67's macOS build, 24, 125, and 181
# (and 133 with integer) failed before the datatype lemma took the logged
# clause (the hint states (= c0 blue) for the logged (= blue c0)), and 89
# and 110 of the small configuration failed Lean before the replay's keys
# told constructors apart ((= x red) and (= x blue) shared a key). Which
# hints a seed's log carries depends on Z3's search, so only verification is
# asserted.
_SMALL = {"variables": 2, "constraints": 6}
ENUM_SEEDS = (({}, 24), ({}, 125), ({}, 181), ({"integer": True}, 133), ({"integer": True}, 150),
              (_SMALL, 89), (_SMALL, 110))


def _statement(text):
    return text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]


def _structure(text):
    return text.split("structure Interpretation where\n", 1)[1].split("\n\n", 1)[0]


class TestEnumerationExport(unittest.TestCase):
    """The frontend, the classification, and the clause log, without Lean."""

    def test_enumerations_are_sorts_of_the_uf_fragments(self):
        for name, fragment in (("constructor_clash", "qf_uf"), ("state_machine", "qf_uf"),
                               ("mode_levels", "qf_uflia"), ("recognizers", "qf_uf"),
                               ("old_style_recognizers", "qf_uf")):
            with self.subTest(name=name):
                _, found = proof_certificate.parse_assertions(ENUM_INPUTS[name], z3.Context(), integer=True)
                self.assertEqual(found, fragment)

    def test_other_datatypes_are_rejected(self):
        cases = {
            "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n(declare-const x L)\n"
            "(assert (not (= x nil)))\n(assert (= x nil))": "only enumeration datatypes",
            "(declare-datatypes ((E 1)) ((par (T) ((e1) (e2)))))\n(declare-const x (E Int))\n"
            "(assert (= x (as e1 (E Int))))": "parametric datatypes are not supported",
            # SMT-LIB 2.5 lists the parameters first, without par.
            "(declare-datatypes (T) ((E A B)))\n(declare-const x (E Int))\n"
            "(assert (= x (as B (E Int))))": "parametric datatypes are not supported",
            "(declare-datatypes ((P 0)) (((pair (fst Int) (snd Int)))))\n(declare-const x P)\n"
            "(assert ((_ is pair) x))": "only enumeration datatypes",
            # An accessor into an enumeration: the record is not one.
            _COLOR + "(declare-datatypes ((P 0)) (((mk (fst Color)))))\n(declare-const p P)\n"
            "(assert (= (fst p) red))": "only enumeration datatypes",
            # Arrays over an enumeration (the constant-array and default-value
            # axioms assume an infinite index sort; none of it is encoded).
            _COLOR + "(declare-const a (Array Color Int))\n"
            "(assert (not (= (select (store a red 1) red) 1)))": "unsupported sort",
            # A pigeonhole over eight constructors: with proofs Z3 searches it
            # exponentially (see _PIGEONHOLE_MAX_CONSTRUCTORS).
            "(declare-datatypes () ((E c0 c1 c2 c3 c4 c5 c6 c7)))\n"
            + "".join("(declare-const v%d E)\n" % i for i in range(9))
            + "(assert (distinct %s))" % " ".join("v%d" % i for i in range(9)):
            "pigeonhole search under proofs",
        }
        for source, message in cases.items():
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    proof_certificate.parse_assertions(source + "\n(check-sat)\n", z3.Context(), integer=True)

    def test_pigeonholes_up_to_seven_constructors_are_accepted(self):
        source = ("(declare-datatypes () ((E c0 c1 c2 c3 c4 c5 c6)))\n"
                  + "".join("(declare-const v%d E)\n" % i for i in range(32))
                  + "(assert (distinct %s))\n(check-sat)\n" % " ".join("v%d" % i for i in range(32)))
        _, found = proof_certificate.parse_assertions(source, z3.Context(), integer=True)
        self.assertEqual(found, "qf_uf")

    def test_the_legacy_core_rejects_enumerations_explicitly(self):
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "through the clause log only"):
            proof_certificate.export_certificate(ENUM_INPUTS["constructor_clash"])

    def test_replay_keys_tell_constructors_apart(self):
        # The structural key of an atom names its constructors and the
        # constructor of a recognizer; (= x red) and (= x blue) used to share
        # one, so unit propagation took one for the other.
        context = z3.Context()
        assertions = z3.parse_smt2_string(
            _COLOR + "(declare-const x Color)(assert (= x red))(assert (= x blue))"
                     "(assert ((_ is red) x))(assert ((_ is blue) x))", ctx=context)
        normalizer = proof_clause_log._Normalizer()
        keys = [normalizer.key(assertion) for assertion in assertions]
        self.assertEqual(len(set(keys)), 4)
        # is-red and (_ is red) are two declarations of one predicate.
        old_style = z3.parse_smt2_string(_COLOR + "(declare-const x Color)(assert (is-red x))", ctx=context)[0]
        self.assertEqual(old_style.decl().kind(), z3.Z3_OP_DT_RECOGNISER)
        self.assertEqual(normalizer.key(old_style), keys[2])

    def test_clause_log_reads_recognizers_and_unused_constructors(self):
        context = z3.Context()
        assertions = z3.parse_smt2_string(_COLOR + "(declare-const x Color)(assert ((_ is red) x))", ctx=context)
        terms = proof_clause_log._Terms(context, list(assertions))
        self.assertTrue(terms.build([["_", "is", "red"], "x"]).eq(assertions[0]))
        blue = terms.build("blue")
        self.assertEqual(str(blue), "blue")
        self.assertEqual(blue.decl().kind(), z3.Z3_OP_DT_CONSTRUCTOR)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "unsupported application head"):
            terms.build([["_", "is", "purple"], "x"])

    def test_root_distinct_over_too_few_values_logs_case_splits(self):
        # The C++ fix: with proofs, a root distinct with more arguments than
        # the enumeration has values is clausified pairwise (z3 crashed
        # writing the clause log before), and the datatype solver's case
        # splits refute it.
        if not _z3_available():
            self.skipTest("the z3 executable is required for the clause log")
        commands, _, _ = proof_certificate.query_snapshot(ENUM_INPUTS["pigeonhole"])
        log = proof_clause_log.run_clause_log(proof_certificate.default_z3_executable(), commands)
        self.assertIn("(declare-fun datatype", log)
        self.assertIn("(assume (not ", log)


class TestEnumerationValidation(unittest.TestCase):
    """The encoding and the reconstructor's checks against the input, without Lean."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = ENUM_INPUTS["function_into_enumeration"]
        cls.certificate = proof_certificate.export_clause_log_certificate(cls.source)

    def test_interpretation_states_the_enumeration(self):
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        structure = _structure(text)
        self.assertIn("  ctors : Nat -> U\n", structure)
        self.assertIn("  enum_distinct : (And (Not (ctors 0 = ctors 1)) (And (Not (ctors 0 = ctors 2)) "
                      "(Not (ctors 1 = ctors 2))))", structure)
        self.assertIn("  enum_fcases_0 : forall _args : List U, (Or (funs 0 _args = ctors 0) "
                      "(Or (funs 0 _args = ctors 1) (funs 0 _args = ctors 2)))", structure)
        self.assertIn('-- Enumeration "Color" is part of _m.U with constructors "red", "green", "blue", '
                      '_m.ctors 0 to 2', text)
        self.assertIn('-- Uninterpreted sort "U" is the type _m.U', text)

    def test_unused_constructors_are_part_of_the_cases(self):
        # The assertions of constructor_clash never name blue, but a value
        # of Color may be blue: the cases list every constructor of the
        # input, whether or not the proof names it.
        source = ENUM_INPUTS["constructor_clash"]
        structure = _structure(proof_to_lean.reconstruct(
            source, proof_certificate.export_clause_log_certificate(source)))
        self.assertIn("  enum_cases_0 : (Or (elems 0 = ctors 0) (Or (elems 0 = ctors 1) (elems 0 = ctors 2)))",
                      structure)

    def test_constructors_are_checked_against_the_input(self):
        # The assertions of function_into_enumeration name no constructor, so
        # the proof's constructors are checked against the input's
        # declaration of Color alone.
        tampered = copy.deepcopy(self.certificate)
        constructors = [d for d in tampered["declarations"] if d["kind"] == z3.Z3_OP_DT_CONSTRUCTOR]
        self.assertTrue(constructors)
        constructors[0]["name"] = "purple"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                    "not a constructor of the input's enumeration Color: purple"):
            proof_to_lean.reconstruct(self.source, tampered)
        # Constructors are told apart by name: red for blue changes an assertion.
        source = ENUM_INPUTS["constructor_clash"]
        tampered = proof_certificate.export_clause_log_certificate(source)
        for declaration in tampered["declarations"]:
            if declaration["kind"] == z3.Z3_OP_DT_CONSTRUCTOR and declaration["name"] == "red":
                declaration["name"] = "blue"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not match the original input"):
            proof_to_lean.reconstruct(source, tampered)

    def test_recognizers_are_checked_against_the_input(self):
        source = ENUM_INPUTS["recognizers"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        recognizers = [d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_DT_IS]
        self.assertEqual({d["name"] for d in recognizers}, {"A", "B"})
        for name, message in (("C", "not a constructor of the input's enumeration T: C"),
                              ("B", "do not match the original input")):
            tampered = copy.deepcopy(certificate)
            next(d for d in tampered["declarations"] if d["kind"] == z3.Z3_OP_DT_IS and d["name"] == "A")[
                "name"] = name
            with self.subTest(name=name):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(source, tampered)
        tampered = copy.deepcopy(certificate)
        next(d for d in tampered["declarations"] if d["kind"] == z3.Z3_OP_DT_IS)["domain"] = ["Bool"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid enumeration recognizer"):
            proof_to_lean.reconstruct(source, tampered)

    def test_a_constructor_cannot_change_its_sort(self):
        tampered = copy.deepcopy(self.certificate)
        tampered["declarations"].append({"kind": z3.Z3_OP_DT_CONSTRUCTOR, "name": "red", "domain": [],
                                         "range": "U", "parameters": []})
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unused declaration|two sorts"):
            proof_to_lean.reconstruct(self.source, tampered)

    def test_datatype_lemmas_are_enumeration_clauses(self):
        # none_of_the_constructors is refuted by exhaustiveness alone, which
        # only the datatype solver knows.
        source = ENUM_INPUTS["none_of_the_constructors"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertIn("datatype", _hints(certificate))
        graph = proof_to_lean._validate_graph(source, certificate)
        proof_to_lean._bind_input(source, graph, certificate["fragment"])
        lemma = next(node for node in range(len(graph.nodes))
                     if graph.decl(node).name == "th-lemma" and graph.decl(node).parameters == ("datatype",))
        proof_to_lean._check_th_lemma(graph, lemma)
        # The same lemma over an input whose sort is not an enumeration.
        graph.enumerations.clear()
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "not an enumeration equality"):
            proof_to_lean._check_th_lemma(graph, lemma)


def _check_in_lean(test, source, query=None, certificate=None):
    """Export through the clause log, reconstruct, and kernel-check once; return the certificate."""
    if certificate is None:
        certificate = proof_certificate.export_clause_log_certificate(source, query=query)
    text, report = lean_test_support.check(test, source, certificate)
    test.assertEqual(_statement(text).count("    (_h"), len(certificate["assertions"]))
    test.assertIn("  ctors : Nat -> U\n", _structure(text))
    test.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)
    return certificate


class TestEnumerationLeanIntegration(unittest.TestCase):
    """End-to-end through the clause log: certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_verify(self):
        certificates = {name: proof_certificate.export_clause_log_certificate(source)
                        for name, source in ENUM_INPUTS.items()}
        lean_test_support.prefetch((ENUM_INPUTS[name], certificate) for name, certificate in certificates.items())
        hints = set()
        for name, source in ENUM_INPUTS.items():
            with self.subTest(name=name):
                hints |= _hints(_check_in_lean(self, source, certificate=certificates[name]))
        self.assertIn("datatype", hints)

    def test_z3test_incremental_pigeonhole_verifies(self):
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "sat: no unsat proof exists"):
            proof_certificate.export_clause_log_certificate(Z3_14, query=0)
        _check_in_lean(self, Z3_14, query=1)

    def test_pinned_random_instances_verify(self):
        sources = []
        for arguments, seed in ENUM_SEEDS:
            source = random_enum_instance(seed, **arguments)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            sources.append((arguments, seed, source, proof_certificate.export_clause_log_certificate(source)))
        lean_test_support.prefetch((source, certificate) for _, _, source, certificate in sources)
        for arguments, seed, source, certificate in sources:
            with self.subTest(seed=seed, options=sorted(arguments)):
                _check_in_lean(self, source, certificate=certificate)

    def test_a_dropped_enumeration_fact_fails_lean(self):
        # The datatype lemma of none_of_the_constructors rests on the cases
        # field: without it Lean rejects the file, so the facts are needed
        # and not decoration.
        source = ENUM_INPUTS["none_of_the_constructors"]
        text = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source))
        self.assertIn("  have _ec", text)
        tampered = "\n".join(line for line in text.split("\n") if not line.startswith("  have _ec"))
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "tampered.lean"
            output.write_text(tampered)
            result = lean_test_support.run_check_lean(output)
        report = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, report)
        errors = [line for line in report.split("\n") if "error:" in line]
        self.assertTrue(errors, report)
        for error in errors:
            self.assertIn("`grind` failed", error)


if __name__ == "__main__":
    unittest.main()
