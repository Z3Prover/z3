############################################
# Copyright (c) 2026 Microsoft Corporation
#
# End-to-end tests for wide n-ary Boolean connectives: certificates through
# both cores, Lean reconstruction, and kernel checks with the pinned Lean
# toolchain. SMT-LIB benchmarks routinely assert conjunctions and
# disjunctions over hundreds of operands (for example the QF_UF benchmark
# NEQ004_size4 in z3test's smtlib-sample asserts one conjunction of 338
# literals); every operand count Z3 solves must be certified, not only the
# small ones.
############################################
from collections import Counter
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest.mock import patch

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
import lean_test_support
import proof_to_lean
from test_proof_to_lean import make_certificate
from test_proof_to_lean_uf import _z3_available

_STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Above Lean's default maxRecDepth (512) for the right-nested And/Or chain a
# connective of this many operands renders to; each case below is solved by
# Z3 in milliseconds.
WIDTH = 260
# The clause log eliminates every conjunct of an asserted conjunction, so its
# Lean check is the most expensive; this width is already rejected today.
CLAUSE_LOG_CONJUNCTION_WIDTH = 200
# Outlined, the proof steps project the assertions out of one conjunction;
# at this many assertions a right-nested conjunction exhausts maxHeartbeats
# (isDefEq on the chain of 600 projections), a balanced one checks in 20 s.
OUTLINED_WIDTH = 600
# The widest conjunction that is not defined in chunks, and outlined when
# every operand is eliminated: its lemmas bind its tails.
OUTLINED_TAIL_WIDTH = proof_to_lean._CHUNKED_OPERANDS
# Below _OUTLINE_PROOF_STEPS proof steps when every operand is eliminated
# (three per operand), so the steps are checked in the theorem itself.
INLINE_CHAIN_WIDTH = 150
# Its middle operand, the one refuted, lies past the first tail.
LOCAL_TAIL_WIDTH = 80


def wide_conjunction(width):
    """(and p0 ... p(n-1)) refuted by the negation of its middle operand."""
    source = "".join("(declare-const p%d Bool)\n" % index for index in range(width))
    source += "(assert (and %s))\n" % " ".join("p%d" % index for index in range(width))
    source += "(assert (not p%d))\n(check-sat)\n" % (width // 2)
    return source


def implication_chain_conjunction(width):
    """(and p0 (=> p0 p1) ... (not p(n-2))): the refutation eliminates every operand."""
    source = "".join("(declare-const p%d Bool)\n" % index for index in range(width - 1))
    operands = ["p0"] + ["(=> p%d p%d)" % (index, index + 1) for index in range(width - 2)]
    source += "(assert (and %s (not p%d)))\n(check-sat)\n" % (" ".join(operands), width - 2)
    return source


def wide_disjunction(width):
    """(or p0 ... p(n-1)) refuted by one negated unit per operand."""
    source = "".join("(declare-const p%d Bool)\n" % index for index in range(width))
    source += "(assert (or %s))\n" % " ".join("p%d" % index for index in range(width))
    source += "".join("(assert (not p%d))\n" % index for index in range(width))
    return source + "(check-sat)\n"


def shared_units_among_assertions(unused, links=150, uses=6):
    """A chain of clauses whose every unit is used by the next `uses` of them, among `unused` other assertions.

    The shape of the QF_IDL benchmark 20210312-Bouvier/vlsat3_c27 in z3test's
    smtlib-sample, reduced: its refutation uses 579 of 15,332 assertions, and
    its outlined lemmas name one another 316,556 times. Here p0 to p(uses-1)
    are asserted, each clause derives the next unit from the `uses` before
    it, and the last unit is refuted; a unit used more than once is a lemma
    of its own, named by every lemma that uses it. The other assertions,
    fresh atoms, stand before and after the chain.
    """
    source = "".join("(declare-const p%d Bool)\n" % index for index in range(links + uses))
    source += "".join("(declare-const q%d Bool)\n" % index for index in range(unused))
    source += "".join("(assert q%d)\n" % index for index in range(unused // 2))
    source += "".join("(assert p%d)\n" % index for index in range(uses))
    source += "".join("(assert (or %s p%d))\n" % (
        " ".join("(not p%d)" % (index + offset) for offset in range(uses)), index + uses) for index in range(links))
    source += "(assert (not p%d))\n" % (links + uses - 1)
    source += "".join("(assert q%d)\n" % index for index in range(unused // 2, unused))
    return source + "(check-sat)\n"


def wide_uf_conjunction(width):
    """A conjunction of predicate applications over an uninterpreted sort, as in NEQ004_size4."""
    source = "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-fun P (U) Bool)\n"
    source += "".join("(declare-const a%d U)\n" % index for index in range(width))
    source += "(assert (and %s))\n" % " ".join("(P a%d)" % index for index in range(width))
    source += "(assert (not (P a%d)))\n(check-sat)\n" % (width // 2)
    return source


def wide_uf_disjunction(width):
    """A disjunction of equalities over an uninterpreted sort, each refuted by a unit disequality."""
    source = "(set-logic QF_UF)\n(declare-sort U 0)\n"
    source += "".join("(declare-const a%d U)\n(declare-const b%d U)\n" % (index, index) for index in range(width))
    source += "(assert (or %s))\n" % " ".join("(= a%d b%d)" % (index, index) for index in range(width))
    source += "".join("(assert (not (= a%d b%d)))\n" % (index, index) for index in range(width))
    return source + "(check-sat)\n"


def guarded_conjunction(width):
    """(or p (and b0 ... b(n-1))) with p and the last operand refuted.

    Z3 assumes the clause (or p b(n-1)), which the exporter ties to the
    first assertion by a cnf lemma: its proof refutes the conjunction from
    the refutation of its last operand.
    """
    atoms = ["b%d" % index for index in range(width)]
    source = "(set-logic QF_UF)\n(declare-const p Bool)\n"
    source += "".join("(declare-const %s Bool)\n" % atom for atom in atoms)
    source += "(assert (or p (and %s)))\n(assert (or p (not %s)))\n(assert (not p))\n" % (" ".join(atoms), atoms[-1])
    return source + "(check-sat)\n"


def last_operands_conjunction(width):
    """(and b0 ... b(n-1)) refuted by a clause over its last two operands: and-elim of both."""
    atoms = ["b%d" % index for index in range(width)]
    source = "(set-logic QF_UF)\n" + "".join("(declare-const %s Bool)\n" % atom for atom in atoms)
    source += "(assert (and %s))\n(assert (or (not %s) (not %s)))\n" % (" ".join(atoms), atoms[-1], atoms[-2])
    return source + "(check-sat)\n"


def distinct_through_ites(count):
    """A distinct over count constants and two ite terms over its last two, equal under a function.

    The shape of the QF_UF benchmark 2018-Goel-hwbench/QF_UF_sokoban.3.prop1_ab_br_max in
    z3test's smtlib-sample (a distinct over 209 constants, the values of
    ite terms): Z3 does not expand a distinct this wide into its pairs but
    logs, for each equality between two of its constants that it meets, the
    lemma (or (not (distinct ...)) (not (= a b))).
    """
    names = ["c%d" % index for index in range(count)]
    source = "(set-logic QF_UF)\n(declare-sort U 0)\n" + "".join("(declare-const %s U)\n" % name for name in names)
    source += ("(declare-const p Bool)\n(declare-const q Bool)\n(declare-const x U)\n(declare-const y U)\n"
               "(declare-fun f (U) U)\n")
    source += "(assert (distinct %s))\n" % " ".join(names)
    source += "(assert (= x (ite p %s %s)))\n(assert (= y (ite q %s %s)))\n" % (
        names[-1], names[-2], names[-2], names[-1])
    source += "(assert (= (f x) %s))\n(assert (= (f y) %s))\n(assert (= p (not q)))\n" % (names[0], names[1])
    return source + "(check-sat)\n"


def distinct_with_equalities(count):
    """A distinct over count constants and three clauses, each with an equality between two of them.

    Z3 assumes the negated equalities as units, and one cnf lemma ties
    them to the distinct, which it holds true: the proof projects the
    three pairs out of it.
    """
    names = ["c%d" % index for index in range(count)]
    source = "(set-logic QF_UF)\n(declare-sort U 0)\n" + "".join("(declare-const %s U)\n" % name for name in names)
    source += "(declare-const p Bool)\n(declare-const q Bool)\n(assert (distinct %s))\n" % " ".join(names)
    source += "(assert (or p (= %s %s)))\n(assert (or q (= %s %s)))\n" % (names[-2], names[-1], names[-3], names[-1])
    source += "(assert (or (not p) (not q) (= %s %s)))\n" % (names[1], names[-1])
    return source + "(check-sat)\n"


def distinct_with_last_equality(count):
    """A distinct over count constants, and its last two equal."""
    names = ["c%d" % index for index in range(count)]
    source = "(declare-sort U 0)\n" + "".join("(declare-const %s U)\n" % name for name in names)
    return source + "(assert (distinct %s))\n(assert (= %s %s))\n(check-sat)\n" % (
        " ".join(names), names[-2], names[-1])


def boolean_distinct(count):
    """A distinct over count Boolean constants: its pairs are negated equivalences."""
    names = ["b%d" % index for index in range(count)]
    source = "".join("(declare-const %s Bool)\n" % name for name in names)
    return source + "(assert (distinct %s))\n(check-sat)\n" % " ".join(names)


def distinct_or_its_pairs(count):
    """A distinct over count constants or the conjunction of its pairs written out, and its last two equal.

    The two disjuncts are different nodes that read alike: one structure
    to the propositional prover, which refutes it from the last pair.
    """
    names = ["c%d" % index for index in range(count)]
    source = "(set-logic QF_UF)\n(declare-sort U 0)\n" + "".join("(declare-const %s U)\n" % name for name in names)
    pairs = ["(not (= %s %s))" % (left, right) for index, left in enumerate(names) for right in names[index + 1:]]
    source += "(declare-const p Bool)\n(declare-const q Bool)\n"
    source += "(assert (or (and (and %s) p) (and (distinct %s) q)))\n" % (" ".join(pairs), " ".join(names))
    return source + "(assert (= %s %s))\n(check-sat)\n" % (names[-2], names[-1])


def longest_run(text, step):
    """The most consecutive repetitions of step in text."""
    return max((len(run) // len(step) for run in re.findall("(?:%s)+" % re.escape(step), text)), default=0)


def lemma_texts(text):
    """The th_lemma_* theorems of a reconstructed text, each up to the next declaration."""
    return re.findall(r"^private theorem th_lemma_\d+ .*?(?=^\S)", text, flags=re.M | re.S)


class _WideLeanIntegration(unittest.TestCase):
    def export(self, source, core):
        if core == "legacy":
            return proof_certificate.export_certificate(source)
        return proof_certificate.export_clause_log_certificate(source)

    def check(self, source, core, fragment, width=WIDTH):
        """Export, kernel-check once, and return (certificate, axioms of unsat)."""
        certificate = self.export(source, core)
        self.assertEqual(certificate["fragment"], fragment)
        try:
            text, report = lean_test_support.check(self, source, certificate)
        except self.failureException as error:
            raise self.failureException("the %s certificate of a %d-operand connective: %s"
                                        % (core, width, error)) from None
        statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
        self.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
        self.assertNotIn("_hyp", statement)
        if ".unsat' does not depend on any axioms" in report:
            return certificate, set()
        axioms = report.split("depends on axioms: [", 1)[1].split("]", 1)[0]
        return certificate, {name.strip() for name in axioms.split(",")}


class TestWidePropositionalLegacyCore(_WideLeanIntegration):
    """The legacy proof object: propositional refutations stay axiom-free at any width."""

    def test_wide_conjunction_is_checked_without_axioms(self):
        certificate, axioms = self.check(wide_conjunction(WIDTH), "legacy", "propositional")
        self.assertIn("and-elim", certificate["rule_counts"])
        self.assertEqual(axioms, set())

    def test_wide_disjunction_is_checked_without_axioms(self):
        certificate, axioms = self.check(wide_disjunction(WIDTH), "legacy", "propositional")
        self.assertEqual(certificate["rule_counts"]["asserted"], WIDTH + 1)
        self.assertEqual(axioms, set())

    def test_outlined_wide_disjunction_projects_each_assertion_at_logarithmic_depth(self):
        # Outlined, every proof step receives the assertions as one
        # hypothesis, Inputs, and projects assertion k by field notation.
        # Right-nested, the last of the 601 assertions sat under 600
        # projections and elaborating the chain exhausted maxHeartbeats (as
        # it did for z3test's QF_LIA BART-PT-002/RF-00.smt2, 1,211
        # assertions); balanced, no assertion is more than ten deep: five
        # to its chunk of 32 assertions among the 19, five inside it.
        source = wide_disjunction(OUTLINED_WIDTH)
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0):
            certificate, axioms = self.check(source, "legacy", "propositional", OUTLINED_WIDTH)
            text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual(axioms, set())
        self.assertIn("private structure Inputs", text)
        size = proof_to_lean._INPUT_CHUNK
        full, rest = divmod(OUTLINED_WIDTH + 1, size)  # 18 chunks of 32 and one of 25
        self.assertTrue(full and rest)
        chunks = re.findall(r"^private def Inputs_c\d+ .* : Prop := (.*)$", text, re.M)
        self.assertEqual([chunk.count("formula_") for chunk in chunks], [size] * full + [rest])
        field = re.search(r"^private structure Inputs .* : Prop where\n  all : (.*)$", text, re.M).group(1)
        self.assertEqual(re.findall(r"\w+_c?\d+", field), ["Inputs_c%d" % index for index in range(full + 1)])
        paths = re.findall(r"_inputs\.all((?:\.[12])+)", text)
        self.assertEqual(len(paths), text.count("_inputs."))
        self.assertEqual(len(set(paths)), OUTLINED_WIDTH + 1)
        self.assertEqual(max(path.count(".") for path in paths), OUTLINED_WIDTH.bit_length())

    def check_shared_units(self, unused, heartbeats):
        """Check the refutation among `unused` assertions with each outlined lemma under `heartbeats`."""
        source = shared_units_among_assertions(unused)
        certificate = proof_certificate.export_certificate(source)
        self.assertEqual(len(certificate["assertions"]), unused + 157)
        text = proof_to_lean.reconstruct(source, certificate)
        proof_to_lean.modules(text, 0, proof_to_lean._MODULE_SIZE)
        lemmas = re.findall(r"^private theorem proof_step_\d+ .*?(?=^\S)", text, flags=re.M | re.S)
        named = [len(re.findall(r"\bproof_step_\d+ _inputs\b", lemma)) for lemma in lemmas]
        # Every unit derived is a lemma that takes the assertions, names
        # the six before it, and projects its clause out of the assertions.
        self.assertEqual(len(lemmas), 154)
        self.assertEqual(Counter(named).most_common(1), [(6, 148)])
        self.assertEqual(sum(named), 893)
        self.assertTrue(all("    (_inputs : Inputs _atoms)\n" in lemma for lemma in lemmas))
        self.assertEqual(text.count("_inputs.all."), 157)
        self.assertEqual(text.count("_inputs."), 157)
        self.assertEqual(len(re.findall(r"^private def Inputs_c\d+ ", text, re.M)),
                         -(-(unused + 157) // proof_to_lean._INPUT_CHUNK))
        marker = "\nprivate theorem proof_step_"
        limited = text.replace(marker, "\nset_option maxHeartbeats %d in" % heartbeats + marker)
        self.assertEqual(limited.count("\nset_option maxHeartbeats %d in\n" % heartbeats), len(lemmas))
        _, report = lean_test_support.check(self, source, text=limited)
        self.assertIn(".unsat' does not depend on any axioms", report)

    def test_lemmas_naming_one_another_do_not_pay_for_the_assertions(self):
        # Inputs was a definition of the whole conjunction of the assertions,
        # and at every `proof_step_N _inputs` Lean's elaborator unfolded it
        # twice, copying the conjunction: QF_IDL vlsat3_c27 (z3test's
        # smtlib-sample; 15,332 assertions, 316,556 such references) took 26
        # s of Lean for each MB of its 128 MB of lemmas and had no verdict
        # after 40 minutes; with Inputs a structure it verifies in 517 s.
        # Here, among 4,157 assertions: as a definition, more than 100 of the
        # 154 lemmas needed more than 240,000 heartbeats each (maxHeartbeats
        # counts thousands), and some more than 320,000. Now every lemma is
        # within 100,000. Lean's default limit, 200,000 thousand, is far above
        # either: what the limit below pins is that a reference to a lemma
        # no longer costs the assertions.
        self.check_shared_units(4000, 160)

    @lean_test_support.slow("19 s of Lean: 16,157 assertions, most of it the theorem's own binders")
    def test_lemmas_among_sixteen_thousand_assertions_stay_within_their_heartbeats(self):
        # Every lemma within 200,000 heartbeats; as a definition more than
        # 100 of them needed over 800,000 each, four times those of 4,157
        # assertions.
        self.check_shared_units(16000, 400)

    def test_projection_of_another_assertion_is_rejected(self):
        # What a projection out of Inputs proves is checked by Lean: through
        # another chunk, or to its chunk's other half, a step proves another
        # assertion than its type says; and so does the theorem's own proof
        # of Inputs with two hypotheses exchanged. Each is a type mismatch,
        # and the text they are made from is accepted: a text Lean rejected
        # for another reason would not show it.
        source = wide_disjunction(70)
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0):
            text = proof_to_lean.reconstruct(source, proof_certificate.export_certificate(source))
        _, accepted = lean_test_support.check(self, source, text=text)
        self.assertIn(".unsat' does not depend on any axioms", accepted)
        self.assertEqual(len(re.findall(r"^private def Inputs_c\d+ ", text, re.M)), 3)
        (use,) = re.findall(r"\n +_inputs\.all\.1\.2\.1\.1\.1\.1\.1\n", text)
        term = text[text.index("(Inputs.mk "):]
        self.assertIn("(And.intro _h0 _h1)", term)
        mutants = {"another chunk": text.replace(use, use.replace(".all.1.2.", ".all.1.1.")),
                   "another assertion of the chunk": text.replace(use, use.replace(".1\n", ".2\n")),
                   "hypotheses exchanged": text.replace("(And.intro _h0 _h1)", "(And.intro _h1 _h0)")}
        for name, mutant in mutants.items():
            with self.subTest(mutant=name), tempfile.TemporaryDirectory() as directory:
                self.assertNotEqual(mutant, text)
                output = Path(directory) / "mutant.lean"
                output.write_text(mutant)
                result = lean_test_support.run_check_lean(output)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                self.assertTrue(all("mismatch" in line for line in errors), report)

    def check_every_operand_eliminated(self, width, outlined):
        source = implication_chain_conjunction(width)
        certificate, axioms = self.check(source, "legacy", "propositional", width)
        self.assertEqual(certificate["rule_counts"]["and-elim"], width)
        self.assertEqual(axioms, set())
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual("private structure Inputs" in text, outlined)
        # No projection starts more than a stride of operands before its own:
        # a tail is a stride past the one before, and an operand at most a
        # stride minus one past its tail. The tails of a conjunction defined
        # in chunks are its tail theorems, applied to the proof projected.
        stride = proof_to_lean._AND_ELIM_STRIDE
        chunked = width > proof_to_lean._CHUNKED_OPERANDS
        tails = re.findall(r"let _tail_\d+_\d+ := _(?:step_\d+|tail_\d+_\d+)((?:\.2)*)\n", text)
        self.assertEqual({path.count(".") for path in tails}, set() if chunked else {stride})
        start = r"_step_\d+|_tail_\d+_\d+|\(proof_step_\d+ _inputs\)"
        if chunked:
            start += r"|\(formula_\d+_t\d+ _atoms (?:_step_\d+|\(proof_step_\d+ _inputs\))\)"
        projections = re.findall(r"\n    (%s)((?:\.2)*)\.1\n" % start, text)
        self.assertEqual(len(projections), width - 1)
        self.assertEqual(max(path.count(".") for _, path in projections), stride - 1)
        theorems = {int(chunk) for chunk in re.findall(r"\(formula_\d+_t(\d+) _atoms ", "".join(
            source for source, _ in projections))}
        self.assertEqual(theorems, set(range(1, (width + stride - 1) // stride)) if chunked else set())
        return text

    def test_outlined_conjunction_with_every_operand_eliminated_is_checked(self):
        # Each operand was projected from the start of the conjunction, one
        # `.2` per operand before it: an outlined lemma eliminating 250 of
        # 600 operands held 94,000 projections and exhausted maxHeartbeats.
        # Then every lemma bound the rest of the conjunction once per 32
        # operands and projected from the nearest of those tails. This
        # conjunction is defined in chunks, so its tails are theorems and
        # no lemma binds one (QF_IDL parity 13.400: 253 lemmas with 25,553
        # such bindings, three quarters of the file's time in Lean).
        text = self.check_every_operand_eliminated(OUTLINED_WIDTH, outlined=True)
        self.assertNotIn("let _tail_", text)

    def test_outlined_lemmas_bind_the_tails_of_a_conjunction_that_is_not_chunked(self):
        text = self.check_every_operand_eliminated(OUTLINED_TAIL_WIDTH, outlined=True)
        self.assertGreater(text.count("let _tail_"), OUTLINED_TAIL_WIDTH // proof_to_lean._AND_ELIM_STRIDE)

    def test_inline_conjunction_with_every_operand_eliminated_is_checked(self):
        text = self.check_every_operand_eliminated(INLINE_CHAIN_WIDTH, outlined=False)
        self.assertEqual(text.count("let _tail_"), (INLINE_CHAIN_WIDTH - 1) // proof_to_lean._AND_ELIM_STRIDE)

    def test_outlined_lemma_binds_tails_after_a_local_premise(self):
        # A conjunction eliminated once is used once, so its proof is a step
        # of the lemma that eliminates from it rather than a lemma of its
        # own: the tails follow that step inside the lemma.
        source = wide_conjunction(LOCAL_TAIL_WIDTH)
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0):
            certificate, axioms = self.check(source, "legacy", "propositional", LOCAL_TAIL_WIDTH)
            text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual(certificate["rule_counts"]["and-elim"], 1)
        self.assertEqual(axioms, set())
        self.assertIn("private structure Inputs", text)
        tail = re.search(r"\n  let _tail_(\d+)_32 := _step_\1(?:\.2){32}\n", text)
        self.assertIsNotNone(tail)
        premise = tail.group(1)
        self.assertNotIn("proof_step_%s " % premise, text)
        self.assertLess(text.index("\n  let _step_%s : " % premise), tail.start())
        self.assertIn("\n    _tail_%s_32%s.1\n" % (premise, ".2" * (LOCAL_TAIL_WIDTH // 2 - 32)), text)

    def test_and_elim_under_a_hypothesis_starts_from_the_tail_theorems(self):
        # Steps written by hand: no proof of Z3's in these tests eliminates
        # from a chunked conjunction under a hypothesis. The conjunction is
        # the hypothesis itself, which the and-elim names by its binder, or
        # a step that follows from one, whose type is inferred. (A premise
        # under hypotheses used to be projected from its start, one `.2`
        # per operand.)
        stride = proof_to_lean._AND_ELIM_STRIDE
        atoms = ["b%d" % index for index in range(WIDTH)]
        conjunction, operand = "(and %s)" % " ".join(atoms), atoms[-2]
        declarations = "".join("(declare-const %s Bool)" % atom for atom in atoms) + "(declare-const p Bool)"
        guarded = "(assert (or (not p) %s))(assert p)" % conjunction
        cases = [
            ("_hyp\\d+", False, declarations + "(assert (not %s))(assert %s)" % (operand, conjunction), [
                ("hypothesis", [], conjunction),
                ("and-elim", [2], operand),
                ("unit-resolution", [0, 3], "false"),
                ("lemma", [4], "(not %s)" % conjunction),
                ("unit-resolution", [5, 1], "false")]),
            ("_step_\\d+", False, declarations + "(assert (not %s))" % operand + guarded, [
                ("hypothesis", [], "p"),
                ("unit-resolution", [1, 3], conjunction),
                ("and-elim", [4], operand),
                ("unit-resolution", [0, 5], "false"),
                ("lemma", [6], "(not p)"),
                ("unit-resolution", [7, 2], "false")]),
        ]
        # Eliminated twice, the conjunction that follows from the hypothesis
        # is a step of its own, a function of the hypothesis that each
        # and-elim applies inside the theorem's application; outlined, that
        # step is a lemma (the text passes that put the application there
        # rewrite the premise's name inside the parentheses).
        shared = (declarations + "(assert (or (not %s) (not %s)))" % (atoms[-1], operand) + guarded, [
            ("hypothesis", [], "p"),
            ("unit-resolution", [1, 3], conjunction),
            ("and-elim", [4], atoms[-1]),
            ("and-elim", [4], operand),
            ("unit-resolution", [0, 5, 6], "false"),
            ("lemma", [7], "(not p)"),
            ("unit-resolution", [8, 2], "false")])
        cases += [("\\(_step_\\d+ _hyp\\d+\\)", outlined) + shared for outlined in (False, True)]
        for premise, outlined, source, steps in cases:
            with self.subTest(premise=premise, outlined=outlined), \
                    patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS",
                                 0 if outlined else proof_to_lean._OUTLINE_PROOF_STEPS):
                text, _ = lean_test_support.check(self, source, make_certificate(source, steps))
                self.assertNotIn("_tail_", text)
                self.assertEqual("private structure Inputs" in text, outlined)
                imports = re.findall(r"\n  let _step_\d+ := proof_step_\d+ _inputs\n", text)
                self.assertEqual(len(imports), int(outlined))
                self.assertRegex(text, r"\n    \(formula_\d+_t%d _atoms %s\)%s\.1\n" % (
                    (WIDTH - 2) // stride, premise, r"\.2" * ((WIDTH - 2) % stride)))


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestWidePropositionalClauseLog(_WideLeanIntegration):
    """The sat.smt clause log: the replay's theory lemmas and resolution chains over wide clauses."""

    def test_wide_conjunction_is_checked(self):
        # The core splits the conjunction into its conjuncts, and the replay ties
        # them to the assertion by and-elim steps and a th-lemma over the whole
        # conjunction; grind fails on that lemma today.
        source = wide_conjunction(CLAUSE_LOG_CONJUNCTION_WIDTH)
        with patch.object(proof_clause_log, "_TRIM_THRESHOLD", float("inf")):
            certificate, axioms = self.check(source, "clause-log", "propositional", CLAUSE_LOG_CONJUNCTION_WIDTH)
        self.assertEqual(certificate["rule_counts"]["and-elim"], CLAUSE_LOG_CONJUNCTION_WIDTH - 1)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)
        # Trimmed, the default since 2026-10-27, the core is the empty clause
        # Z3 assumes once preprocessing reduces the conjunction against the
        # unit to false (until then the trimmer wrote a cyclic core for it).
        certificate, axioms = self.check(source, "clause-log", "propositional", CLAUSE_LOG_CONJUNCTION_WIDTH)
        self.assertNotIn("and-elim", certificate["rule_counts"])
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)

    def test_wide_disjunction_is_checked(self):
        certificate, axioms = self.check(wide_disjunction(WIDTH), "clause-log", "propositional")
        self.assertEqual(certificate["rule_counts"]["asserted"], WIDTH + 1)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)


class TestWideUninterpretedLegacyCore(_WideLeanIntegration):
    def test_wide_predicate_conjunction_is_checked(self):
        certificate, axioms = self.check(wide_uf_conjunction(WIDTH), "legacy", "qf_uf")
        self.assertIn("and-elim", certificate["rule_counts"])
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestWideUninterpretedClauseLog(_WideLeanIntegration):
    def test_wide_equality_disjunction_is_checked(self):
        certificate, axioms = self.check(wide_uf_disjunction(WIDTH), "clause-log", "qf_uf")
        self.assertEqual(certificate["rule_counts"]["asserted"], WIDTH + 1)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)


def formula_definitions(text):
    """The bodies of the formula definitions of a reconstructed text, by name."""
    return dict(re.findall(r"^def (formula_\w+) .*? : Prop := (.*)$", text, flags=re.M))


def chunked_definitions(definitions):
    """The names of the conjunctions defined in chunks, among the definitions of a text."""
    return [name for name in definitions if name + "_c1" in definitions]


def unfolded(test, definitions, name):
    """The body of a definition with its chunks substituted, each of which the one before names once."""
    body, chunk = definitions[name], 1
    while "%s_c%d" % (name, chunk) in definitions:
        applied = re.findall(r"\(%s_c%d [^()]*\)" % (name, chunk), body)
        test.assertEqual(len(applied), 1, "chunk %d of %s is not named once by the chunks before it" % (chunk, name))
        body = body.replace(applied[0], definitions["%s_c%d" % (name, chunk)])
        chunk += 1
    return body


def reconstruct_written_out(source, certificate):
    """The text with every conjunction written out in its definition, as before the chunks."""
    with patch.object(proof_to_lean, "_CHUNKED_OPERANDS", float("inf")):
        return proof_to_lean.reconstruct(source, certificate)


class TestChunkedConjunctionDefinitions(unittest.TestCase):
    """A conjunction above _CHUNKED_OPERANDS operands is defined in chunks (_formula_definitions)."""

    def test_a_conjunction_above_the_limit_is_defined_in_chunks_that_unfold_to_it(self):
        stride, limit = proof_to_lean._AND_ELIM_STRIDE, proof_to_lean._CHUNKED_OPERANDS
        for width in (limit, limit + 1, limit + stride, 1000):
            source = wide_conjunction(width)
            certificate = proof_certificate.export_certificate(source)
            text = proof_to_lean.reconstruct(source, certificate)
            with patch.object(proof_to_lean, "_CHUNKED_OPERANDS", width):
                whole = proof_to_lean.reconstruct(source, certificate)
            flat, chunked = formula_definitions(whole), formula_definitions(text)
            (name,) = [name for name, body in flat.items() if body.count("(And ") == width - 1]
            chunks = [chunk for chunk in chunked if chunk.startswith(name + "_c")]
            count = (width + stride - 1) // stride if width > limit else 1
            with self.subTest(width=width):
                # Chunk k is written before chunk k - 1, which names it, and all before the conjunction.
                self.assertEqual(chunks, ["%s_c%d" % (name, chunk) for chunk in reversed(range(1, count))])
                self.assertEqual(set(chunked) - set(chunks), set(flat))
                if width <= limit:
                    self.assertEqual(text, whole)
                    continue
                # Every chunk but the last holds a stride of operands and then the next chunk;
                # with the chunks unfolded, the definition is the conjunction written out.
                body = chunked[name]
                for chunk in reversed(chunks):
                    applied = "(%s _atoms)" % chunk
                    self.assertEqual(body.count("(And "), stride)
                    self.assertTrue(body.endswith(applied + ")" * stride), chunk)
                    body = chunked[chunk]
                self.assertEqual(unfolded(self, chunked, name), flat[name])
                # Theorem k proves chunk k from the conjunction by a stride of projections of chunk k - 1.
                theorems = re.findall(r"^theorem (\w+) \(_atoms : Nat -> Prop\) \(_h : \((\w+) _atoms\)\) : "
                                      r"\((\w+) _atoms\) := (.*)$", text, flags=re.M)
                self.assertEqual(theorems, [
                    ("%s_t%d" % (name, chunk), name, "%s_c%d" % (name, chunk),
                     ("_h" if chunk == 1 else "(%s_t%d _atoms _h)" % (name, chunk - 1)) + ".2" * stride)
                    for chunk in range(1, count)])
                # What the proof says of the conjunction is unchanged but for the and-elim of its
                # middle operand: only its definition differs, and the tail the projection starts
                # from is the theorem of the operand's chunk, where the conjunction written out
                # has its tails bound up to there.
                rest = [line for line in text.split("\n")
                        if not re.match(r"(?:def|theorem) %s(?:_[ct]\d+)? " % name, line)]
                written = [line for line in whole.split("\n") if not line.startswith("def %s " % name)]
                self.assertNotIn("let _tail_", text)
                base = width // 2 // stride * stride
                self.assertEqual(sum(line.startswith("  let _tail_") for line in written), base // stride)
                written = [line for line in written if not line.startswith("  let _tail_")]
                self.assertEqual(len(rest), len(written))
                ((chunked_step, written_step),) = [pair for pair in zip(rest, written) if pair[0] != pair[1]]
                path = r"\.2" * (width // 2 - base) + r"\.1"
                self.assertRegex(written_step, r"^    _tail_\d+_%d%s$" % (base, path))
                self.assertRegex(chunked_step, r"^    \(%s_t%d _atoms _step_\d+\)%s$" % (name, base // stride, path))

    def test_a_distinct_and_the_conjunction_of_its_pairs_are_chunked_alike(self):
        # The legacy core relates a distinct to the conjunction of its pairs by two
        # def-axioms; over 24 constants (276 pairs) both are defined in chunks, and the
        # proofs between them project and build the conjunctions through the chunks' names.
        stride = proof_to_lean._AND_ELIM_STRIDE
        source = distinct_with_last_equality(24)
        certificate = proof_certificate.export_certificate(source)
        self.assertIn("def-axiom", certificate["rule_counts"],
                      "the legacy core no longer relates this distinct to the conjunction of its pairs by def-axioms")
        text, report = lean_test_support.check(self, source, certificate)
        self.assertIn(".unsat' does not depend on any axioms", report)
        definitions, flat = formula_definitions(text), formula_definitions(reconstruct_written_out(source, certificate))
        chunked = chunked_definitions(definitions)
        self.assertEqual(len(chunked), 2, "expected the distinct and the conjunction of its pairs, both in chunks")
        for name in chunked:
            chunks = [name] + ["%s_c%d" % (name, chunk) for chunk in range(1, (276 + stride - 1) // stride)]
            self.assertEqual([chunk for chunk in definitions if chunk == name or chunk.startswith(name + "_c")],
                             chunks[:0:-1] + [name])
            self.assertEqual(sum(definitions[chunk].count("(And ") for chunk in chunks), 275)
            self.assertEqual(unfolded(self, definitions, name), flat[name])
        # One of the two is the distinct, over the terms.
        self.assertEqual(sum(self.pairs_in_order(flat[name], 24, r"\(Not \(%s = %s\)\)", r"\(term_\d+ [^()]*\)")
                             for name in chunked), 1)

    def pairs_in_order(self, body, count, pair, operand):
        """Whether a conjunction is the pairs of a distinct over count arguments: by the first, then the second."""
        pairs = re.findall(pair % (("(%s)" % operand,) * 2), body)
        if len(pairs) != body.count("(And ") + 1:
            return False  # a conjunction of something else
        arguments = [pairs[0][0]] + [right for _, right in pairs[:count - 1]]
        self.assertEqual(len(set(arguments)), count)
        self.assertEqual(pairs, [(left, right) for index, left in enumerate(arguments)
                                 for right in arguments[index + 1:]])
        return True

    def test_the_chunks_of_a_distinct_unfold_to_its_pairs_in_order(self):
        # No Lean: the definitions. 24 arguments are the fewest whose pairs (276) are defined in
        # chunks; 25 leave a last chunk that is not full; through both cores.
        stride, limit = proof_to_lean._AND_ELIM_STRIDE, proof_to_lean._CHUNKED_OPERANDS
        self.assertLessEqual(23 * 22 // 2, limit)
        for count, core in ((24, "clause-log"), (25, "legacy"), (25, "clause-log")):
            if core == "clause-log" and not _z3_available():
                continue
            source = distinct_with_last_equality(count)
            certificate = (proof_certificate.export_certificate(source) if core == "legacy"
                           else proof_certificate.export_clause_log_certificate(source))
            definitions = formula_definitions(proof_to_lean.reconstruct(source, certificate))
            flat = formula_definitions(reconstruct_written_out(source, certificate))
            with self.subTest(count=count, core=core):
                chunked = chunked_definitions(definitions)
                self.assertTrue(chunked)
                self.assertEqual(set(definitions) - {name for name in definitions if re.search(r"_c\d+$", name)},
                                 set(flat))
                for name in chunked:
                    self.assertIn("%s_c%d" % (name, (count * (count - 1) // 2 - 1) // stride), definitions)
                    self.assertEqual(unfolded(self, definitions, name), flat[name])
                self.assertEqual(sum(self.pairs_in_order(flat[name], count, r"\(Not \(%s = %s\)\)",
                                                         r"\(term_\d+ [^()]*\)") for name in chunked), 1)

    def test_a_boolean_distinct_is_chunked_over_its_negated_equivalences(self):
        # Over Booleans the pairs are negated equivalences; 24 arguments have no model, which
        # the proof shows from pairs it projects through the chunks' theorems.
        source = boolean_distinct(24)
        certificate = proof_certificate.export_certificate(source)
        self.assertEqual(certificate["fragment"], "propositional")
        text, report = lean_test_support.check(self, source, certificate)
        self.assertIn(".unsat' does not depend on any axioms", report)
        definitions, flat = formula_definitions(text), formula_definitions(reconstruct_written_out(source, certificate))
        chunked = chunked_definitions(definitions)
        self.assertEqual(len(chunked), 1, "expected the distinct alone to be defined in chunks")
        name = chunked[0]
        self.assertEqual(unfolded(self, definitions, name), flat[name])
        self.assertTrue(self.pairs_in_order(flat[name], 24, r"\(Not \(Iff %s %s\)\)", r"\(formula_\d+ [^()]*\)"))
        self.assertRegex(text, r"\(%s_t\d+ _atoms _f\d+\)" % name)


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestChunkedConjunctionsClauseLog(_WideLeanIntegration):
    """Proofs reach an operand of a conjunction defined in chunks through the chunks' theorems.

    A projection out of a conjunction written out costs Lean's elaborator
    the size of what is left of the conjunction (measured; And.right takes
    the two sides as implicit arguments): reaching operand k of n took
    time k * n, and the 71 lemmas of z3test's QF_UF sokoban.3 that each
    refute a distinct over 209 constants (21,736 pairs) from one pair ran
    out of heartbeats on 21,735 steps of mt And.right, 480,000 characters
    each.
    """

    def structural(self, lemma):
        """The lemma's first alternative: the proof over the gates, before the unfolded fallback."""
        return lemma.split("    | (unfold", 1)[0]

    def test_distinct_over_209_constants_is_refuted_from_single_pairs(self):
        # The reduced form of sokoban.3: with the distinct written out the
        # first of these lemmas ran out of 1,000,000 heartbeats at `whnf`.
        stride = proof_to_lean._AND_ELIM_STRIDE
        source = distinct_through_ites(209)
        certificate, axioms = self.check(source, "clause-log", "qf_uf", 209)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)
        text = proof_to_lean.reconstruct(source, certificate)
        chunks = (209 * 208 // 2 + stride - 1) // stride
        self.assertEqual(len(re.findall(r"^theorem formula_\d+_t\d+ ", text, flags=re.M)), chunks - 1)
        lemmas = [self.structural(lemma) for lemma in lemma_texts(text) if "_conj" in lemma]
        self.assertGreaterEqual(len(lemmas), 2)
        # One pair is the last of the distinct: the last chunk's theorem and less than a chunk's projections.
        self.assertTrue(any(re.search(r"\(formula_\d+_t%d _atoms _m _conj\)(?:\.2)*\)\n" % (chunks - 1), lemma)
                            for lemma in lemmas))
        self.assertLess(max(len(lemma) for lemma in lemmas), 1000)
        self.assertLessEqual(longest_run(text, ".2"), stride)
        self.assertLess(longest_run(text, "(mt (@And.right _ _) "), stride)

    def test_cnf_lemma_projects_the_pairs_of_a_true_distinct_from_its_tail_theorems(self):
        stride = proof_to_lean._AND_ELIM_STRIDE
        source = distinct_with_equalities(60)
        certificate, axioms = self.check(source, "clause-log", "qf_uf", 60)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)
        lemmas = [self.structural(lemma) for lemma in lemma_texts(proof_to_lean.reconstruct(source, certificate))]
        projected = 0
        for lemma in lemmas:
            projections = re.findall(r"have _f\d+ := \(formula_\d+_t(\d+) _atoms _m (_f\d+)\)((?:\.2)*)(?:\.1)?\n",
                                     lemma)
            if not projections:
                continue
            projected += len(projections)
            self.assertEqual(len({proof for _, proof, _ in projections}), 1)  # from the distinct's own proof
            self.assertLess(max(len(path) // 2 for _, _, path in projections), stride)
            # No tail of the distinct is bound in the proof: the theorems are the tails.
            self.assertIsNone(re.search(r"have _f\d+ := _f\d+(?:\.2){%d}\n" % stride, lemma))
        self.assertGreater(projected, 0, "no lemma of Z3's clause log for this input projects a pair out of the "
                           "true distinct any more: the test needs another input")
        self.assertLessEqual(projected, 3)  # at most one per equality

    def test_distinct_and_the_conjunction_of_its_pairs_are_one_structure_in_a_lemma(self):
        # Two nodes that read alike are one structure to the prover, named by
        # one of their definitions (_structure_names): the tail theorems it
        # projects with must be those of that definition. Here the distinct
        # and the conjunction of its 276 pairs are both defined in chunks,
        # and the lemma refutes the structure from its last pair.
        source = distinct_or_its_pairs(24)
        certificate, axioms = self.check(source, "clause-log", "qf_uf", 276)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)
        with patch.object(proof_to_lean, "_structure_names", wraps=proof_to_lean._structure_names) as named:
            text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual(len(chunked_definitions(formula_definitions(text))), 2)
        shared = 0
        for (graph, memo), _ in named.call_args_list:
            alike = {}
            for node, structure in memo.items():
                if node in graph.wide_conjunctions:
                    alike.setdefault(structure, []).append(node)
            shared += sum(len(nodes) > 1 for nodes in alike.values())
        self.assertGreater(shared, 0, "no lemma of Z3's clause log for this input reads the distinct and the "
                           "conjunction of its pairs together any more: the test needs another input")
        refutations = re.findall(r"\(fun \(_conj : \((formula_\d+) _atoms _m\)\) => [^\n]*?"
                                 r"\((formula_\d+)_t(\d+) _atoms _m _conj\)", text)
        self.assertTrue(refutations)
        for named_by, tails_of, chunk in refutations:
            self.assertEqual(named_by, tails_of)
            self.assertEqual(int(chunk), 275 // proof_to_lean._AND_ELIM_STRIDE)  # the last pair's chunk

    def test_unfolding_a_chunked_distinct_names_its_chunks(self):
        # The fallback of a theory lemma unfolds the definitions down to the
        # terms: the chunks follow the distinct, in their order.
        stride = proof_to_lean._AND_ELIM_STRIDE
        source = distinct_with_last_equality(24)
        certificate, axioms = self.check(source, "clause-log", "qf_uf", 24)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)
        text = proof_to_lean.reconstruct(source, certificate)
        definitions = formula_definitions(text)
        chunked = chunked_definitions(definitions)
        self.assertTrue(chunked)
        unfolded_somewhere = False
        for name in chunked:
            chunks = [name] + ["%s_c%d" % (name, chunk) for chunk in range(1, (276 + stride - 1) // stride)]
            unfolds = [line for line in text.split("\n") if re.search(r"\bunfold\b.* %s " % name, line)]
            unfolded_somewhere = unfolded_somewhere or bool(unfolds)
            for line in unfolds:
                self.assertIn(" %s " % " ".join(chunks), line)
        self.assertTrue(unfolded_somewhere, "no lemma of this input unfolds the distinct any more")

    def refutations(self, text):
        """The structural proofs of the lemmas that refute a conjunction defined in chunks from one operand."""
        lemmas = [self.structural(lemma) for lemma in lemma_texts(text)]
        lemmas = [lemma for lemma in lemmas if "(fun (_conj : " in lemma]
        self.assertTrue(lemmas, "no lemma of Z3's clause log for this input refutes the conjunction from one "
                        "of its operands any more: the test needs another input")
        return lemmas

    def check_guarded_conjunction(self, width):
        source = guarded_conjunction(width)
        certificate, axioms = self.check(source, "clause-log", "propositional", width)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)
        text = proof_to_lean.reconstruct(source, certificate)
        return text, max(self.refutations(text), key=len)

    def test_wide_conjunction_is_refuted_from_its_last_operand(self):
        self.check_guarded_conjunction(2000)

    def test_refuting_a_wide_conjunction_from_its_last_operand_is_linear(self):
        # No Lean: the text. The proof was one mt And.right per operand before
        # the refuted one (22 characters each), and Lean's time on it grew
        # with the square of the width.
        stride = proof_to_lean._AND_ELIM_STRIDE
        sizes = {}
        for width in (1000, 2000, 4000):
            source = guarded_conjunction(width)
            text = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source))
            self.assertLess(max(len(lemma) for lemma in self.refutations(text)), 1500)
            self.assertLessEqual(longest_run(text, ".2"), stride)
            self.assertEqual(longest_run(text, "(mt (@And.right _ _) "), 0)
            sizes[width] = len(text)
        self.assertLess(sizes[4000], 2.1 * sizes[2000])
        self.assertLess(sizes[2000], 2.1 * sizes[1000])

    @lean_test_support.slow("a 16,000-operand conjunction refuted from its last operand, 2.2 MB of Lean")
    def test_conjunction_of_16000_operands_is_refuted_from_its_last(self):
        # With the conjunction written out the lemma ran out of heartbeats
        # at `whnf` after 33 s; at 8,000 operands it took 17 s.
        text, lemma = self.check_guarded_conjunction(16000)
        self.assertLess(len(lemma), 1500)

    def check_last_operands(self, width):
        source = last_operands_conjunction(width)
        certificate, axioms = self.check(source, "clause-log", "propositional", width)
        self.assertEqual(certificate["rule_counts"]["and-elim"], 2)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)
        return proof_to_lean.reconstruct(source, certificate)

    def test_and_elim_out_of_a_chunked_conjunction_starts_from_its_tail_theorems(self):
        # The reduced QF_IDL parity 10.700 (z3test's smtlib-sample): 36
        # and-elims out of one assertion of 115,040 operands. The theorem
        # bound the assertion's tail every 32 operands up to the last one
        # eliminated, 3,339 lets, and ran out of heartbeats at operand 52,832.
        # At the first width the last operand is alone in the last chunk,
        # which the chunk's theorem proves as it stands, and the one before
        # it is the last of its chunk; at the second the last chunk is full
        # and both are in it, the last one with no `.1`. (In whichever order
        # the log needs the two operands.)
        stride = proof_to_lean._AND_ELIM_STRIDE
        for width in (proof_to_lean._CHUNKED_OPERANDS + 1, proof_to_lean._CHUNKED_OPERANDS + stride):
            with self.subTest(width=width):
                theorem = self.check_last_operands(width).split("\ntheorem unsat ")[1]
                self.assertNotIn("_tail_", theorem)
                tails = re.findall(r"\n    \(formula_%d_t(\d+) _atoms _step_\d+\)((?:\.2)*(?:\.1)?)\n" % width, theorem)
                self.assertEqual(sorted(tails), sorted(
                    (str(position // stride), ".2" * (position % stride) + (".1" if position < width - 1 else ""))
                    for position in (width - 2, width - 1)))

    def test_and_elim_from_another_chunk_or_of_another_operand_is_rejected(self):
        # What an and-elim out of a chunked conjunction rests on is checked
        # by Lean: started from the theorem of the chunk before, or one
        # projection short, the step proves another operand than its type
        # says. (The text as exported is the one the test above checks.)
        stride = proof_to_lean._AND_ELIM_STRIDE
        width = proof_to_lean._CHUNKED_OPERANDS + 1
        source = last_operands_conjunction(width)
        text = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source))
        chunk, path = width // stride - 1, r"\.2" * (stride - 1) + r"\.1"
        (use,) = re.findall(r"\n    \(formula_%d_t%d _atoms _step_\d+\)%s\n" % (width, chunk, path), text)
        mutants = {"another chunk": use.replace("_t%d _atoms" % chunk, "_t%d _atoms" % (chunk - 1)),
                   "another operand": use.replace(".2.1\n", ".1\n")}
        for name, mutant in mutants.items():
            with self.subTest(mutant=name), tempfile.TemporaryDirectory() as directory:
                self.assertNotEqual(mutant, use)
                output = Path(directory) / "mutant.lean"
                output.write_text(text.replace(use, mutant))
                result = lean_test_support.run_check_lean(output)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                self.assertIn("Type mismatch", errors[0])

    def test_and_elim_far_into_a_conjunction_binds_nothing(self):
        # No Lean: the text. The theorem grew by a let of 110 characters per
        # 32 operands before the last one eliminated (13,500 characters at
        # 4,000 operands).
        for width in (1000, 2000, 4000):
            source = last_operands_conjunction(width)
            text = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source))
            self.assertNotIn("_tail_", text)
            self.assertEqual(len(re.findall(r"\n    \(formula_%d_t%d _atoms _step_\d+\)" % (
                width, (width - 1) // proof_to_lean._AND_ELIM_STRIDE), text)), 2)
            self.assertLess(len(text.split("\ntheorem unsat ")[1]), 1000)

    @lean_test_support.slow("and-elim of the last operands of an 8,000-operand conjunction, 1 MB of Lean")
    def test_last_operands_of_a_conjunction_of_8000_are_eliminated(self):
        # Written out, each projection walked what was left of the
        # conjunction and the theorem ran out of heartbeats at `isDefEq`
        # (5.6 s at 4,000 operands); the tails are the chunks, by their names.
        self.check_last_operands(8000)

    @lean_test_support.slow("and-elim of the last operands of a 128,000-operand conjunction, 16 MB of Lean")
    def test_last_operands_of_a_conjunction_of_128000_are_eliminated(self):
        # With the tails bound by 3,999 lets the theorem ran out of
        # heartbeats at `whnf` (79 s; 68 s at 64,000 operands, 24 s at
        # 32,000); from the tail theorems the file takes 47 s, 23 s, 13 s.
        text = self.check_last_operands(128000)
        self.assertLess(len(text.split("\ntheorem unsat ")[1]), 1000)


if __name__ == "__main__":
    unittest.main()
