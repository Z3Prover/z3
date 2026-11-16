"""Build-scope selection/wiring fixtures and real F* carrier-isolation checks."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import checker_scope


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = json.loads((ROOT / "tools/checker_modules.json").read_text(encoding="utf-8"))
KERNEL = ["Z3CoreModel.fst", "Z3TypedQuantifier.fst", "Z3GhostStandardModel.fst",
          "Z3CoreKernel.fst", "Z3QuantifierKernel.fst", "Z3BinderKernel.fst"]


def closure(*extra, without=KERNEL):
    return {m for m in MANIFEST["modules"] + MANIFEST["cherry_modules"] if m not in without} | set(extra)


PWSH = os.environ.get("PWSH") or shutil.which("pwsh")
FSTAR = os.environ.get("FSTAR_EXE") or shutil.which("fstar.exe")
FAKE_FSTAR = """#!/bin/sh
printf '%s\\n' "$*" >> "$FAKE_FSTAR_LOG"
case " $* " in
  *" --version "*) echo "F* fake" ;;
  *" --dep "*) cat "$FAKE_DEP_OUTPUT" ;;
  *" --cache_checked_modules "*)
    previous=; cache=; module=
    for arg in "$@"; do
      [ "$previous" = --cache_dir ] && cache=$arg
      previous=$arg; module=$arg
    done
    touch "$cache/$(basename "$module").checked" ;;
esac
"""


def dep_output(directory, files, interfaces):
    lines = ["Z3List.fst.checked: \\", "\tZ3List.fst", "", "ALL_FST_FILES= \\"]
    lines += [f"\t{name} \\" for name in files[:-1]] + [f"\t{files[-1]}", "", "ALL_FSTI_FILES= \\"]
    lines += [f"\t{name} \\" for name in interfaces[:-1]] + [f"\t{interfaces[-1]}", ""]
    lines += ["ALL_CHECKED_FILES= \\", f"\t{directory / 'Z3Unlisted.fst.checked'}", ""]
    return "\n".join(lines)


class DependencyOutputTests(unittest.TestCase):
    def test_reads_only_this_directorys_sources_from_the_file_lists(self):
        output = dep_output(
            ROOT,
            ["/opt/fstar/lib/fstar/ulib/FStar.List.Tot.Base.fst", "Z3List.fst",
             str(ROOT / "Z3NativeProof.fst"), str(ROOT / "audits/Z3Elsewhere.fst")],
            ["/opt/fstar/lib/fstar/ulib/FStar.All.fsti", "Z3Native.fsti"],
        )
        self.assertEqual(checker_scope.dependency_files(output, ROOT),
                         {"Z3List.fst", "Z3NativeProof.fst", "Z3Native.fsti"})

    def test_crlf_output_is_accepted(self):
        output = dep_output(ROOT, ["Z3List.fst", "Z3AstTheory.fst"], ["Z3Native.fsti"])
        self.assertEqual(checker_scope.dependency_files(output.replace("\n", "\r\n"), ROOT),
                         {"Z3List.fst", "Z3AstTheory.fst", "Z3Native.fsti"})

    def test_output_without_file_lists_is_an_error(self):
        with self.assertRaisesRegex(RuntimeError, "ALL_FST_FILES"):
            checker_scope.dependency_files("Z3List.fst.checked: \\\n\tZ3List.fst\n", ROOT)


@unittest.skipUnless(FSTAR, "needs F* (set FSTAR_EXE)")
class CarrierDependencyTests(unittest.TestCase):
    def test_modular_power_does_not_import_legacy_values(self):
        for module in ("Z3IndependentModPow.fsti", "Z3IndependentModPow.fst",
                       "Z3IndependentModOrder.fsti", "Z3IndependentModOrder.fst",
                       "Z3IndependentModOrderTests.fst",
                       "Z3IndependentModDivisor.fsti", "Z3IndependentModDivisor.fst",
                       "Z3IndependentModDivisorTests.fst",
                       "Z3IndependentPrimeDivisor.fsti", "Z3IndependentPrimeDivisor.fst",
                       "Z3IndependentPrimeDivisorTests.fst",
                       "Z3IndependentPrimeFactors.fsti", "Z3IndependentPrimeFactors.fst",
                       "Z3IndependentPrimeFactorsTests.fst",
                       "Z3IndependentCoprimePower.fsti", "Z3IndependentCoprimePower.fst",
                       "Z3IndependentFactorPrime.fsti", "Z3IndependentFactorPrime.fst",
                       "Z3IndependentPrimeEvidence.fsti", "Z3IndependentPrimeEvidence.fst"):
            with self.subTest(module=module):
                dependencies = checker_scope.dependency_closure(
                    checker_scope.dependency_command(FSTAR, [module]))
                self.assertFalse(dependencies & {"Z3ValueTheory.fst", "Z3UnifiedProof.fst"})

    def test_independent_checker_has_no_legacy_value_dependency(self):
        for module in ("Z3IndependentChecker.fsti", "Z3IndependentChecker.fst",
                       "Z3IndependentCheckerTests.fst", "Z3ClauseProof.fst",
                       "Z3SortedDistinct.fsti", "Z3SortedDistinct.fst",
                       "Z3SortedDistinctTests.fst",
                       "Z3SortedDistinctRoot.fsti", "Z3SortedDistinctRoot.fst",
                       "Z3SortedDistinctRootTests.fst",
                       "Z3IndependentDistinctReplay.fsti", "Z3IndependentDistinctReplay.fst",
                       "Z3IndependentDistinctReplayTests.fst",
                       "Z3IndependentSkolemReplay.fsti", "Z3IndependentSkolemReplay.fst",
                       "Z3IndependentDependentReplay.fsti", "Z3IndependentDependentReplay.fst",
                       "Z3IndependentBinderReplay.fsti", "Z3IndependentBinderReplay.fst",
                       "Z3IndependentBinderElaboration.fsti", "Z3IndependentBinderElaboration.fst",
                       "Z3IndependentDefinitionPair.fsti", "Z3IndependentDefinitionPair.fst",
                       "Z3IndependentDefinitionModel.fsti", "Z3IndependentDefinitionModel.fst",
                       "Z3IndependentDefinitionModelTests.fst",
                       "Z3IndependentDefinitionInstance.fsti", "Z3IndependentDefinitionInstance.fst",
                       "Z3IndependentDefinitionInstanceTests.fst",
                       "Z3IndependentDefinitionEquivalence.fsti", "Z3IndependentDefinitionEquivalence.fst",
                       "Z3IndependentDefinitionEquivalenceTests.fst",
                       "Z3IndependentDefinitionContext.fsti", "Z3IndependentDefinitionContext.fst",
                       "Z3IndependentDefinitionContextTests.fst",
                       "Z3IndependentDefinitionContextEquivalence.fsti",
                       "Z3IndependentDefinitionContextEquivalence.fst",
                       "Z3IndependentDefinitionContextEquivalenceTests.fst",
                       "Z3IndependentDefinitionNnf.fsti", "Z3IndependentDefinitionNnf.fst",
                       "Z3IndependentDefinitionNnfTests.fst",
                       "Z3IndependentDefinitionRoot.fsti", "Z3IndependentDefinitionRoot.fst",
                       "Z3IndependentDefinitionSkolem.fsti", "Z3IndependentDefinitionSkolem.fst",
                       "Z3IndependentDefinitionSkolemTests.fst",
                       "Z3IndependentDefinitionDocument.fsti", "Z3IndependentDefinitionDocument.fst",
                       "Z3IndependentDefinitionNnfDocument.fsti", "Z3IndependentDefinitionNnfDocument.fst",
                       "Z3IndependentDefinitionNnfDocumentTests.fst",
                       "Z3IndependentFiniteFieldReplay.fsti", "Z3IndependentFiniteFieldReplay.fst",
                       "Z3IndependentFiniteFieldRoot.fsti", "Z3IndependentFiniteFieldRoot.fst", "Z3IndependentFiniteFieldRootTests.fst",
                       "Z3IndependentFiniteFieldDocument.fsti", "Z3IndependentFiniteFieldDocument.fst",
                       "Z3IndependentSkolemModel.fsti", "Z3IndependentSkolemModel.fst",
                       "Z3IndependentDefinitionSkolemReplay.fsti",
                       "Z3IndependentDefinitionSkolemReplay.fst",
                       "Z3IndependentDefinitionSkolemDocument.fsti",
                       "Z3IndependentDefinitionSkolemDocument.fst",
                       "Z3IndependentSkolemRoot.fsti", "Z3IndependentSkolemRoot.fst",
                       "Z3NativeProof.fst", "Z3IndependentNative.fsti",
                       "Z3IndependentNative.fst"):
            with self.subTest(module=module):
                dependencies = checker_scope.dependency_closure(
                    checker_scope.dependency_command(FSTAR, [module]))
                self.assertNotIn("Z3ValueTheory.fst", dependencies)

    def test_sorted_vacuity_does_not_depend_on_nnf_replay(self):
        dependencies = checker_scope.dependency_closure(
            checker_scope.dependency_command(FSTAR, ["Z3QuantifierVacuitySorted.fst"]))
        self.assertNotIn("Z3NnfReplay.fst", dependencies)

    def test_carrier_independent_foundations_do_not_import_legacy_values(self):
        for module in ("Z3OperatorTags.fst", "Z3CanonicalOps.fst", "Z3ClausalSemantics.fst",
                       "Z3ObservationalSemantics.fst", "Z3ClauseSyntax.fst",
                       "Z3ExprScope.fst", "Z3GroundScope.fst", "Z3DocumentScope.fst", "Z3SortedInstantiation.fst", "Z3DefinitionSyntax.fst", "Z3DefinitionExpansionScope.fst", "Z3DefinitionExpansionScopeTests.fst", "Z3DefinitionRecognition.fst", "Z3DefinitionRecognitionScope.fst", "Z3DefinitionRecognitionScopeTests.fst", "Z3DefinitionScope.fst", "Z3DefinitionScopeTests.fst",
                       "Z3ExprBinding.fst", "Z3Substitution.fst", "Z3CommutativitySyntax.fst", "Z3SortedCommutativity.fst", "Z3SortedCommutativityTests.fst", "Z3QuantifierNnfSyntax.fst", "Z3QuantifierPullSyntax.fst", "Z3QuantifierVacuitySyntax.fst", "Z3QuantifierVacuitySemantics.fst", "Z3QuantifierVacuityScope.fst", "Z3QuantifierVacuitySorted.fst",
                       "Z3QuantifierInstantiationSyntax.fst", "Z3QuantifierInstantiationSyntaxTests.fst",
                       "Z3SubstitutionTests.fst", "Z3DatatypeSyntax.fst", "Z3DatatypeValue.fst",
                       "Z3DatatypeSignature.fst", "Z3SortedInteger.fst", "Z3SortedSemantics.fst",
                       "Z3SortedQuantifier.fst", "Z3SortedQuantifierInstantiation.fst",
                       "Z3SortedQuantifierInstantiationTests.fst", "Z3BooleanSyntax.fst",
                       "Z3BooleanSyntaxTests.fst", "Z3DistinctAst.fst", "Z3DistinctAstTests.fst", "Z3SortedDatatype.fst",
                       "Z3DatatypeValueTests.fst", "Z3DatatypeNativeModelTests.fst",
                       "Z3SkolemSyntax.fst", "Z3SkolemSyntaxTests.fst",
                       "Z3SortedSkolem.fst", "Z3SortedDependentSkolem.fst",
                       "Z3SortedSkolemTests.fst", "Z3PolynomialSemantics.fst",
                       "Z3ArithmeticSyntax.fst", "Z3SortedArithmetic.fst",
                       "Z3IntegerDivisionSyntax.fst", "Z3IntegerRewriteSyntax.fst", "Z3ConditionalRewriteSyntax.fst", "Z3ArithmeticFactorSyntax.fst", "Z3LpReplaySyntax.fst", "Z3SortedIntDivision.fst", "Z3SortedReal.fst",
                       "Z3SortedRealLinear.fst", "Z3SortedRealOrder.fst",
                       "Z3SortedRealProduct.fst", "Z3SortedRealTests.fst", "Z3SortedRealReplayTests.fst",
                       "Z3SortedRealProductTests.fst", "Z3TypedRoot.fst",
                       "Z3BooleanRewriteSyntax.fst", "Z3SortedBooleanRewrite.fst",
                       "Z3SortedBooleanRewriteTests.fst",
                       "Z3ArraySyntax.fst", "Z3ArrayEqualitySyntax.fst", "Z3SortedArray.fst",
                       "Z3SortedArrayTests.fst", "Z3SortedArrayEquality.fst",
                       "Z3BvSyntax.fst", "Z3BvFreshSyntax.fst", "Z3BvFreshScope.fst", "Z3BvFreshScopeTests.fst", "Z3SortedBv.fst", "Z3SortedBvTests.fst",
                       "Z3SortedFiniteField.fst", "Z3FiniteFieldCertificate.fst", "Z3LpGomorySyntax.fst", "Z3TheoryNormalizeSyntax.fst", "Z3UnifiedProofSyntax.fst", "Z3HypothesisSemantics.fst", "Z3HypothesisSemanticsTests.fst", "Z3RelationalReachability.fst", "Z3RelationalReachabilityTests.fst", "Z3CongruenceSyntax.fst", "Z3RelationalRuleSyntax.fst", "Z3ModusPonensSyntax.fst", "Z3ModusPonensSyntaxTests.fst", "Z3SortedRelational.fst", "Z3SortedRelationalTests.fst", "Z3SortedLeafFacts.fst", "Z3SortedLeafFactsTests.fst", "Z3SortedHypothesisSemantics.fst", "Z3SortedLemmaFacts.fst", "Z3SortedLemmaFactsTests.fst", "Z3SortedModusPonens.fst", "Z3SortedModusPonensTests.fst", "Z3UnifiedNode.fst", "Z3UnifiedNodeTests.fst", "Z3DocumentSyntax.fst", "Z3DocumentPreparation.fst", "Z3DocumentFactSemantics.fst", "Z3DocumentReplay.fst", "Z3DocumentReplaySemantics.fst", "Z3DocumentReplaySemanticsTests.fst", "Z3BinderScopeSyntax.fst", "Z3BinderScopeIndependent.fst", "Z3NnfReplay.fst", "Z3SortedProof.fst", "Z3SortedProofTests.fst", "Z3SortedRootDocument.fst",
                       "Z3SortedBinding.fst", "Z3SortedBindingTests.fst",
                       "Z3LambdaSyntax.fst", "Z3LambdaSyntaxTests.fst",
                       "Z3SortedLambda.fst", "Z3SortedLambdaTests.fst", "Z3SortedLambdaEquality.fst",
                       "Z3SortedLambdaEqualityTests.fst",
                       "Z3SortedLambdaRootTests.fst",
                       "Z3SortedQuantifierInstantiationRootTests.fst",
                       "Z3ObservationalSyntax.fst", "Z3ObservationalProof.fst",
                       "Z3ObservationalSemanticsTests.fst"):
            with self.subTest(module=module):
                dependencies = checker_scope.dependency_closure(
                    checker_scope.dependency_command(FSTAR, [module]))
                self.assertIn("Z3AstTheory.fst", dependencies)
                if module in {"Z3OperatorTags.fst", "Z3CanonicalOps.fst",
                              "Z3ClausalSemantics.fst", "Z3ClauseSyntax.fst",
                              "Z3SortedInteger.fst", "Z3SortedSemantics.fst",
                              "Z3SortedQuantifier.fst", "Z3BooleanSyntax.fst",
                              "Z3BooleanSyntaxTests.fst", "Z3DistinctAst.fst",
                              "Z3SortedDatatype.fst"}:
                    self.assertIn("Z3OperatorTags.fst", dependencies)
                forbidden = {"Z3ValueTheory.fst", "Z3ArrayTheory.fst",
                             "Z3SeqTheory.fst", "Z3BvTheory.fst",
                             "Z3ResolutionProofTheory.fst", "Z3DatatypeLemma.fst",
                             "Z3Definitions.fst", "Z3BooleanRewrite.fst",
                             "Z3BinderSubstitution.fst", "Z3QuantifierPull.fst"}
                if module in {"Z3TypedRoot.fst", "Z3SortedRootDocument.fst", "Z3SortedRealReplayTests.fst", "Z3SortedArray.fst", "Z3SortedArrayTests.fst",
                              "Z3SortedArrayEquality.fst", "Z3SortedFiniteField.fst",
                              "Z3SortedLambdaRootTests.fst", "Z3SortedQuantifierInstantiationRootTests.fst"}:
                    forbidden.remove("Z3ArrayTheory.fst")
                if module in {"Z3TypedRoot.fst", "Z3SortedRootDocument.fst", "Z3SortedRealReplayTests.fst", "Z3BvSyntax.fst", "Z3SortedBv.fst",
                              "Z3SortedBvTests.fst", "Z3SortedLambdaRootTests.fst",
                              "Z3SortedQuantifierInstantiationRootTests.fst"}:
                    forbidden.remove("Z3BvTheory.fst")
                self.assertFalse(dependencies & forbidden, dependencies)

    def test_sorted_checker_does_not_import_legacy_document_checker(self):
        dependencies = checker_scope.dependency_closure(
            checker_scope.dependency_command(FSTAR, ["Z3SortedProof.fst"]))
        self.assertIn("Z3DocumentPreparation.fst", dependencies)
        self.assertFalse(dependencies & {"Z3ProofDocument.fst", "Z3UnifiedProof.fst",
                                         "Z3TheoryNormalize.fst", "Z3ValueTheory.fst"},
                         dependencies)


class SelectionTests(unittest.TestCase):
    roots = ["Z3SortedProof.fst", "Z3Native.fsti", "Z3NativeProof.fst"]

    def test_checker_scope_verifies_the_production_closure_in_manifest_order(self):
        modules, tests = checker_scope.select(MANIFEST, "ocaml", False, closure(), self.roots)
        self.assertEqual(modules, [m for m in MANIFEST["modules"] if m not in KERNEL])
        self.assertEqual(tests, [])
        self.assertIn("Z3SortedRealExtension.fst", modules)
        self.assertNotIn("Z3IdTable-c.cherry.fst", modules)

    def test_full_scope_verifies_every_registered_module_and_test(self):
        modules, tests = checker_scope.select(MANIFEST, "ocaml", True, closure(), self.roots)
        self.assertEqual(modules, MANIFEST["modules"])
        self.assertEqual(tests, MANIFEST["tests"])

    def test_cherry_scopes_add_the_cherry_overrides_root_and_tests(self):
        cherry = closure("Z3Cherry.fst", without=KERNEL + ["Z3BvFreshModel.fst"])
        modules, tests = checker_scope.select(MANIFEST, "cherry", False, cherry, ["Z3Cherry.fst"])
        self.assertEqual(modules, [m for m in MANIFEST["modules"] if m in cherry]
                         + MANIFEST["cherry_modules"] + ["Z3Cherry.fst"])
        self.assertEqual(tests, [])
        modules, tests = checker_scope.select(MANIFEST, "cherry", True, cherry, ["Z3Cherry.fst"])
        self.assertEqual(modules, MANIFEST["modules"] + MANIFEST["cherry_modules"] + ["Z3Cherry.fst"])
        self.assertEqual(tests, MANIFEST["tests"] + ["Z3CherryTests.fst"])

    def test_a_test_module_in_the_checker_closure_fails_both_scopes(self):
        for full in (False, True):
            with self.subTest(full=full), self.assertRaisesRegex(RuntimeError, "Z3RealPower.fst"):
                checker_scope.select(MANIFEST, "ocaml", full, closure("Z3RealPower.fst"), self.roots)

    def test_an_unregistered_dependency_fails(self):
        with self.assertRaisesRegex(RuntimeError, "Z3Unregistered.fst"):
            checker_scope.select(MANIFEST, "ocaml", False, closure("Z3Unregistered.fst"), self.roots)

    def test_a_root_outside_the_closure_fails(self):
        with self.assertRaisesRegex(RuntimeError, "Z3SortedProof.fst"):
            checker_scope.select(MANIFEST, "ocaml", False,
                                 closure(without=KERNEL + ["Z3SortedProof.fst"]), self.roots)

    def test_checker_extraction_entries_are_the_closure_implementations(self):
        entries = checker_scope.extraction_entries(MANIFEST, closure(), False)
        self.assertEqual(entries, [m for m in MANIFEST["modules"]
                                   if m not in KERNEL and not m.endswith(".fsti")])
        self.assertNotIn("Z3Native.fsti", entries)

    def test_full_extraction_entries_are_every_registered_implementation(self):
        entries = checker_scope.extraction_entries(MANIFEST, closure(), True)
        self.assertEqual(entries, [m for m in MANIFEST["modules"] if not m.endswith(".fsti")])
        self.assertEqual(len(entries), 155)
        self.assertTrue(set(KERNEL) <= set(entries))


@unittest.skipUnless(os.name == "posix" and PWSH and shutil.which("git"),
                     "needs PowerShell and git on a POSIX host")
class PowerShellWiringTests(unittest.TestCase):
    """Run build_ocaml_checker.ps1 against fake cmake, z3, F* and bash executables."""

    def build(self, *flags):
        temporary = Path(tempfile.mkdtemp(prefix="checker-scope-"))
        self.addCleanup(shutil.rmtree, temporary)
        fstar = temporary / "fstar"
        shutil.copytree(ROOT / "ocaml_runtime", fstar / "ocaml_runtime")
        (fstar / "tools").mkdir()
        for name in ("build_ocaml_checker.ps1", "checker_scope.py", "checker_modules.json"):
            shutil.copy(ROOT / "tools" / name, fstar / "tools" / name)
        for module in MANIFEST["modules"] + MANIFEST["cherry_modules"] + MANIFEST["tests"]:
            (fstar / module).touch()
        subprocess.run(["git", "init", "-q"], cwd=temporary, check=True)
        subprocess.run(["git", "-c", "user.name=test", "-c", "user.email=test@example.com",
                        "commit", "-q", "--allow-empty", "-m", "fixture"], cwd=temporary, check=True)
        bin_dir = temporary / "bin"
        executables = {
            bin_dir / "cmake": "#!/bin/sh\n",
            bin_dir / "bash": '#!/bin/sh\ncp "$1" "$FAKE_NATIVE_SCRIPT"\n',
            bin_dir / "fstar.exe": FAKE_FSTAR,
            temporary / "install/bin/z3": "#!/bin/sh\necho 'Z3 version 5.4.0 - 64 bit'\n",
        }
        for path, text in executables.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
            path.chmod(0o755)
        names = sorted(closure())
        (temporary / "dep.txt").write_text(dep_output(
            fstar, [n for n in names if n.endswith(".fst")], [n for n in names if n.endswith(".fsti")]))
        environment = dict(os.environ, PATH=f"{bin_dir}{os.pathsep}{os.environ['PATH']}",
                           FAKE_FSTAR_LOG=str(temporary / "fstar.log"),
                           FAKE_DEP_OUTPUT=str(temporary / "dep.txt"),
                           FAKE_NATIVE_SCRIPT=str(temporary / "native.sh"))
        result = subprocess.run(
            [PWSH, "-NoProfile", "-File", fstar / "tools/build_ocaml_checker.ps1",
             "-FstarExe", bin_dir / "fstar.exe", "-Z3WindowsBuildDir", temporary / "z3-build",
             "-Z3InstallDir", temporary / "install", "-CacheDir", temporary / "cache",
             "-WslBuildDir", temporary / "native", "-ReportDir", temporary / "report",
             "-BuildCherry", "-CherryFstarExe", bin_dir / "fstar.exe", *flags],
            env=environment, capture_output=True, text=True, timeout=300)
        verified, entries = [], None
        self.assertTrue((temporary / "fstar.log").is_file(), result.stdout + result.stderr)
        for line in (temporary / "fstar.log").read_text(encoding="utf-8").splitlines():
            parts = line.split()
            if "--cache_checked_modules" in parts:
                verified.append(parts[-1])
            if "--codegen" in parts:
                entries = [parts[i + 1] for i, part in enumerate(parts) if part == "--custard_entry_module"]
        native = (temporary / "native.sh").read_text(encoding="utf-8")
        report = json.loads((temporary / "report/scope-ocaml.json").read_text(encoding="utf-8"))
        return result, verified, entries, native, report

    def test_without_run_tests_only_the_closure_is_verified_and_no_tests_are_built(self):
        result, verified, entries, native, report = self.build()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(verified, [m for m in MANIFEST["modules"] if m not in KERNEL])
        self.assertEqual(entries, [m[:-4] for m in MANIFEST["modules"]
                                   if m not in KERNEL and m.endswith(".fst")])
        self.assertNotIn("--run-tests", native)
        self.assertNotIn("native-tests", native)
        self.assertIn("/report/scope-cherry.json", native)
        self.assertEqual((report["mode"], report["native_tests"]), ("checker", False))
        self.assertEqual(report["selected_modules"], verified)
        self.assertEqual(sorted(report["registered_not_selected"]),
                         sorted(KERNEL + MANIFEST["tests"]))

    def test_run_tests_verifies_every_module_and_test_then_runs_native_tests(self):
        result, verified, entries, native, report = self.build("-RunTests")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Native checker CLI tests failed", result.stdout + result.stderr)
        self.assertEqual(verified, MANIFEST["modules"] + MANIFEST["tests"])
        self.assertEqual(entries, [m[:-4] for m in MANIFEST["modules"] if m.endswith(".fst")])
        self.assertIn("--run-tests", native)
        self.assertIn("native-tests", native)
        self.assertEqual((report["mode"], report["registered_not_selected"]), ("full", []))


if __name__ == "__main__":
    unittest.main()
