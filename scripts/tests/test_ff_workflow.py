############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Unit tests for finite-field checker configuration.
############################################
import ast
import json
from pathlib import Path
import unittest


_REPO_ROOT = Path(__file__).resolve().parents[2]


class TestFiniteFieldWorkflow(unittest.TestCase):
    def test_checker_revisions_match_pipeline(self):
        pins = json.loads((_REPO_ROOT / "scripts/ff-proof-checker-versions.json").read_text())
        pipeline = ast.parse((_REPO_ROOT / "scripts/ff_proof_pipeline.py").read_text())
        revisions = {
            node.targets[0].id: ast.literal_eval(node.value)
            for node in pipeline.body
            if isinstance(node, ast.Assign)
            and isinstance(node.targets[0], ast.Name)
            and node.targets[0].id in ("CARCARA_REVISION", "FFPACHECK_REVISION")
        }
        for name in ("carcara", "ffpacheck"):
            with self.subTest(checker=name):
                pin = pins[name]
                self.assertEqual(pin["revision"], revisions[name.upper() + "_REVISION"])
                self.assertTrue(pin["archive"].endswith("/" + pin["revision"]))
                self.assertRegex(pin["sha256"], r"^[0-9a-f]{64}$")
        self.assertEqual(pins["carcara"]["repository"], "https://github.com/ufmg-smite/carcara")
        self.assertEqual(
            pins["carcara"]["archive"],
            "https://codeload.github.com/ufmg-smite/carcara/legacy.tar.gz/" + pins["carcara"]["revision"],
        )

    def test_workflow_installs_pins_before_building_checkers(self):
        workflow = (_REPO_ROOT / ".github/workflows/finite-field.yml").read_text()
        install = "cp scripts/ff-proof-checker-versions.json z3test/regressions/finite_field/proof_checkers/versions.json"
        build = "python z3test/regressions/finite_field/proof_checkers/build.py --out proof-checkers"
        self.assertLess(workflow.index(install), workflow.index(build))
        self.assertIn("--suite proofs", workflow)


if __name__ == "__main__":
    unittest.main()
