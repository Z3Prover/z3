############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Unit tests for documentation workflow configuration.
############################################
from pathlib import Path
import re
import unittest


_REPO_ROOT = Path(__file__).resolve().parents[2]


class TestDocWorkflows(unittest.TestCase):
    def _ubuntu_doc_job(self, workflow):
        text = (_REPO_ROOT / ".github" / "workflows" / workflow).read_text()
        match = re.search(r"^  ubuntu-doc:\n(?P<body>.*?)(?=^  [A-Za-z0-9_-]+:|\Z)", text, re.MULTILINE | re.DOTALL)
        self.assertIsNotNone(match, f"{workflow} should define an ubuntu-doc job")
        return match.group("body")

    def test_ubuntu_doc_builds_python_bindings_for_z3py_docs(self):
        for workflow in ("nightly.yml", "release.yml"):
            with self.subTest(workflow=workflow):
                job = self._ubuntu_doc_job(workflow)
                self.assertIn("--z3py-package-path=../build/python/z3", job)
                cmake_line = next(line for line in job.splitlines() if "cmake -S . -B build" in line)
                self.assertIn("-DZ3_BUILD_PYTHON_BINDINGS=ON", cmake_line)


if __name__ == "__main__":
    unittest.main()
