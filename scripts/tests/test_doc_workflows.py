############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Unit tests for documentation workflow configuration.
############################################
from pathlib import Path
import unittest


_REPO_ROOT = Path(__file__).resolve().parents[2]


class TestDocWorkflows(unittest.TestCase):
    def _ubuntu_doc_job(self, workflow):
        lines = (_REPO_ROOT / ".github" / "workflows" / workflow).read_text().splitlines()
        try:
            start = lines.index("  ubuntu-doc:") + 1
        except ValueError:
            self.fail(f"{workflow} should define an ubuntu-doc job")

        body = []
        for line in lines[start:]:
            if line.startswith("  ") and not line.startswith("    ") and line.endswith(":"):
                break
            body.append(line)
        return "\n".join(body)

    def test_ubuntu_doc_builds_python_bindings_for_z3py_docs(self):
        for workflow in ("nightly.yml", "release.yml"):
            with self.subTest(workflow=workflow):
                job = self._ubuntu_doc_job(workflow)
                self.assertIn("--z3py-package-path=../build/python/z3", job)
                cmake_line = next(line for line in job.splitlines() if "cmake -S . -B build" in line)
                self.assertIn("-DZ3_BUILD_PYTHON_BINDINGS=ON", cmake_line)


if __name__ == "__main__":
    unittest.main()
