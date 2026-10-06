############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Unit tests for nightly validation workflow configuration.
############################################
from pathlib import Path
import unittest


_REPO_ROOT = Path(__file__).resolve().parents[2]


class TestNightlyValidationWorkflow(unittest.TestCase):
    def test_ubuntu_java_validation_uses_release_layout(self):
        workflow = (_REPO_ROOT / ".github" / "workflows" / "nightly-validation.yml").read_text()
        job = workflow.split("  validate-exe-ubuntu-x64:\n", 1)[1].split(
            "\n  validate-exe-macos-x64:", 1
        )[0]
        self.assertIn('javac -cp "$Z3_DIR/java/com.microsoft.z3.jar" VersionCheck.java', job)
        self.assertIn('-cp ".:$Z3_DIR/java/com.microsoft.z3.jar" VersionCheck', job)
        self.assertIn('-Djava.library.path="$Z3_DIR/bin"', job)
        self.assertIn("env -u LD_LIBRARY_PATH java", job)
        self.assertNotIn("$Z3_DIR/bin/com.microsoft.z3.jar", job)


if __name__ == "__main__":
    unittest.main()
