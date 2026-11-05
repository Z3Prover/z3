############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Unit tests for release source archives.
############################################
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import textwrap
import unittest


_REPO_ROOT = Path(__file__).resolve().parents[2]


class TestReleaseWorkflow(unittest.TestCase):
    def test_source_archive_matches_release_commit(self):
        workflow = (_REPO_ROOT / ".github/workflows/release.yml").read_text()
        publish = workflow.split("  publish-github:\n", 1)[1].split("  publish-nuget:\n", 1)[0]
        archive_step = publish.split("      - name: Create source archive\n", 1)[1]
        archive_script = textwrap.dedent(
            archive_step.split("        run: |\n", 1)[1].split("      - name:", 1)[0]
        )
        self.assertLess(publish.index("Download all artifacts"), publish.index("Create source archive"))
        self.assertLess(publish.index("Create source archive"), publish.index("Create Release"))
        self.assertIn('-name "*.tar.gz"', publish)
        self.assertIn('"${unique_files[@]}"', publish)
        self.assertIn("--target ${{ github.sha }}", publish)

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)

            def git(*args):
                return subprocess.check_output(
                    ["git", *args], cwd=root, text=True, stderr=subprocess.PIPE
                ).strip()

            git("init")
            (root / "source.txt").write_text("release source\n")
            git("add", "source.txt")
            git("-c", "user.name=Test", "-c", "user.email=test@example.com", "commit", "-m", "Release")
            release_commit = git("rev-parse", "HEAD")
            (root / "source.txt").write_text("later source\n")
            git("-c", "user.name=Test", "-c", "user.email=test@example.com", "commit", "-am", "Later")
            (root / "untracked.txt").write_text("not release source\n")
            (root / "tmp").mkdir()

            subprocess.run(
                ["bash", "-e", "-c", archive_script],
                cwd=root,
                env={**os.environ, "RELEASE_VERSION": "5.3.2", "GITHUB_SHA": release_commit},
                check=True,
            )
            with tarfile.open(root / "tmp/z3-5.3.2-source.tar.gz") as archive:
                self.assertEqual(archive.getnames(), ["z3-z3-5.3.2", "z3-z3-5.3.2/source.txt"])
                self.assertEqual(archive.extractfile("z3-z3-5.3.2/source.txt").read(), b"release source\n")


if __name__ == "__main__":
    unittest.main()
