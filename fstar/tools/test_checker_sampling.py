"""Tests for reproducible, checked, bounded SMT-LIB archive sampling."""

import contextlib
from collections import Counter
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import zstandard

import run_checker_regressions as runner
import sample_checker_benchmarks as sampler


UNSAT = b"; original source and license\n(set-info :status unsat)\n(assert false)\n"


class CheckerSamplingTests(unittest.TestCase):
    def test_extended_cohort_matches_fixed_inputs_and_workflow_count(self):
        root = Path(__file__).resolve().parents[2]
        corpus = root / "fstar" / "benchmarks" / "smtlib-sample"
        manifest = corpus / "manifest.json"
        document = json.loads(manifest.read_text(encoding="utf-8"))
        counts = {entry["logic"]: count for entry, count in sampler.archive_specs(document)}
        self.assertEqual(counts, {
            "QF_DT": 25, "QF_NIA": 25, "UF": 25,
            "UFLRA": 10, "QF_BV": 25, "QF_UFBV": 25,
            "QF_UFDT": 25, "QF_ABV": 25, "QF_AUFBV": 25,
            "QF_UFLRA": 25, "QF_NRA": 25, "UFDT": 25, "UFDTLIA": 25,
        })
        self.assertEqual(Counter(case["logic"] for case in document["cases"]), counts)
        paths, discovered = runner.discover(corpus, ".", 0)
        self.assertEqual(discovered, sum(counts.values()))
        runner.verify_manifest(corpus, ".", manifest, paths)
        for path in paths:
            self.assertRegex(path.read_bytes(), sampler.STATUS)
        workflow = (root / ".github" / "workflows" / "pulse-checker-regressions.yml").read_text()
        self.assertIn(f"--expected-cases {sum(counts.values())} ", workflow)

    def archive(self, directory, members, logic="QF_DT"):
        contents = io.BytesIO()
        with tarfile.open(fileobj=contents, mode="w") as archive:
            for name, data in members:
                info = tarfile.TarInfo(name)
                if data is None:
                    info.type = tarfile.SYMTYPE
                    info.linkname = "../outside.smt2"
                    archive.addfile(info)
                else:
                    info.size = len(data)
                    archive.addfile(info, io.BytesIO(data))
        path = Path(directory) / f"{logic}.tar.zst"
        path.write_bytes(zstandard.ZstdCompressor().compress(contents.getvalue()))
        entry = {
            "logic": logic,
            "url": f"https://zenodo.org/api/records/16740866/files/{logic}.tar.zst/content",
            "size_bytes": path.stat().st_size,
            "sha256": sampler.file_sha256(path),
        }
        return path, entry

    def test_seed_is_repeatable_rotates_members_and_ignores_archive_order(self):
        with tempfile.TemporaryDirectory() as directory:
            members = [(f"non-incremental/QF_DT/family/{index}.smt2", UNSAT)
                       for index in range(20)]
            path, entry = self.archive(directory, members)
            first, eligible = sampler.sample_archive(path, entry, 3, "run-1")
            self.assertEqual(eligible, 20)
            self.assertEqual(first, sampler.sample_archive(path, entry, 3, "run-1")[0])
            second, _ = sampler.sample_archive(path, entry, 3, "run-2")
            self.assertNotEqual(first, second)
            path, entry = self.archive(directory, list(reversed(members)))
            self.assertEqual(first, sampler.sample_archive(path, entry, 3, "run-1")[0])

    def test_filters_status_and_size_without_modifying_selected_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            boundary = UNSAT + b" " * (sampler.MAX_INPUT_BYTES - len(UNSAT))
            path, entry = self.archive(directory, [
                ("non-incremental/QF_DT/a.smt2", UNSAT),
                ("non-incremental/QF_DT/nested/b.smt2", boundary),
                ("non-incremental/QF_DT/large.smt2", boundary + b" "),
                ("non-incremental/QF_DT/sat.smt2", b"(set-info :status sat)\n"),
                ("non-incremental/QF_DT/empty.smt2", b""),
                ("non-incremental/QF_DT/list.txt", UNSAT),
            ])
            selected, eligible = sampler.sample_archive(path, entry, 2, "seed")
            self.assertEqual(eligible, 2)
            self.assertEqual([(row[0], row[2]) for row in selected],
                             [("QF_DT/a.smt2", UNSAT), ("QF_DT/nested/b.smt2", boundary)])

    def test_checksum_failure_precedes_decompression(self):
        with tempfile.TemporaryDirectory() as directory:
            path, entry = self.archive(directory, [("non-incremental/QF_DT/a.smt2", UNSAT)])
            with patch.object(sampler.zstandard, "ZstdDecompressor") as decompress:
                for bad in ({**entry, "sha256": "0" * 64},
                            {**entry, "size_bytes": entry["size_bytes"] + 1}):
                    with self.assertRaisesRegex(ValueError, "size/SHA-256 mismatch"):
                        sampler.sample_archive(path, bad, 1, "seed")
                decompress.assert_not_called()

    def test_unsafe_nonregular_and_duplicate_members_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            for name in ("/outside.smt2", "non-incremental/QF_DT/../outside.smt2",
                         "non-incremental/QF_DT/a\\b.smt2", "non-incremental/UF/a.smt2"):
                with self.subTest(name=name):
                    path, entry = self.archive(directory, [(name, UNSAT)])
                    with self.assertRaisesRegex(ValueError, "Unsafe or unexpected"):
                        sampler.sample_archive(path, entry, 1, "seed")
            path, entry = self.archive(directory, [("non-incremental/QF_DT/link.smt2", None)])
            with self.assertRaisesRegex(ValueError, "Unsafe or unexpected"):
                sampler.sample_archive(path, entry, 1, "seed")
            path, entry = self.archive(directory, [
                ("non-incremental/QF_DT/a.smt2", UNSAT),
                ("non-incremental/QF_DT/a.smt2", UNSAT)])
            with self.assertRaisesRegex(ValueError, "Duplicate archive member"):
                sampler.sample_archive(path, entry, 1, "seed")

    def test_insufficient_population_fails_instead_of_repeating_or_reducing_sample(self):
        with tempfile.TemporaryDirectory() as directory:
            path, entry = self.archive(directory, [("non-incremental/QF_DT/a.smt2", UNSAT)])
            with self.assertRaisesRegex(ValueError, "requested 2 inputs, only 1 eligible"):
                sampler.sample_archive(path, entry, 2, "seed")

    def test_prepared_manifest_verifies_membership_provenance_and_reports_sampling(self):
        with tempfile.TemporaryDirectory() as directory:
            path, entry = self.archive(directory, [
                (f"non-incremental/QF_DT/family/{index}.smt2", UNSAT) for index in range(20)])
            manifest = Path(directory) / "source.json"
            manifest.write_text(json.dumps({
                "schema_version": 1, "source": "https://zenodo.org/records/16740866",
                "per_logic": {"QF_DT": 3}, "archives": [entry], "cases": [],
            }))
            output = Path(directory) / "sample"

            def download(destination, spec, timeout):
                self.assertEqual(spec, entry)
                shutil.copyfile(path, destination)

            with patch.object(sampler, "download_archive", side_effect=download), \
                    contextlib.redirect_stdout(io.StringIO()):
                sampler.prepare_sample(manifest, output, "run-123", 60)
            paths, discovered = runner.discover(output, ".", 0)
            metadata = runner.verify_manifest(output, ".", output / "manifest.json", paths)
            self.assertEqual(discovered, 3)
            self.assertEqual(metadata["manifest"]["seed"], "run-123")
            self.assertEqual(metadata["manifest"]["source_manifest_sha256"],
                             sampler.file_sha256(manifest))
            for row in json.loads((output / "manifest.json").read_text())["cases"]:
                self.assertEqual(row["sha256"], hashlib.sha256(UNSAT).hexdigest())
            report = Path(directory) / "report"
            report.mkdir()
            (report / "selection.json").write_text(json.dumps({
                "paths": [path.relative_to(output).as_posix() for path in paths], **metadata}))
            with patch.dict("os.environ", {"SAMPLER_OUTCOME": "success"}):
                runner.report(report)
            text = (report / "report.md").read_text()
            self.assertIn("Seed `run-123`", text)
            self.assertIn("Maximum eligible input size: 262144 bytes", text)
            self.assertIn("Benchmark sampling: **success**", text)
            self.assertEqual(json.loads((report / "summary.json").read_text())["tested"], 0)

    def test_download_failure_never_creates_a_success_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            _, entry = self.archive(directory, [("non-incremental/QF_DT/a.smt2", UNSAT)])
            manifest = Path(directory) / "source.json"
            manifest.write_text(json.dumps({
                "schema_version": 1, "source": "https://zenodo.org/records/16740866",
                "per_logic": 1, "archives": [entry]}))
            output = Path(directory) / "sample"
            with patch.object(sampler, "download_archive",
                              side_effect=subprocess.CalledProcessError(22, ["curl"])), \
                    contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaises(subprocess.CalledProcessError):
                    sampler.prepare_sample(manifest, output, "seed", 60)
            self.assertFalse((output / "manifest.json").exists())
            with patch.dict("os.environ", {"SAMPLER_OUTCOME": "failure"}):
                runner.report(output)
            self.assertIn("Benchmark sampling: **failure**", (output / "report.md").read_text())

    def test_archive_configuration_rejects_unpinned_or_nonzenodo_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            _, entry = self.archive(directory, [("non-incremental/QF_DT/a.smt2", UNSAT)])
            document = {"schema_version": 1, "per_logic": 1, "archives": [entry]}
            for change in (
                    {"url": "https://example.com/QF_DT.tar.zst"},
                    {"url": entry["url"].replace("https:", "http:")},
                    {"logic": "../QF_DT"}, {"sha256": "unverified"}, {"size_bytes": 0}):
                with self.subTest(change=change), self.assertRaises(ValueError):
                    sampler.archive_specs({**document, "archives": [{**entry, **change}]})
            with self.assertRaises(ValueError):
                sampler.archive_specs({**document, "archives": [entry, entry]})
            with self.assertRaises(ValueError):
                sampler.archive_specs({**document, "per_logic": {"UF": 1}})


if __name__ == "__main__":
    unittest.main()
