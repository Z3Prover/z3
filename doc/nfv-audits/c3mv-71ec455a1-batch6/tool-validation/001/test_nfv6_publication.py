import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import replay_nfv6_checks as replay
import validate_nfv6_publication as validator
import verify_nfv6 as runner


ROOT = Path(__file__).resolve().parent


class PublicationTests(unittest.TestCase):
    def test_replay_preserves_all_nonlocation_options(self):
        record = json.loads((ROOT / "nfv6-checks" / "checks.json").read_text())[3]
        command = replay.replay_command(record, Path("historical.dfy"), Path("Dafny.exe"), Path("z3-4.12.1.exe"))
        expected = list(record["command"])
        expected[0], expected[2] = "Dafny.exe", "historical.dfy"
        expected[expected.index("--solver-path") + 1] = "z3-4.12.1.exe"
        self.assertEqual(command, expected)
        with self.assertRaisesRegex(AssertionError, "pinned solver"):
            replay.replay_command(record, Path("historical.dfy"), Path("Dafny.exe"), Path("z3-4.14.1.exe"))

    def test_audit_failure_acknowledgement_precedes_any_execution(self):
        with patch.object(runner, "run_bounded") as process, patch.object(replay, "validate") as validate:
            with self.assertRaises(PermissionError):
                replay.replay(ROOT, 4, Path("unused"), Path("unused"), ROOT / "unused")
            process.assert_not_called()
            validate.assert_not_called()

    def test_replay_cannot_write_into_immutable_bundle(self):
        with patch.object(runner, "run_bounded") as process:
            with self.assertRaisesRegex(ValueError, "outside"):
                replay.replay(ROOT, 4, Path("unused"), Path("unused"), ROOT / "new-replay", True)
            process.assert_not_called()

    def test_failed_positive_cannot_be_promoted_to_admitted(self):
        model, prop = runner.load_sealed()
        history = copy.deepcopy(json.loads((ROOT / "nfv6-checks" / "checks.json").read_text()))
        history[3]["admitted"] = True
        with self.assertRaisesRegex(AssertionError, "admission"):
            validator.check_history(ROOT, history, model, prop)

    def test_incomplete_domain_group_cannot_gate_positive(self):
        model, prop = runner.load_sealed()
        history = copy.deepcopy(json.loads((ROOT / "nfv6-checks" / "checks.json").read_text()))
        history[2]["domain_example_ids"].pop()
        with self.assertRaisesRegex(AssertionError, "domain"):
            validator.check_history(ROOT, history, model, prop)


if __name__ == "__main__":
    unittest.main()
