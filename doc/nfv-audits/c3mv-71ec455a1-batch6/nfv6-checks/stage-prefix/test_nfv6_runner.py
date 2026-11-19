import copy
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify_nfv6 as runner


class ValidityDerivativeTests(unittest.TestCase):
    def test_accepts_single_annotation_without_computation_change(self):
        model, _ = runner.load_sealed()
        candidate = model.replace('  var i := size;\n', '  var i := size;\n// synth: checked proof hint\n  assert i == size;\n', 1)
        self.assertEqual(runner.checked_annotations(candidate, model), candidate)

    def test_rejects_changed_computation(self):
        model, _ = runner.load_sealed()
        candidate = model.replace('  language := [];', '  language := [true];', 1)
        with self.assertRaisesRegex(AssertionError, 'Computation/signatures/contracts/goals'):
            runner.checked_annotations(candidate, model)

    def test_rejects_code_hidden_on_proof_line(self):
        model, _ = runner.load_sealed()
        for forbidden in ['assert true; status := 1;', 'assert true; assume false;', 'assert true by { assume false; }']:
            candidate = model.replace('  var i := size;\n', '  var i := size;\n  ' + forbidden + '\n', 1)
            with self.subTest(forbidden=forbidden), self.assertRaises(AssertionError):
                runner.checked_annotations(candidate, model)

    def test_removes_only_complete_entry_ensures(self):
        model, prop = runner.load_sealed()
        checked = runner.validity_only(model, prop)
        expected = model
        start = model.index("method DecimalGreater(")
        header_end = model.index("\n{", start)
        for clause in prop["original_ensures"]:
            line = "  ensures " + clause + "\n"
            at = expected.index(line, start)
            tag = expected.rfind("// synth:", start, at)
            self.assertEqual(expected[tag:at], "// synth: checked contract, proof annotation, or structural delimiter\n")
            expected = expected[:tag] + expected[at + len(line):]
        self.assertEqual(checked, expected)
        self.assertEqual(checked[:start], model[:start])
        self.assertTrue(checked.endswith(model[header_end:]))
        self.assertEqual(len(prop["original_ensures"]), 5)

    def test_rejects_weakened_goal_metadata(self):
        model, prop = runner.load_sealed()
        weakened = copy.deepcopy(prop)
        weakened["original_ensures"] = weakened["original_ensures"][:-1]
        with self.assertRaisesRegex(AssertionError, "Full frozen goal list"):
            runner.validity_only(model, weakened)

    def test_failed_gate_returns_nonzero_after_recording_real_exit(self):
        def failed_check(command, stream, wall_seconds):
            stream.write(b'Dafny program verifier finished with 31 verified, 2 errors\n')
            return 4, False, None

        with tempfile.TemporaryDirectory() as temporary:
            checks = Path(temporary)
            with patch.object(runner, 'CHECKS', checks), patch.object(runner, 'run_bounded', side_effect=failed_check), patch('sys.argv', ['verify_nfv6.py', '--phase', 'validity']), contextlib.redirect_stdout(io.StringIO()):
                result = runner.main()
            self.assertEqual(result, 1)
            record, = json.loads((checks / 'checks.json').read_text())
            self.assertEqual(record['exit_code'], 4)
            self.assertFalse(record['admitted'])
            self.assertFalse((checks / '.running').exists())


if __name__ == "__main__":
    unittest.main()
