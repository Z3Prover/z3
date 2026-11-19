"""Mocked replay outcomes test tooling, not audit properties."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
BUNDLE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('nfv5_replay', BUNDLE / 'replay_nfv5_checks.py')
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)
CHECKS = json.loads((BUNDLE / 'nfv5-models' / 'checks.json').read_text())


class ReplayTests(unittest.TestCase):
    def run_mock(self, checks, outcomes):
        with tempfile.TemporaryDirectory(prefix='nfv5-replay-test-') as tmp:
            with patch.object(replay.runner, 'run_bounded', side_effect=outcomes) as run:
                result = replay.run_checks(BUNDLE, checks, Path('trusted-dafny'), Path('trusted-solver'), Path(tmp)/'out')
            rows = json.loads((Path(tmp)/'out'/'results.json').read_text())
            return result, rows, run

    def test_later_match_does_not_mask_mismatch(self):
        result, rows, _ = self.run_mock(CHECKS[:2], [(4,False,None),(0,False,None)])
        self.assertEqual(result, 1)
        self.assertEqual([r['matched'] for r in rows], [False,True])

    def test_changed_hash_rejected_before_execution(self):
        checks = copy.deepcopy(CHECKS[:1])
        checks[0]['input_sha256'] = '0'*64
        with tempfile.TemporaryDirectory() as tmp, patch.object(replay.runner, 'run_bounded') as run:
            with self.assertRaises(AssertionError):
                replay.run_checks(BUNDLE, checks, Path('dafny'), Path('solver'), Path(tmp)/'out')
            run.assert_not_called()

    def test_isolation_mbqi_and_resource_limit_preserved(self):
        result, rows, run = self.run_mock([CHECKS[15]], [(4,False,None)])
        self.assertEqual(result, 0)
        command = run.call_args.args[0]
        self.assertIn('--isolate-assertions', command)
        self.assertEqual(command[command.index('--solver-option')+1], 'O:smt.mbqi=true')
        self.assertEqual(run.call_args.args[2], 600)

    def test_interrupted_check_requires_opt_in(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(replay.runner, 'run_bounded') as run:
            with self.assertRaises(AssertionError):
                replay.run_checks(BUNDLE, [CHECKS[12]], Path('dafny'), Path('solver'), Path(tmp)/'out')
            run.assert_not_called()


if __name__ == '__main__':
    unittest.main()
