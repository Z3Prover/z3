"""Focused tool tests; mocked process outcomes are NOT audit evidence."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


class ReplayTests(unittest.TestCase):
    def test_later_match_does_not_mask_mismatch(self):
        with tempfile.TemporaryDirectory(prefix='nfv4-replay-test-') as tmp:
            fake=[subprocess.CompletedProcess([],0,'mocked first mismatch'),subprocess.CompletedProcess([],4,'mocked later match')]
            with patch.object(subprocess,'run',side_effect=fake):
                result=RUN(BUNDLE,CHECKS[:2],Path('trusted-dafny'),Path('trusted-z3'),Path(tmp)/'output')
            rows=json.loads((Path(tmp)/'output'/'results.json').read_text())
            self.assertEqual(result,1)
            self.assertEqual([r['matched'] for r in rows],[False,True])

    def test_modified_input_hash_rejected_before_execution(self):
        checks=copy.deepcopy(CHECKS[:1])
        checks[0]['input_sha256']='0'*64
        with tempfile.TemporaryDirectory(prefix='nfv4-replay-test-') as tmp:
            with patch.object(subprocess,'run') as process:
                with self.assertRaises(AssertionError):
                    RUN(BUNDLE,checks,Path('trusted-dafny'),Path('trusted-z3'),Path(tmp)/'output')
                process.assert_not_called()


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--bundle',type=Path,default=Path(__file__).resolve().parent)
    args=parser.parse_args()
    BUNDLE=args.bundle.resolve()
    script=BUNDLE/'replay_nfv4_checks.py'
    namespace={'__name__':'nfv_replay_tested_module','__file__':str(script)}
    exec(compile(script.read_text(),str(script),'exec'),namespace)
    RUN=namespace['run_checks']
    CHECKS=json.loads((BUNDLE/'nfv4-models'/'checks.json').read_text())
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(ReplayTests))
    raise SystemExit(0 if result.wasSuccessful() else 1)
