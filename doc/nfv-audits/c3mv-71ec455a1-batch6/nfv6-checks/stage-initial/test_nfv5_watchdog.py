"""Exercise trusted harness processes only, never audited production source."""
import importlib.util
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import MagicMock, patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('nfv5runner', Path(__file__).with_name('verify_nfv5.py'))
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class WatchdogTests(unittest.TestCase):
    def test_completed_success(self):
        with tempfile.TemporaryFile() as log:
            result = runner.run_bounded([sys.executable, '-c', 'print("success")'], log, 10)
            self.assertEqual(result, (0, False, None))

    def test_nonzero_exit_does_not_clean_up(self):
        process = MagicMock()
        process.wait.return_value = 4
        context = MagicMock()
        context.__enter__.return_value = process
        with patch.object(runner.subprocess, 'Popen', return_value=context), patch.object(runner.subprocess, 'run') as cleanup:
            self.assertEqual(runner.run_bounded(['mock'], io.BytesIO(), 10), (4, False, None))
            cleanup.assert_not_called()

    @unittest.skipUnless(sys.platform == 'win32', 'Windows process-tree cleanup')
    def test_timeout_removes_owned_child(self):
        code = ('import subprocess,sys,time; '
                'child=subprocess.Popen([sys.executable,"-c","import time; time.sleep(60)"]); '
                'print(child.pid,flush=True); time.sleep(60)')
        with tempfile.TemporaryFile() as log:
            result = runner.run_bounded([sys.executable, '-c', code], log, 2)
            self.assertEqual(result[:2], (124, True))
            log.seek(0)
            output = log.read().decode()
        child = int(output.splitlines()[0])
        probe = subprocess.run(['powershell', '-NoProfile', '-NonInteractive', '-Command',
            f'if (Get-Process -Id {child} -ErrorAction SilentlyContinue) {{ exit 1 }}'], capture_output=True)
        self.assertEqual(probe.returncode, 0, 'Owned child survived watchdog')
        self.assertIn('[audit harness] Wall-clock resource limit reached', output)


if __name__ == '__main__':
    unittest.main()
