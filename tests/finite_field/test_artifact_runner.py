#!/usr/bin/env python3
"""Regression for large-input delivery across the RSS sampling interruptions."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
from benchmark_artifacts import run, _run_supervised, infrastructure_error
import benchmark_ff_optimizations


class RunnerTest(unittest.TestCase):
    @unittest.skipUnless(sys.version_info >= (3, 14), 'runner requires Python 3.14+')
    def test_delayed_reader_gets_complete_large_input(self):
        # A pipe cannot hold this payload. The reader's delay forces several
        # communicate() timeouts before the remaining input can be delivered.
        child = ('import sys,time; time.sleep(.2); data=sys.stdin.read(); '
                 'assert len(data)==1048576; print("unsat")')
        result = run(dict(command=[sys.executable, '-c', child], smt='x'*1048576,
                          timeout=3, checks=1))
        self.assertEqual(result['result'], 'unsat', result)

    @unittest.skipUnless(sys.version_info >= (3, 14), 'runner requires Python 3.14+')
    def test_supervisor_timeout_kills_and_reaps_solver(self):
        with tempfile.TemporaryDirectory() as directory:
            pidfile = Path(directory)/'pids.json'
            # Ignore TERM in the solver: the worker's finally must kill and reap
            # it. This intentionally trips the outer guard before the solver's
            # own 30-second timeout, without waiting for a real host disturbance.
            child = ('import json,os,signal,sys,time; '
                     'signal.signal(signal.SIGTERM, signal.SIG_IGN); '
                     'open(sys.argv[1],"w").write(json.dumps([os.getpid(),os.getppid(),os.getpgrp()])); '
                     'time.sleep(30)')
            result = _run_supervised(dict(command=[sys.executable, '-c', child, str(pidfile)],
                                         smt='', timeout=30, checks=1), .5)
            self.assertEqual(result['result'], 'infrastructure_error', result)
            self.assertEqual(result['infrastructure_kind'], 'supervisor_timeout', result)
            self.assertEqual(result['answers'], [])
            self.assertTrue(pidfile.exists(), 'test child never started')
            solver_pid, worker_pid, group = json.loads(pidfile.read_text())
            self.assertEqual(worker_pid, group)
            for pid in [solver_pid, worker_pid]:
                with self.assertRaises(ProcessLookupError, msg=f'process {pid} leaked'):
                    os.kill(pid, 0)
            with self.assertRaises(ProcessLookupError):
                os.killpg(group, 0)

    @unittest.skipUnless(sys.version_info >= (3, 14), 'runner requires Python 3.14+')
    def test_solver_timeout_remains_distinct(self):
        result = run(dict(command=[sys.executable, '-c', 'import time; time.sleep(2)'],
                          smt='', timeout=.1, checks=1))
        self.assertEqual(result['result'], 'timeout', result)
        self.assertNotIn('infrastructure_kind', result)

    @unittest.skipUnless(sys.version_info >= (3, 14), 'runner requires Python 3.14+')
    def test_worker_failure_is_structured(self):
        result = run(dict(command=['/definitely/missing/benchmark-test-solver'],
                          smt='', timeout=.1, checks=1))
        self.assertEqual(result['result'], 'infrastructure_error', result)
        self.assertEqual(result['infrastructure_kind'], 'worker_exit', result)
        self.assertIn('FileNotFoundError', result['stderr'])

    def test_optimization_journal_survives_failure_and_refuses_unsafe_resume(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root/'case.smt2'; source.write_text('(check-sat)\n')
            manifest = root/'manifest.json'
            manifest.write_text(json.dumps([dict(case='first', family='test', path=str(source)),
                                           dict(case='second', family='test', path=str(source))]))
            configs = root/'configs.json'
            configs.write_text(json.dumps(dict(test=dict(binary=sys.executable))))
            out = root/'results'
            argv = ['benchmark_ff_optimizations', '--manifest', str(manifest), '--configs',
                    str(configs), '--out', str(out), '--jobs', '1']
            responses = [infrastructure_error('supervisor_timeout', 'injected worker failure'),
                         dict(result='unsat', answers=['unsat'], seconds=.01, stdout='', stderr='')]
            with patch.object(sys, 'argv', argv), patch.object(benchmark_ff_optimizations, 'run', side_effect=responses):
                with self.assertRaisesRegex(SystemExit, '1 infrastructure errors recorded'):
                    benchmark_ff_optimizations.main()
            journal = (out/'runs.jsonl').read_text()
            rows = list(map(json.loads, journal.splitlines()))
            self.assertEqual([row['result'] for row in rows], ['infrastructure_error', 'unsat'])
            self.assertEqual({row['case'] for row in rows}, {'first', 'second'})
            with patch.object(sys, 'argv', argv), patch.object(benchmark_ff_optimizations, 'run') as rerun:
                with self.assertRaisesRegex(SystemExit, 'new output directory'):
                    benchmark_ff_optimizations.main()
                rerun.assert_not_called()
            self.assertEqual((out/'runs.jsonl').read_text(), journal)


if __name__ == '__main__': unittest.main()
