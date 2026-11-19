import copy
import ast
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify_nfv6 as runner


class ValidityDerivativeTests(unittest.TestCase):
    def test_positive_preserves_every_original_byte_and_rejects_validity_derivative(self):
        model, prop = runner.load_sealed()
        self.assertEqual(runner.original_positive(model, prop), model)
        with self.assertRaisesRegex(AssertionError, 'All frozen original postconditions'):
            runner.original_positive(runner.validity_only(model, prop), prop)

    def test_positive_rejects_each_replaced_conjunct(self):
        model, prop = runner.load_sealed()
        first = model.index('method DecimalGreater(')
        for clause in prop['original_ensures']:
            changed = model[:first] + model[first:].replace('  ensures ' + clause, '  ensures true', 1)
            with self.subTest(clause=clause), self.assertRaisesRegex(AssertionError, 'All frozen original postconditions'):
                runner.original_positive(changed, prop)

    def test_positive_requires_complete_matching_admitted_domain_group(self):
        _, prop = runner.load_sealed()
        ids = [e['id'] for e in prop['witnesses']]
        row = {'kind': 'domain', 'admitted': True, 'canonical_sha256': 'canonical', 'full_goal_candidate_sha256': 'candidate', 'domain_example_ids': ids, 'gate_validity_sequence': 2, 'sequence': 3}
        self.assertEqual(runner.prior_domains([row], 'canonical', 'candidate', ids, 2), row)
        for history, canonical, candidate, examples, validity in [([], 'canonical', 'candidate', ids, 2), ([dict(row, admitted=False)], 'canonical', 'candidate', ids, 2), ([row], 'other', 'candidate', ids, 2), ([row], 'canonical', 'other', ids, 2), ([row], 'canonical', 'candidate', ids[:-1], 2), ([row], 'canonical', 'candidate', ids, 1)]:
            with self.subTest(history=history, canonical=canonical, candidate=candidate, count=len(examples), validity=validity), self.assertRaisesRegex(AssertionError, 'full independent domain group'):
                runner.prior_domains(history, canonical, candidate, examples, validity)

    def test_domains_bind_all_inputs_without_positive_contracts(self):
        model, prop = runner.load_sealed()
        prefix = runner.validity_only(model, prop)
        checked = runner.domain_callers(prefix, prop)
        self.assertTrue(checked.startswith(prefix))
        callers = checked[len(prefix):].split('method ConcreteDomain')[1:]
        self.assertEqual(len(callers), len(prop['witnesses']))
        for caller, example in zip(callers, prop['witnesses'], strict=True):
            for item in prop['inputs']:
                lead = '  var ' + item['name'] + ': ' + item['type'] + ' := '
                row, = [line for line in caller.splitlines() if line.startswith(lead)]
                expression = row[len(lead):-1].replace('true', 'True').replace('false', 'False')
                self.assertEqual(ast.literal_eval(expression), example['inputs'][item['name']])
            self.assertNotIn('ensures ', caller)
            self.assertNotIn('assume ', caller)
            self.assertEqual(caller.count(' := DecimalGreater('), 1)

    def test_domain_generation_ignores_expected_outputs(self):
        model, prop = runner.load_sealed()
        changed = copy.deepcopy(prop)
        for example in changed['witnesses']:
            example['expected'] = {'deliberately_unusable': object()}
        prefix = runner.validity_only(model, prop)
        self.assertEqual(runner.domain_callers(prefix, prop), runner.domain_callers(prefix, changed))

    def test_domains_reject_unbound_input(self):
        model, prop = runner.load_sealed()
        changed = copy.deepcopy(prop)
        del changed['witnesses'][0]['inputs']['word']
        with self.assertRaisesRegex(AssertionError, 'bind every frozen input'):
            runner.domain_callers(runner.validity_only(model, prop), changed)

    def test_domain_gate_requires_admitted_matching_validity(self):
        row = {'kind': 'validity', 'admitted': True, 'canonical_sha256': 'canonical', 'full_goal_candidate_sha256': 'candidate', 'sequence': 2}
        self.assertEqual(runner.prior_validity([row], 'canonical', 'candidate'), row)
        for history, canonical, candidate in [([], 'canonical', 'candidate'), ([dict(row, admitted=False)], 'canonical', 'candidate'), ([row], 'different', 'candidate'), ([row], 'canonical', 'different')]:
            with self.subTest(history=history, canonical=canonical, candidate=candidate), self.assertRaisesRegex(AssertionError, 'validity must be admitted'):
                runner.prior_validity(history, canonical, candidate)

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
