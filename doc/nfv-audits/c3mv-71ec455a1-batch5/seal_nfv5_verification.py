"""Seal completed verification artifacts without rerunning the verifier."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).parent
REPO = Path(r'C:\z3seq')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '--no-pager', *args], cwd=REPO).decode().strip()


if __name__ == '__main__':
    target = ROOT / 'nfv5-verification-handoff.json'
    assert not target.exists(), 'Do not overwrite a completed handoff'
    results = json.loads((ROOT / 'nfv5-results.json').read_text())
    assert sha(ROOT / 'nfv5-models' / 'checks.json') == results['checks_sha256']
    assert sha(ROOT / 'nfv5-model-freeze.json') == results['freeze_sha256']
    assert sha(ROOT / 'nfv5-attempt13-resource-intervention.json') == results['resource_intervention_sha256']
    assert results['summary']['verified'] == results['summary']['refuted'] == 0
    assert results['summary']['verifier_attempts'] == 16
    assert results['summary']['resources_exhausted'] == 3
    assert results['summary']['admitted_examples'] == 4
    expected = dict(branch='c3mv', head='f975e94d9830bcca332b309df422b364c6e99191',
        source_tree='caa5a9922f074f9f4adc8f7c98e1685be9626503',
        stash='7af7fad70e9cea38601c67ff00d89f6b5576c2d6')
    actual = dict(branch=git('branch', '--show-current'), head=git('rev-parse', 'HEAD'),
        source_tree=git('rev-parse', 'HEAD:src'), stash=git('rev-parse', 'refs/stash'))
    assert actual == expected and not git('status', '--porcelain=v1', '-uall')
    assert git('rev-parse', 'HEAD:doc/nfv-audits') == git('rev-parse', expected['head'] + ':doc/nfv-audits')
    report = ROOT / 'nfv5-verification.md'
    for link in re.findall(r'\]\(([^)]+)\)', report.read_text()):
        assert (report.parent / link).is_file(), link
    names = ['nfv5-verification.md', 'nfv5-results.json', 'nfv5-followups.json',
        'nfv5-model-freeze.json', 'nfv5-retranslation-plan.json', 'nfv5-models/checks.json',
        'nfv5-attempt13-resource-intervention.json', 'verify_nfv5.py',
        'finish_nfv5_verification.py', 'seal_nfv5_verification.py', 'test_nfv5_watchdog.py']
    files = []
    for name in names:
        path = ROOT / name
        if path.suffix == '.py':
            ast.parse(path.read_text(encoding='utf-8-sig'), filename=name)
        files.append(dict(path=name, sha256=sha(path)))
    receipt = dict(stage='nfv5-verify', status='done', recorded_utc=datetime.now(timezone.utc).isoformat(),
        files=files, summary=results['summary'], repository_preservation=actual,
        watchdog_tests=dict(command='python -B test_nfv5_watchdog.py -v', passed=3, failed=0,
            seconds=4.806, execution='Trusted Python parent/child harness only; no audited source execution'),
        next_stage='nfv5-publish', schedule_id=2, stop_schedule=False,
        publication_notes=['Preserve raw historical bytes and explicit line-ending exceptions.',
            'Replay retains isolation and wall resource metadata; expensive interrupted checks opt-in only.',
            'Never count internal obligations or partial domains as whole verified properties.',
            'Preserve all four prior publications and source/stash; continue audit after publication.'])
    target.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(json.dumps(dict(handoff=str(target), sha256=sha(target), summary=results['summary']), indent=2))
