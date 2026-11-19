"""Read-only validation of this sealed, manually authored NFV audit bundle."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

root=Path(__file__).resolve().parent
digest=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p: json.loads(p.read_text(encoding='utf-8'))
at=lambda base,name: base/Path(name.replace('\\','/'))
manifest=load(root/'manifest.json')
listed=set()
for entry in manifest['files']:
    relative=Path(entry['path'].replace('\\','/'))
    path=(root/relative).resolve()
    assert path.is_relative_to(root)
    raw=path.read_bytes()
    assert len(raw)==entry['bytes'] and digest(path)==entry['sha256'],entry['path']
    assert b'\r\n' not in raw,(entry['path'],'LF stability')
    listed.add(path.relative_to(root))
actual={p.relative_to(root) for p in root.rglob('*') if p.is_file() and p!=root/'manifest.json'}
assert listed==actual,listed^actual
models=root/'nfv2-models'
props=load(models/'properties.json')
checks=load(models/'checks.json')
results=load(root/'nfv2-results.json')
assert len(props)==7 and len(checks)==42
assert (results['verified'],results['refuted'],results['unresolved'])==(4,2,1)
assert sum(c['exit_code']==0 for c in checks)==32
assert sum('timed out' in at(models,c['log']).read_text(encoding='utf-8') for c in checks)==1
for check in checks:
    assert digest(at(models,check['input']))==check['input_sha256'],check['input']
    log=at(models,check['log']).read_text(encoding='utf-8')
    assert log.strip()
    if check['exit_code']==0:
        assert re.search(r'finished with \d+ verified, 0 errors',log) and 'time out' not in log and 'timed out' not in log
    command=check['command']
    assert Path(command[command.index('--solver-path')+1].replace('\\','/')).name=='z3-4.12.1.exe'
    assert command[command.index('--cores')+1]=='2'
    assert command[command.index('--verification-time-limit')+1]=='30'
freeze=load(root/'nfv2-model-freeze.json')
assert digest(root/'nfv2-selection.json')==freeze['selection_sha256']
selection=load(root/'nfv2-selection-freeze.json')
assert digest(root/'nfv2-selection-source-inventory.json')==selection['source_inventory_sha256']
for name,value in freeze['files'].items():
    assert digest(models/'frozen'/name)==value,name
def computation(text):
    return '\n'.join(l.strip() for l in text.splitlines() if l.strip() and not l.strip().startswith(('//','assert ','invariant ','decreases ')))
baseline=load(models/'frozen'/'properties.json')
for p,old in zip(props,baseline):
    assert p['id']==old['id']
    assert digest(models/(p['id']+'.dfy'))==p['sha256']
    assert p['assumptions']==old['assumptions'] and p['environment']==old['environment'] and p['original_ensures']==old['original_ensures']
    assert computation((models/(p['id']+'.dfy')).read_text(encoding='utf-8'))==computation((models/'frozen'/(p['id']+'.dfy')).read_text(encoding='utf-8'))
for p in results['properties']:
    canonical=next(q for q in props if q['id']==p['id'])
    assert canonical['sha256']==p['canonical_sha256']
    for field in ('validity','domain','original_positive_attempt','primary_evidence'):
        record=next(c for c in checks if c['input']==p[field])
        if field!='original_positive_attempt' and not (field=='primary_evidence' and p['id']=='P13'):
            assert record['exit_code']==0
    if p['id']=='P13':assert p['nfv_outcome']=='audit_failure'
drafts=load(models/'draft-checks.json')
assert len(drafts)==16
for check in drafts:
    assert at(models,check['log']).is_file()
    if check['phase']=='resolve':
        assert digest(models/'drafts'/(check['input']+'.dfy'))==check['input_sha256']
prose=re.sub(r'```.*?```','',(root/'README.md').read_text(encoding='utf-8'),flags=re.S)
for link in re.findall(r'\]\(([^)]+)\)',prose):
    if not link.startswith(('https://','http://')):
        assert (root/Path(link)).is_file(),link
for script in root.rglob('*.py'):
    compile(script.read_text(encoding='utf-8'),str(script),'exec')
smoke=load(root/'tool-validation'/'results.json')
assert smoke['status']=='pass' and smoke['live_verifier_invocations']==5
assert smoke['mixed_runner_exit']==1 and smoke['successful_runner_exit']==0 and smoke['replay_exit']==0
replay=load(root/'tool-validation'/'replay'/'results.json')
assert len(replay)==2 and all(r['matched'] for r in replay)
runner=root/'tool-validation'/'runner-models'
runner_checks=load(runner/'checks.json')
assert len(runner_checks)==3
for check in runner_checks:
    assert digest(at(runner,check['input']))==check['input_sha256']
    assert at(runner,check['log']).is_file()
check=subprocess.run([sys.executable,str(root/'check_nfv_provenance.py')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',cwd=root)
assert check.returncode==0,check.stdout
assert sum(p['source_tags'] for p in json.loads(check.stdout)['properties'])==171
print(json.dumps(dict(status='pass',published_files=len(listed)+1,audit_verification_attempts=42,publication_tool_verifier_invocations=5,whole_properties=dict(verified=4,refuted=2,unresolved=1),checks='manifest, LF bytes, checked inputs/logs, frozen domains/contracts/computation, outcomes, provenance, report links, Python syntax, replay and runner exits'),indent=2))
