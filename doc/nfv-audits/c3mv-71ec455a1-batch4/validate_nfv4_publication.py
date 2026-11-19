"""Read-only validation of the sealed report, complete evidence and outcomes."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--bundle',type=Path,default=Path(__file__).resolve().parent)
root=parser.parse_args().bundle.resolve()


def at(base,name):
    path=(base/Path(name.replace('\\','/'))).resolve()
    assert path.is_relative_to(base.resolve()) and path.is_file(),name
    return path


def load(path):
    return json.loads(path.read_text(encoding='utf-8'))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest=load(root/'manifest.json')
listed=set()
for item in manifest['files']:
    path=at(root,item['path'])
    assert not path.is_symlink()
    assert len(path.read_bytes())==item['bytes'] and sha(path)==item['sha256'],item['path']
    listed.add(path.relative_to(root))
assert listed=={p.relative_to(root) for p in root.rglob('*') if p.is_file() and p!=root/'manifest.json'}
exceptions=load(root/'export-notes.json')['raw_crlf_exceptions']
actual=sorted(p.as_posix() for p in listed if b'\r\n' in (root/p).read_bytes())
assert exceptions==actual
assert (root/'.gitattributes').read_text()=='* text eol=lf\n'+''.join(p+' -text\n' for p in exceptions)
models=root/'nfv4-models'
props=load(models/'properties.json')
checks=load(models/'checks.json')
drafts=load(models/'draft-checks.json')
results=load(root/'nfv4-results.json')
freeze=load(root/'nfv4-model-freeze.json')
selection=load(root/'nfv4-selection.json')
assert [p['id'] for p in props]==['P20','P21','P22']
assert len(checks)==3 and len(drafts)==20 and sum(c['exit_code']!=0 for c in drafts)==3
assert results['summary']['verified']==results['summary']['refuted']==results['summary']['domain_attempts']==0
assert results['summary']['type_check_or_audit_failure']==3
assert sha(models/'checks.json')==results['checks_sha256']
assert sha(models/'draft-checks.json')==freeze['draft_history_sha256']
assert sha(root/'nfv4-selection.json')==freeze['selection_sha256']=='7d7e9ff5bc259460e5dfc9b6892f7ccadc1fd8378fd10e970a585b07029bb4ce'
assert sha(root/'nfv4-model-freeze.json')==results['freeze_sha256']
for f in freeze['files']:
    assert sha(at(root,f['path']))==f['sha256']
for p,h in zip(props,checks):
    assert p['frozen_intent']==next(s for s in selection['properties'] if s['id']==p['id'])
    assert sha(models/(p['id']+'.dfy'))==p['sha256']
    assert (models/(p['id']+'.dfy')).read_bytes()==(models/'frozen'/(p['id']+'.dfy')).read_bytes()
    assert h['id']==p['id'] and h['kind']=='validity' and h['exit_code']==4
    assert sha(at(models,h['input']))==h['input_sha256'] and sha(at(models,h['log']))==h['log_sha256']
    baseline=(models/(p['id']+'.dfy')).read_text()
    first=baseline.index('method '+p['entry_point']+'(')
    last=baseline.index('\n{',first)
    header=baseline[first:last]
    assert re.findall(r'^\s*ensures ([^\n]*)',header,re.M)==p['original_ensures']
    assert re.findall(r'^\s*requires ([^\n]*)',header,re.M)==[a['clause'] for a in p['assumptions']]
    header,n=re.subn(r'^// synth:[^\n]*\n[ \t]*ensures [^\n]*\n','',header,flags=re.M)
    assert n==3 and at(models,h['input']).read_text()==baseline[:first]+header+baseline[last:]
    log=at(models,h['log']).read_text()
    assert 'Error: index out of range' in log
    command=h['command']
    assert command[command.index('--solver-path')+1].endswith('z3-4.12.1.exe')
    assert command[command.index('--cores')+1]=='2' and command[command.index('--verification-time-limit')+1]=='30'
for h in drafts:
    assert sha(at(models,h['log']))==h['log_sha256']
    for f in h['inputs']:
        assert sha(at(models,f['path']))==f['sha256']
for receipt_name in ['nfv4-verification-handoff.json','nfv4-selection-freeze.json']:
    receipt=load(root/receipt_name)
    for name,digest in receipt.get('files',receipt.get('source_handoffs',{})).items():
        assert sha(at(root,name))==digest
assert sha(root/'nfv4-modeling.md')==freeze['report_sha256']
source_check=subprocess.run([sys.executable,str(root/'check_nfv4_models.py'),'--provenance-only',str(models)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
assert source_check.returncode==0,source_check.stdout
prose=re.sub(r'```.*?```','',(root/'README.md').read_text(),flags=re.S)
for link in re.findall(r'\]\(([^)]+)\)',prose):
    if not link.startswith(('https://','http://')):
        at(root,link)
for path in root.rglob('*.py'):
    ast.parse(path.read_text(encoding='utf-8'),filename=str(path))
tools=load(root/'tool-validation'/'results.json')
assert tools['status']=='pass' and tools['live_verifier_invocations']==3 and tools['unit_exit']==tools['replay_exit']==0
replayed=load(root/'tool-validation'/'replay'/'results.json')
assert len(replayed)==3 and all(h['matched'] and h['actual_exit']==4 for h in replayed)
for h in replayed:
    assert sha(at(root/'tool-validation'/'replay',h['log']))==h['log_sha256']
assert 'Ran 2 tests' in (root/'tool-validation'/'unit-tests.log').read_text()
assert load(root/'nfv4-followups.json')['stop_schedule'] is False
print(json.dumps(dict(status='pass',files=len(listed)+1,audit_verifier_attempts=3,live_tool_verifier_invocations=3,whole_properties_verified=0,whole_properties_refuted=0,audit_failures=3,checks='Raw manifest/input/log/frozen bytes; unchanged computations/contracts; gate-aware outcomes; source anchors; Python syntax; links; live replay and mocked mismatch/hash tests.'),indent=2))
