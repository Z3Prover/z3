"""Read-only validation of this sealed manual NFV audit and raw evidence."""
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

root=Path(__file__).resolve().parent
load=lambda p:json.loads(p.read_text(encoding='utf-8'))
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
at=lambda base,name:base/Path(name.replace('\\','/'))
manifest=load(root/'manifest.json')
listed=set()
exception=Path('nfv3-models')/'drafts'/'001-provenance'/'check_nfv3_provenance.py'
for item in manifest['files']:
    p=at(root,item['path']).resolve()
    assert p.is_relative_to(root) and p.is_file()
    raw=p.read_bytes()
    assert len(raw)==item['bytes'] and digest(p)==item['sha256'],item['path']
    if p.relative_to(root)!=exception:assert b'\r\n' not in raw,item['path']
    listed.add(p.relative_to(root))
assert listed=={p.relative_to(root) for p in root.rglob('*') if p.is_file() and p!=root/'manifest.json'}
assert (root/'.gitattributes').read_text().splitlines()[-1]=='nfv3-models/drafts/001-provenance/check_nfv3_provenance.py -text'
models=root/'nfv3-models'
checks=load(models/'checks.json')
props=load(models/'properties.json')
results=load(root/'nfv3-results.json')
assert len(checks)==18 and len(props)==2
assert sum(c['exit_code']==0 for c in checks)==12
assert sum('timed out' in at(models,c['log']).read_text() for c in checks)==1
assert [(p['id'],p['nfv_outcome']) for p in results['outcomes']]==[('P18','resources_exhausted'),('P19','refuted')]
assert digest(models/'checks.json')==results['history_sha256']
assert digest(models/'properties.json')==results['metadata_sha256']
assert digest(models/'provenance.json')==results['provenance_sha256']
for c in checks:
    assert digest(at(models,c['input']))==c['input_sha256']
    assert digest(at(models,c['log']))==c['log_sha256']
    command=c['command']
    assert command[command.index('--solver-path')+1].endswith('z3-4.12.1.exe')
    assert command[command.index('--cores')+1]=='2' and command[command.index('--verification-time-limit')+1]=='30'
    if c['exit_code']==0:assert re.search(r'verified, 0 errors',at(models,c['log']).read_text())
for c in load(models/'draft-checks.json'):
    for f in c['inputs']:assert digest(at(models,f['path']))==f['sha256']
    assert digest(at(models,c['log']))==c['log_sha256']
freeze=load(root/'nfv3-model-freeze.json')
assert digest(root/'nfv3-selection.json')==freeze['selection_sha256']=='0beb5b435b99a07ee85fbc6830028ee477f8b79bbd243c1f254887ef9b0da13e'
for f in freeze['files']:assert digest(at(root,f['path']))==f['sha256']
def stable(text):
    code=re.sub(r'//[^\n]*','',text)
    return '\n'.join(r.strip() for r in code.splitlines() if r.strip() and not re.match(r'^\s*(assert|invariant|decreases)\b',r))+'\n'
for p,old in zip(props,load(models/'frozen'/'properties.json')):
    current=models/(p['id']+'.dfy')
    assert digest(current)==p['sha256']
    assert p['id']==old['id'] and p['assumptions']==old['assumptions'] and p['environment']==old['environment'] and p['original_ensures']==old['original_ensures']
    assert stable(current.read_text())==stable((models/'frozen'/current.name).read_text())
p=next(p for p in props if p['id']=='P19')
ref=next(c for c in checks if c['phase']=='visited-prefix-mbqi-refute')
text=at(models,ref['input']).read_text()
start=text.index('method '+p['entry_point']); header=text[start:text.index('\n{',start)]
assert re.findall(r'^\s*ensures (.+)$',header,re.M)==['!('+' && '.join('('+g+')' for g in p['original_ensures'])+')']
assert len(re.findall(r'^\s*requires (.+)$',header,re.M))==len(p['assumptions'])+8
assert 'method ConcreteDomain0()' in text and ref['exit_code']==0
follow=load(root/'nfv3-followups.json')
assert follow['shorter_implication'] and follow['shorter_refutation'] and not follow['optional_restrictions']
assert all(follow['candidate'][n] for n in ('validity','domain','whole_original_property','helpers_and_original_contracts_unchanged'))
assert digest(models/'P19-candidate.dfy')==follow['candidate']['sha256']
source_check=subprocess.run([sys.executable,str(root/'check_nfv3_provenance.py'),'--models',str(models),'--inventory',str(root/'nfv3-coverage-source-inventory.json')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
assert source_check.returncode==0,source_check.stdout
prose=re.sub(r'```.*?```','',(root/'README.md').read_text(),flags=re.S)
for link in re.findall(r'\]\(([^)]+)\)',prose):
    if not link.startswith(('https://','http://')):assert at(root,link).is_file(),link
for path in root.rglob('*.py'):ast.parse(path.read_text(encoding='utf-8'))
tool=load(root/'tool-validation'/'results.json')
assert tool['status']=='pass' and tool['live_verifier_invocations']==5
assert tool['replay_exit']==0 and tool['mismatch_exit']==1
assert all(r['matched'] for r in load(root/'tool-validation'/'replay'/'results.json'))
mixed=load(root/'tool-validation'/'mismatch'/'results.json')
assert len(mixed)==2 and not mixed[0]['matched'] and mixed[1]['matched']
print(json.dumps(dict(status='pass',published_files=len(listed)+1,audit_verifier_attempts=18,tool_verifier_invocations=5,outcomes=dict(P18='resources_exhausted',P19='refuted local missed-hit model contract'),checks='Raw manifest/input/log/frozen bytes, contracts/computation, outcomes, provenance, report links, Python syntax, replay and mismatch propagation'),indent=2))
