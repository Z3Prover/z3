"""Preserve the resolved modeling baseline before any property proof attempt."""
import hashlib
import json
from pathlib import Path
import shutil

root=Path(__file__).parent
models=root/'nfv2-models'
selection=root/'nfv2-selection.json'
assert hashlib.sha256(selection.read_bytes()).hexdigest()=='be379560dc9f91cc8650d5abaa0de4e4680748d54c81be5385cc69e2131a1685'
props=json.loads((models/'properties.json').read_text(encoding='utf-8'))
history=json.loads((models/'draft-checks.json').read_text(encoding='utf-8'))
files=['properties.json','sources.json']+[p['id']+'.dfy' for p in props]
for p in props:
    last=next(r for r in reversed(history) if r['id']==p['id'] and r['phase']=='resolve')
    assert last['exit_code']==0 and last['input_sha256']==p['sha256']
    assert hashlib.sha256((models/(p['id']+'.dfy')).read_bytes()).hexdigest()==p['sha256']
baseline=models/'frozen'
baseline.mkdir(exist_ok=False)
for name in files:
    shutil.copyfile(models/name,baseline/name)
freeze=dict(selection_sha256=hashlib.sha256(selection.read_bytes()).hexdigest(),
    audited_head='71ec455a18702fe695d0c924a535ff9f385bd58d',
    phase='resolved before any property-free validity, concrete domain, or original-property verification',
    policy='Keep entry computation, non-proof helper computation, helper contracts and complete entry contracts unchanged. Only sound proof annotations/erased proof bodies may change; compare explicitly with these exact baseline inputs and preserve every attempt. Candidate repairs may change entry computation only and must retain the full original contracts and helpers.',
    files={name:hashlib.sha256((baseline/name).read_bytes()).hexdigest() for name in files},
    properties=[dict(id=p['id'],entry_point=p['entry_point'],requires=p['assumptions'],ensures=p['original_ensures'],helpers=p['environment']) for p in props])
target=root/'nfv2-model-freeze.json'
assert not target.exists()
target.write_text(json.dumps(freeze,indent=2)+'\n',encoding='utf-8',newline='\n')
for name,digest in freeze['files'].items():
    assert hashlib.sha256((baseline/name).read_bytes()).hexdigest()==digest
print(json.dumps(dict(status='frozen',models=len(props),baseline_files=len(files),manifest_sha256=hashlib.sha256(target.read_bytes()).hexdigest()),indent=2))
