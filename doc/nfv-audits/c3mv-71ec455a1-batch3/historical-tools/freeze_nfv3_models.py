"""Seal exact draft-resolved models and computational/contract fingerprints."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import re
import shutil

root=Path(__file__).parent
models=root/'nfv3-models'
frozen=models/'frozen'
target=root/'nfv3-model-freeze.json'
assert not frozen.exists() and not target.exists()
selection=root/'nfv3-selection.json'
assert hashlib.sha256(selection.read_bytes()).hexdigest()=='0beb5b435b99a07ee85fbc6830028ee477f8b79bbd243c1f254887ef9b0da13e'
props=json.loads((models/'properties.json').read_text())
history=json.loads((models/'draft-checks.json').read_text())
assert {p['id'] for p in props}=={'P18','P19'}
assert history[-3]['phase']=='provenance' and all(h['exit_code']==0 for h in history[-3:])
for p,h in zip(props,history[-2:]):
    raw=(models/(p['id']+'.dfy')).read_bytes()
    assert h['id']==p['id'] and h['phase']=='resolve'
    assert hashlib.sha256(raw).hexdigest()==p['sha256']==h['inputs'][0]['sha256']
frozen.mkdir()
files=[]
for path in [models/'properties.json',models/'sources.json']+[models/(p['id']+'.dfy') for p in props]:
    shutil.copyfile(path,frozen/path.name)
    files.append(dict(path=str((frozen/path.name).relative_to(root)),sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
fingerprints=[]
for p in props:
    code=re.sub(r'//[^\n]*','',(models/(p['id']+'.dfy')).read_text())
    stable='\n'.join(r.strip() for r in code.splitlines() if r.strip() and not re.match(r'^\s*(assert|invariant|decreases)\b',r))+'\n'
    fingerprints.append(dict(id=p['id'],computation_and_contract_sha256=hashlib.sha256(stable.encode()).hexdigest(),original_ensures=p['original_ensures'],requires=[a['clause'] for a in p['assumptions']],helper_contracts=[dict(name=e['name'],requires=e['requires'],ensures=e['ensures']) for e in p['environment']]))
receipt=dict(recorded_utc=datetime.now(timezone.utc).isoformat(),selection_sha256=hashlib.sha256(selection.read_bytes()).hexdigest(),head='71ec455a18702fe695d0c924a535ff9f385bd58d',master='c2460a558fc6fee3cf15cfebd2d3f642ebf77770',files=files,properties=fingerprints,phase='Modeling complete: provenance and resolution only, no Dafny verification yet',new_draft_checks=len(history),draft_failures=sum(h['exit_code']!=0 for h in history),new_verifier_attempts=0,policy='Keep all raw frozen files immutable. Computation, helper contracts, entry domains, complete positive goals and original examples stay frozen. Only disclosed proof annotations may change; a proof gap is not refutation. Fingerprint is an additional textual guard, not a proof of annotation-only equivalence or source correctness.')
target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='sealed',properties=[p['id'] for p in props],files=len(files),draft_checks=len(history),draft_failures=receipt['draft_failures'],new_verifier_attempts=0,freeze_sha256=hashlib.sha256(target.read_bytes()).hexdigest()),indent=2))
