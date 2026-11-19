"""Check proof-annotation-only edits against the frozen baseline; refresh hashes."""
import hashlib
import json
from pathlib import Path
import re

root=Path(__file__).parent
models=root/'nfv2-models'
props=json.loads((models/'properties.json').read_text(encoding='utf-8'))
baseline=json.loads((models/'frozen'/'properties.json').read_text(encoding='utf-8'))
def computation(text):
    return '\n'.join(line.strip() for line in text.splitlines() if line.strip() and not line.strip().startswith(('//','assert ','invariant ','decreases ')))
for p,old in zip(props,baseline):
    assert p['id']==old['id']
    text=(models/(p['id']+'.dfy')).read_text(encoding='utf-8')
    frozen=(models/'frozen'/(p['id']+'.dfy')).read_text(encoding='utf-8')
    assert computation(text)==computation(frozen),(p['id'],'non-annotation edit')
    assert p['original_ensures']==old['original_ensures'] and p['assumptions']==old['assumptions']
    assert p['environment']==old['environment'],'helper contract or environment changed'
    p['sha256']=hashlib.sha256(text.encode()).hexdigest()
(models/'properties.json').write_text(json.dumps(props,indent=2)+'\n',encoding='utf-8',newline='\n')
print('PASS: all computations and contracts match frozen baseline; only proof annotations differ.')
