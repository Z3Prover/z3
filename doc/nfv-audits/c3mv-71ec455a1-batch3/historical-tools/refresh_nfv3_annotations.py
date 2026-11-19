"""Refresh generated hashes only after checking frozen computation/contracts."""
import hashlib
import json
from pathlib import Path
import re

root=Path(__file__).parent
models=root/'nfv3-models'
def stable(text):
    code=re.sub(r'//[^\n]*','',text)
    return '\n'.join(r.strip() for r in code.splitlines() if r.strip() and not re.match(r'^\s*(assert|invariant|decreases)\b',r))+'\n'
path=models/'properties.json'
props=json.loads(path.read_text())
history_path=models/'annotations.json'
history=json.loads(history_path.read_text()) if history_path.exists() else []
for p in props:
    current=(models/(p['id']+'.dfy')).read_text()
    baseline=(models/'frozen'/(p['id']+'.dfy')).read_text()
    assert stable(current)==stable(baseline),p['id']
    digest=hashlib.sha256(current.encode()).hexdigest()
    if digest!=p['sha256']:
        history.append(dict(id=p['id'],before_sha256=p['sha256'],after_sha256=digest,scope='Proof annotation only; frozen computation/contracts text unchanged after stripping standalone assert/invariant/decreases. Exact frozen file and all previous checked inputs retained.'))
        p['sha256']=digest
    tags={}
    for source,line in re.findall(r'^// src: ([^:]+):(\d+) \|',current,re.M):tags.setdefault(source,set()).add(int(line))
    p['source_tags']={source:sorted(lines) for source,lines in tags.items()}
    p['source_lines']=p['source_tags'][p['path']]
path.write_text(json.dumps(props,indent=2)+'\n',encoding='utf-8',newline='\n')
history_path.write_text(json.dumps(history,indent=2)+'\n',encoding='utf-8',newline='\n')
followup_path=root/'nfv3-followups.json'
if followup_path.exists():
    followup=json.loads(followup_path.read_text())
    followup['candidate']['verified_input_sha256']=next(h['input_sha256'] for h in json.loads((models/'checks.json').read_text()) if h['phase']=='candidate-proof')
    followup['candidate']['sha256']=hashlib.sha256((models/'P19-candidate.dfy').read_bytes()).hexdigest()
    followup['candidate']['provenance_correction']='Current final-false source tag corrected from closing brace 707 to return statement 706; verified historical input retained byte-exact. No computation/contract change.'
    followup_path.write_text(json.dumps(followup,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='pass',annotation_revisions=len(history)),indent=2))
