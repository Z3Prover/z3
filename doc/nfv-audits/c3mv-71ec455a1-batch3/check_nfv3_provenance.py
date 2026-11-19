"""Local exact-tag and metadata checks, not source equivalence/upstream gates."""
import argparse
import hashlib
import json
from pathlib import Path
import re

parser=argparse.ArgumentParser()
parser.add_argument('--models',type=Path,required=True)
parser.add_argument('--inventory',type=Path,required=True)
args=parser.parse_args()
assert hashlib.sha256(args.inventory.read_bytes()).hexdigest()=='d33911bd8dde877a572a5ad435e56574b46965c98e3a4836abc2e77392964824'
sources={f['path']:{r['line']:r['text'] for r in f['excerpts']} for f in json.loads(args.inventory.read_text())['files']}
summaries=[]
for p in json.loads((args.models/'properties.json').read_text()):
    raw=(args.models/(p['id']+'.dfy')).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==p['sha256']
    model=raw.decode()
    code=re.sub(r'//[^\n]*','',model)
    assert not re.search(r'\b(assume|expect|include|import|export|module|extern|abstract|opaque|iterator|yield|const|type|newtype|trait|codatatype)\b',code)
    assert '{:' not in code and not re.search(r'\bdecreases\s+\*',code)
    pending=False; synth=False; count=0
    for row in model.splitlines():
        if not row.strip():continue
        tag=re.fullmatch(r'// src: ([^:]+):(\d+) \| (.*)',row)
        if tag:
            path,n,quote=tag.groups()
            assert sources[path][int(n)].strip()==quote,(p['id'],row)
            assert path in p['required_context']
            pending=True; synth=False; count+=1
        elif row.startswith('// synth: '):
            assert not pending,(p['id'],'discarded source tag')
            pending=True; synth=True
        else:
            assert pending,(p['id'],'untagged',row)
            if synth:assert re.fullmatch(r'[{};]+|(?:requires|ensures|invariant|assert|decreases|reads|modifies)\b.*',row.strip()),(p['id'],'synthetic computation',row)
            pending=False
    assert not pending
    signature=code[code.index('method '+p['entry_point']):].split('\n{',1)[0]
    assert re.findall(r'^\s*ensures (.+)$',signature,re.M)==p['original_ensures']
    assert re.findall(r'^\s*requires (.+)$',signature,re.M)==[a['clause'] for a in p['assumptions']]
    names=set(re.findall(r'^\s*(?:function|predicate|method|lemma)\s+(\w+)\(',code,re.M))-{p['entry_point']}
    assert names=={e['name'] for e in p['environment']}
    assert all(e['source'] and e['contract_status'].startswith('Must verify body') for e in p['environment'])
    assert all(a['origin']=='inferred' for a in p['assumptions'])
    assert p['frozen_selection_sha256']=='0beb5b435b99a07ee85fbc6830028ee477f8b79bbd243c1f254887ef9b0da13e'
    summaries.append(dict(id=p['id'],source_tags=count,helpers=len(names),requires=len(p['assumptions']),sha256=p['sha256']))
print(json.dumps(dict(status='pass',scope='exact source tags and metadata; not source equivalence, native safety or complete upstream admission gates',properties=summaries),indent=2))
