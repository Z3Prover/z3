"""Preserve every batch-five provenance/resolve draft and complete diagnostics."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT=Path(__file__).parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def provenance(folder):
    props=json.loads((folder/'properties.json').read_text())
    sources=json.loads((folder/'sources.json').read_text())
    anchors={(f['path'],r['line']):r['text'].strip() for f in sources['files'] for r in f['excerpts']}
    counts=[]
    for prop in props:
        raw=(folder/(prop['id']+'.dfy')).read_bytes()
        assert sha(raw)==prop['sha256']
        model=raw.decode(); code=re.sub(r'//[^\n]*','',model)
        assert not re.search(r'\b(assume|axiom|include|import|module|newtype|type)\b|\{:|decreases\s+\*',code)
        tags=0
        for line in model.splitlines():
            if line.startswith('// src: '):
                m=re.fullmatch(r'// src: (.+):(\d+) \| (.*)',line)
                assert m and anchors[(m[1],int(m[2]))]==m[3]
                tags+=1
        lines=model.splitlines()
        for i,line in enumerate(lines):
            if not line.strip() or line.lstrip().startswith('//'): continue
            assert i>0 and (lines[i-1].startswith('// src: ') or lines[i-1].startswith('// synth: ')), (prop['id'],i+1)
            if lines[i-1].startswith('// synth: '):
                assert line.strip() in {'{','}'} or re.match(r'^\s*(requires|ensures|invariant|decreases|assert)\b',line)
        signature=code[code.index('method '+prop['entry_point']):].split('\n{',1)[0]
        assert re.findall(r'^\s*requires (.+)$',signature,re.M)==[a['clause'] for a in prop['assumptions']]
        assert re.findall(r'^\s*ensures (.+)$',signature,re.M)==prop['original_ensures']
        assert len(prop['original_ensures'])==3
        declarations=re.findall(r'^(?:ghost )?(?:function|predicate|method|lemma) (\w+)\(',code,re.M)
        assert len(declarations)==len(set(declarations))
        assert set(declarations)=={prop['entry_point']}|{h['name'] for h in prop['environment']}
        for h in prop['environment']:
            assert h['body_required'] and h['source_anchors']
            for a in h['source_anchors']:
                assert anchors[(a['path'],a['line'])]==a['text']
        for ex in prop['examples']:
            assert set(ex['inputs'])==set(prop['inputs'])
        counts.append(dict(id=prop['id'],source_tags=tags,helpers=len(prop['environment']),requires=len(prop['assumptions']),examples=len(prop['examples'])))
    print(json.dumps(dict(status='pass',scope='Local anchor/metadata/forbidden-construct checks, not full upstream parser/admission or translation equivalence',properties=counts),indent=2))


def literal(value):
    if type(value) is bool: return str(value).lower()
    if type(value) is int: return str(value)
    return '['+','.join(literal(v) for v in value)+']'


def make_domain(prop, model):
    start=model.index('method '+prop['entry_point'])
    opening=model.index('\n{',start)
    header=model[start:opening]
    header=re.sub(r'^\s*ensures [^\n]*\n?','',header,flags=re.M)
    validity=model[:start]+header+model[opening:]
    drivers=[]
    names=list(prop['inputs'])
    for n,example in enumerate(prop['examples'],1):
        values=example['inputs']
        drivers.append(f'\n// Independent domain harness {n}: {example["label"]}\nmethod ConcreteDomain{n}()\n{{')
        for key in names:
            drivers.append(f'  var {key}: {prop["inputs"][key]} := {literal(values[key])};')
        for clause in prop['assumptions']:
            drivers.append('  assert '+clause['clause']+';')
        args=','.join(names)
        outputs=','.join('out'+str(i) for i in range(len(prop['outputs'])))
        drivers.append(f'  var {outputs} := {prop["entry_point"]}({args});\n}}')
    return validity+'\n'.join(drivers)+'\n'


if len(sys.argv)>1 and sys.argv[1]=='--provenance-only':
    provenance(Path(sys.argv[2]))
    raise SystemExit(0)

MODELS=ROOT/'nfv5-models'
DRAFTS=MODELS/'drafts'
DRAFTS.mkdir(exist_ok=True)
history_path=MODELS/'draft-checks.json'
history=json.loads(history_path.read_text()) if history_path.exists() else []
props=json.loads((MODELS/'properties.json').read_text())
failed=False


def run(pid, phase, command, folder, inputs):
    global failed
    begin=time.monotonic()
    completed=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
    log=folder/'output.log'
    log.write_text(completed.stdout,encoding='utf-8',newline='\n')
    record=dict(sequence=len(history)+1,id=pid,phase=phase,recorded_utc=datetime.now(timezone.utc).isoformat(),
        seconds=round(time.monotonic()-begin,3),exit_code=completed.returncode,command=command,
        inputs=[dict(path=str(p.relative_to(MODELS)),sha256=sha(p.read_bytes())) for p in inputs],
        log=str(log.relative_to(MODELS)),log_sha256=sha(log.read_bytes()))
    history.append(record)
    history_path.write_text(json.dumps(history,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:record[k] for k in ('sequence','id','phase','seconds','exit_code')}),flush=True)
    if completed.returncode:
        failed=True
        print(completed.stdout,flush=True)


snapshot=DRAFTS/f'{len(history)+1:03}-provenance'
snapshot.mkdir()
for path in [MODELS/'properties.json',MODELS/'sources.json',Path(__file__)]+[MODELS/(p['id']+'.dfy') for p in props]:
    shutil.copyfile(path,snapshot/path.name)
run('all','provenance',[sys.executable,str(snapshot/Path(__file__).name),'--provenance-only',str(snapshot)],snapshot,list(snapshot.iterdir()))
for prop in props:
    if '--only-provenance' in sys.argv:
        break
    if '--ids' in sys.argv and prop['id'] not in sys.argv[sys.argv.index('--ids')+1].split(','):
        continue
    for phase in ['resolve','domain-resolve']:
        folder=DRAFTS/f'{len(history)+1:03}-{prop["id"]}-{phase}'
        folder.mkdir()
        source=(MODELS/(prop['id']+'.dfy')).read_text()
        if phase=='domain-resolve': source=make_domain(prop,source)
        path=folder/(prop['id']+'.dfy')
        path.write_text(source,encoding='utf-8',newline='\n')
        if phase=='domain-resolve':
            shutil.copyfile(path,MODELS/(prop['id']+'-domain.dfy'))
        run(prop['id'],phase,[str(ROOT/'nfv-tools'/'dafny'/'Dafny.exe'),'resolve',str(path),'--allow-warnings','--show-snippets','false'],folder,[path])
raise SystemExit(1 if failed else 0)
