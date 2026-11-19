"""Append-only, bounded verification of sealed batch-four mathematical models."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT=Path(__file__).parent
MODELS=ROOT/'nfv4-models'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stable(text):
    code=re.sub(r'//[^\n]*','',text)
    return '\n'.join(line.strip() for line in code.splitlines() if line.strip() and not re.match(r'^\s*(assert|invariant|decreases)\b',line))+'\n'


def goals(text,p,new_goals,pins=()):
    first=text.index('method '+p['entry_point']+'(')
    last=text.index('\n{',first)
    rows=[]
    for row in text[first:last].splitlines():
        if re.match(r'^\s*ensures ',row):
            assert rows[-1].startswith('// synth:')
            rows.pop()
        else:
            rows.append(row)
    tag=rows.pop()
    assert tag.startswith('// synth:')
    for pin in pins:
        rows.extend(['// synth: separate complete concrete-input pin','  requires '+pin])
    for goal in new_goals:
        rows.extend(['// synth: identified whole original or explicitly auxiliary goal','  ensures '+goal])
    rows.append(tag)
    return text[:first]+'\n'.join(rows)+text[last:]


def literal(value):
    if type(value) is bool:
        return str(value).lower()
    if type(value) is int:
        return str(value) if value>=0 else '('+str(value)+')'
    assert type(value) is list
    return '['+','.join(literal(v) for v in value)+']'


def drivers(text,p,examples):
    names=list(p['inputs'])
    for index,example in enumerate(examples,1):
        assert set(example['inputs'])==set(names)
        text+='\n// Independent concrete domain/caller, not a native execution.\nmethod ConcreteDomain'+str(index)+'()\n{\n'
        for name in names:
            text+='  var '+name+': '+p['inputs'][name]+' := '+literal(example['inputs'][name])+';\n'
        for clause in p['assumptions']:
            text+='  assert '+clause['clause']+';\n'
        outputs=','.join('out'+str(i) for i in range(len(p['outputs'])))
        text+='  var '+outputs+' := '+p['entry_point']+'('+','.join(names)+');\n}\n'
    return text


def verify(pid,kind,label,text,p,mbqi):
    checks=MODELS/'checks'
    checks.mkdir(exist_ok=True)
    history_path=MODELS/'checks.json'
    history=json.loads(history_path.read_text()) if history_path.exists() else []
    digest=hashlib.sha256(text.encode()).hexdigest()
    phase=(label+'-' if label else '')+kind
    old=next((h for h in reversed(history) if h['id']==pid and h['phase']==phase and h['input_sha256']==digest and h['mbqi']==mbqi),None)
    if old:
        print(json.dumps(dict(id=pid,phase=phase,retained=True,exit_code=old['exit_code'])),flush=True)
        return old['exit_code']==0
    name=f'{len(history)+1:03}-{pid}-{phase}'
    path=checks/(name+'.dfy')
    assert not path.exists()
    path.write_text(text,encoding='utf-8',newline='\n')
    command=[str(ROOT/'nfv-tools'/'dafny'/'Dafny.exe'),'verify',str(path),'--solver-path',str(ROOT/'nfv-tools'/'dafny'/'z3'/'bin'/'z3-4.12.1.exe'),'--verification-time-limit','30','--cores','2','--allow-warnings','--show-snippets','false']
    if mbqi:
        command+=['--solver-option','O:smt.mbqi=true']
    started=datetime.now(timezone.utc).isoformat()
    start=time.monotonic()
    completed=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
    log=path.with_suffix('.log')
    log.write_text(completed.stdout,encoding='utf-8',newline='\n')
    record=dict(sequence=len(history)+1,id=pid,kind=kind,phase=phase,started_utc=started,seconds=round(time.monotonic()-start,3),exit_code=completed.returncode,canonical_sha256=p['sha256'],input_sha256=sha(path),input=str(path.relative_to(MODELS)),log=str(log.relative_to(MODELS)),log_sha256=sha(log),command=command,mbqi=mbqi)
    history.append(record)
    history_path.write_text(json.dumps(history,indent=2)+'\n',encoding='utf-8',newline='\n')
    lines=completed.stdout.splitlines()
    print(json.dumps({k:record[k] for k in ['sequence','id','phase','seconds','exit_code','input']}),flush=True)
    print('\n'.join(lines[-18:]),flush=True)
    return completed.returncode==0


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--phase',required=True,choices=['validity','domain','proof','refute'])
    parser.add_argument('--select',nargs='+',default=['P20','P21','P22'])
    parser.add_argument('--label',default='')
    parser.add_argument('--mbqi',action='store_true')
    parser.add_argument('--example',type=int,default=0)
    args=parser.parse_args()
    seal=json.loads((ROOT/'nfv4-model-freeze.json').read_text())
    for f in seal['files']:
        assert sha(ROOT/f['path'])==f['sha256']
    assert sha(MODELS/'draft-checks.json')==seal['draft_history_sha256']
    props={p['id']:p for p in json.loads((MODELS/'frozen'/'properties.json').read_text())}
    failed=False
    for pid in args.select:
        p=props[pid]
        baseline=(MODELS/'frozen'/(pid+'.dfy')).read_text()
        text=(MODELS/(pid+'.dfy')).read_text()
        assert stable(text)==stable(baseline),'Only sound disclosed proof annotations may change after sealing'
        history=json.loads((MODELS/'checks.json').read_text()) if (MODELS/'checks.json').exists() else []
        if args.phase!='validity':
            assert any(h['id']==pid and h['kind']=='validity' and h['exit_code']==0 for h in history),'Property-free validity must pass first'
        if args.phase in ['proof','refute']:
            assert any(h['id']==pid and h['kind']=='domain' and h['exit_code']==0 for h in history),'Independent original domains must pass first'
        if args.phase=='validity':
            checked=goals(text,p,[])
        elif args.phase=='domain':
            checked=drivers(goals(text,p,[]),p,p['examples'])
        elif args.phase=='refute':
            assert any(h['id']==pid and h['kind']=='proof' for h in history),'Check original complete positive goal before refutation'
            example=p['examples'][args.example]
            pins=[name+' == '+literal(example['inputs'][name]) for name in p['inputs']]
            negative='!('+' && '.join('('+g+')' for g in p['original_ensures'])+')'
            checked=drivers(goals(text,p,[negative],pins),p,[example])
        else:
            checked=text
        failed|=not verify(pid,args.phase,args.label,checked,p,args.mbqi)
    raise SystemExit(1 if failed else 0)
