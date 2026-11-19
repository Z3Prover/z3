"""Bounded replayable batch-3 model checks; never run inspected native code."""
import argparse
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

root=Path(__file__).parent
models=root/'nfv3-models'
def signature(text,entry):
    match=re.search(r'^method '+re.escape(entry)+r'\(',text,re.M)
    assert match
    return match.start(),text.index('\n{',match.start())
def goals(text,p,new_goals,pins=()):
    first,last=signature(text,p['entry_point']); rows=[]
    for row in text[first:last].splitlines():
        if re.match(r'^\s*ensures ',row):
            assert rows[-1].startswith('// synth:'); rows.pop()
        else:rows.append(row)
    tag=rows.pop(); assert tag.startswith('// synth:')
    for pin in pins:rows.extend(['// synth: independent concrete input domain pin','  requires '+pin])
    for goal in new_goals:rows.extend(['// synth: explicitly identified complete or auxiliary check goal','  ensures '+goal])
    rows.append(tag)
    return text[:first]+'\n'.join(rows)+text[last:]
def literal(value):
    if isinstance(value,bool):return str(value).lower()
    if isinstance(value,int):return '('+str(value)+')' if value<0 else str(value)
    assert isinstance(value,list)
    return '['+', '.join(map(literal,value))+']'
def drivers(text,p,examples):
    first,last=signature(text,p['entry_point'])
    match=re.search(r'^method \w+\(([^()]*)\) returns \(([^()]*)\)',text[first:last])
    names=[v.split(':',1)[0].strip() for v in match[1].split(',') if v.strip()]
    outputs=[v for v in match[2].split(',') if v.strip()]
    for i,example in enumerate(examples):
        w=example['inputs']; assert set(w)==set(names)
        text+='\n// Independent concrete proof harness, not a source-translated entry.\nmethod ConcreteDomain'+str(i)+'()\n{\n'
        if p['id']=='P19':
            ptr=w['canonicalPointers'][w['lits'][w['oldWatch']]]
            idx=next(j for j,a in enumerate(w['activePointers']) if w['pointeeValue'][a]==w['pointeeValue'][ptr])
            active=literal(w['activePointers']); values=literal(w['pointeeValue'])
            text+='  assert 0 <= '+str(idx)+' < |'+active+'| && ('+values+')[('+active+')['+str(idx)+']] == ('+values+')['+str(ptr)+'];\n'
            text+='  assert exists j :: j == '+str(idx)+' && 0 <= j < |'+active+'| && ('+values+')[('+active+')[j]] == ('+values+')['+str(ptr)+'];\n'
            text+='  assert SemanticActive('+str(ptr)+','+active+','+values+');\n'
        text+='  var '+', '.join('out'+str(j) for j in range(len(outputs)))+' := '+p['entry_point']+'('+', '.join(literal(w[n]) for n in names)+');\n}\n'
    return text
def stable(text):
    code=re.sub(r'//[^\n]*','',text)
    return '\n'.join(r.strip() for r in code.splitlines() if r.strip() and not re.match(r'^\s*(assert|invariant|decreases)\b',r))+'\n'
def verify(pid,phase,text,canonical,mbqi=False):
    directory=models/'checks'; directory.mkdir(exist_ok=True)
    history_path=models/'checks.json'
    history=json.loads(history_path.read_text()) if history_path.exists() else []
    digest=hashlib.sha256(text.encode()).hexdigest()
    found=next((r for r in reversed(history) if r['id']==pid and r['phase']==phase and r['input_sha256']==digest and r.get('mbqi',False)==mbqi),None)
    if found:
        print(json.dumps(dict(id=pid,phase=phase,retained=True,exit_code=found['exit_code'])),flush=True)
        return found['exit_code']==0
    name=f'{len(history)+1:03}-{pid}-{phase}'
    path=directory/(name+'.dfy'); path.write_text(text,encoding='utf-8',newline='\n')
    command=[str(root/'nfv-tools'/'dafny'/'Dafny.exe'),'verify',str(path),'--solver-path',str(root/'nfv-tools'/'dafny'/'z3'/'bin'/'z3-4.12.1.exe'),'--verification-time-limit','30','--cores','2','--allow-warnings','--show-snippets','false']
    if mbqi:command+=['--solver-option','O:smt.mbqi=true']
    started=datetime.now(timezone.utc).isoformat(); start=time.monotonic()
    completed=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
    log=path.with_suffix('.log'); log.write_text(completed.stdout,encoding='utf-8',newline='\n')
    record=dict(id=pid,phase=phase,started_utc=started,seconds=round(time.monotonic()-start,3),exit_code=completed.returncode,canonical_sha256=canonical,input_sha256=digest,input=str(path.relative_to(models)),log=str(log.relative_to(models)),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),command=command,mbqi=mbqi)
    history.append(record); history_path.write_text(json.dumps(history,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:record[k] for k in ('id','phase','seconds','exit_code','input')}),flush=True)
    print(completed.stdout,flush=True)
    return completed.returncode==0

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--phase',choices=['validity','domain','admission','proof','refute'],required=True)
    parser.add_argument('--select',nargs='+',default=['P18','P19'])
    parser.add_argument('--label',default='')
    parser.add_argument('--mbqi',action='store_true')
    args=parser.parse_args()
    receipt=json.loads((root/'nfv3-model-freeze.json').read_text())
    for f in receipt['files']:assert hashlib.sha256((root/f['path']).read_bytes()).hexdigest()==f['sha256']
    props={p['id']:p for p in json.loads((models/'properties.json').read_text())}
    failed=False
    for pid in args.select:
        p=props[pid]; text=(models/(pid+'.dfy')).read_text()
        assert hashlib.sha256(text.encode()).hexdigest()==p['sha256']
        baseline=(models/'frozen'/(pid+'.dfy')).read_text()
        assert stable(text)==stable(baseline),'Only proof annotations may change after freeze'
        phase=args.phase
        if phase=='validity':checked=goals(text,p,[])
        elif phase=='domain':checked=drivers(goals(text,p,[]),p,p['witnesses'])
        elif phase=='admission':
            assert pid=='P18'
            cases=['('+' && '.join(n+' == '+literal(v) for n,v in w['inputs'].items())+')' for w in p['witnesses']]
            checked=drivers(goals(text,p,['constraints_ok'],['('+' || '.join(cases)+')']),p,p['witnesses'])
        elif phase=='refute':
            w=p['witnesses'][0]['inputs']
            negative='!('+' && '.join('('+g+')' for g in p['original_ensures'])+')'
            checked=drivers(goals(text,p,[negative],[n+' == '+literal(v) for n,v in w.items()]),p,[p['witnesses'][0]])
        else:checked=text
        failed|=not verify(pid,(args.label+'-' if args.label else '')+phase,checked,p['sha256'],args.mbqi)
    raise SystemExit(1 if failed else 0)
