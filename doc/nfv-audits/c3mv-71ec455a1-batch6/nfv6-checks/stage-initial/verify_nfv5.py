"""Append-only, bounded verification of sealed batch-five mathematical models."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT=Path(__file__).parent
MODELS=ROOT/'nfv5-models'


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


def decoded(widths,flat):
    result=[]
    offset=0
    for width in widths:
        assert 0<=width<=len(flat)-offset
        result.append(flat[offset:offset+width])
        offset+=width
    assert offset==len(flat)
    return result


def partition_hints(wn,fn,values):
    widths,flat=values[wn],values[fn]
    rows=decoded(widths,flat)
    lines=[]
    for i in range(len(widths),-1,-1):
        offset=sum(widths[:i])
        lines.append('  assert Rows('+literal(widths[i:])+','+literal(flat[offset:])+') == '+literal(rows[i:])+';')
        lines.append('  assert Flat('+literal(rows[i:])+') == '+literal(flat[offset:])+';')
    lines.append('  assert Widths('+literal(rows)+') == '+literal(widths)+';')
    lines.append('  assert Partition('+wn+','+fn+');')
    return '\n'.join(lines)+'\n'


def concrete_hints(p,example):
    w=example['inputs']
    text='\n// Checked concrete proof annotations only; no new entry/helper contracts.\n'
    if p['id']=='P20':
        for wn,fn in [('syntaxWidths','syntaxItems'),('widths','items')]:
            text+=partition_hints(wn,fn,w)
        assert w['syntaxPower']==[False,True,True] and w['syntaxWidths']==[0,1,1] and w['syntaxItems']==[0,0]
        graph='seq(|syntaxPower|,i=>i),Rows(syntaxWidths,syntaxItems),syntaxPower'
        edge=lambda a,b:'Edge('+graph+','+a+','+b+')'
        text+='  assert forall a,b :: '+edge('a','b')+' ==> (a==1 || a==2) && b==0;\n'
        text+='  assert CurrentBaseAcyclic('+graph+') by {\n'
        text+='    forall cycle: seq<int> | |cycle|>1 && cycle[0]==cycle[|cycle|-1] && (forall j :: 0<=j<|cycle|-1 ==> '+edge('cycle[j]','cycle[j+1]')+')\n'
        text+='      ensures false\n    {\n'
        text+='      assert '+edge('cycle[0]','cycle[1]')+';\n'
        text+='      assert (cycle[0]==1 || cycle[0]==2) && cycle[1]==0;\n'
        text+='      if |cycle|==2 { assert cycle[0]==0; }\n'
        text+='      else { assert '+edge('cycle[1]','cycle[2]')+'; assert cycle[1]==1 || cycle[1]==2; }\n'
        text+='    }\n  }\n'
    elif p['id']=='P21':
        for wn,fn in [('facetWidths','facetValues'),('factDepWidths','factDepItems'),('wordWidths','wordChars'),('langWidths','langWords'),('coreWidths','coreIds'),('bucketWidths','bucketItems')]:
            text+=partition_hints(wn,fn,w)
        fc,fs,fw=w['facetContrib'],w['facetSatisfied'],w['facetWidths']
        eligible=True
        for i in range(len(fc),-1,-1):
            if i<len(fc):
                eligible=(fc[i] or fs[i]) and eligible
            text+='  assert Eligible(facetContrib,facetSatisfied,'+str(i)+') == '+literal(eligible)+';\n'
            positions=[j for f in range(i,len(fc)) if fc[f] for j in range(sum(fw[:f]),sum(fw[:f+1]))]
            text+='  assert Collect(facetContrib,facetWidths,'+str(i)+','+str(sum(fw[:i]))+') == '+literal(positions)+';\n'
        words=decoded(w['wordWidths'],w['wordChars'])
        langs=decoded(w['langWidths'],w['langWords'])
        for ids in langs:
            for word in words:
                accepted=any(words[i]==word for i in ids)
                text+='  assert AcceptWord('+literal(ids)+','+literal(words)+','+literal(word)+') == '+literal(accepted)+';\n'
    return text


def drivers(text,p,examples,hints=False):
    names=list(p['inputs'])
    for index,example in enumerate(examples,1):
        assert set(example['inputs'])==set(names)
        text+='\n// Independent concrete domain/caller, not a native execution.\nmethod ConcreteDomain'+str(index)+'()\n{\n'
        for name in names:
            text+='  var '+name+': '+p['inputs'][name]+' := '+literal(example['inputs'][name])+';\n'
        if hints:
            text+=concrete_hints(p,example)
        for clause in p['assumptions']:
            text+='  assert '+clause['clause']+';\n'
        outputs=','.join('out'+str(i) for i in range(len(p['outputs'])))
        text+='  var '+outputs+' := '+p['entry_point']+'('+','.join(names)+');\n}\n'
    return text


def run_bounded(command,stream,wall_seconds):
    with subprocess.Popen(command,stdout=stream,stderr=subprocess.STDOUT) as process:
        try:
            return process.wait(timeout=wall_seconds),False,None
        except subprocess.TimeoutExpired:
            cleanup=(
                'function Stop-OwnedTree([int]$owned) { '
                'Get-CimInstance Win32_Process -Filter "ParentProcessId = $owned" | '
                'ForEach-Object { Stop-OwnedTree $_.ProcessId }; '
                'Stop-Process -Id $owned -Force -ErrorAction SilentlyContinue }; '
                'Stop-OwnedTree '+str(process.pid))
            subprocess.run(['powershell','-NoProfile','-NonInteractive','-Command',cleanup],
                check=True,stdout=subprocess.DEVNULL,stderr=subprocess.STDOUT,timeout=60)
            actual=process.wait(timeout=60)
            stream.write(('\n[audit harness] Wall-clock resource limit reached after '
                +str(wall_seconds)+' seconds; only this attempt process tree was stopped.\n').encode())
            stream.flush()
            return 124,True,actual


def verify(pid,kind,label,text,p,mbqi,isolate=False,wall_seconds=600):
    checks=MODELS/'checks'
    checks.mkdir(exist_ok=True)
    history_path=MODELS/'checks.json'
    history=json.loads(history_path.read_text()) if history_path.exists() else []
    digest=hashlib.sha256(text.encode()).hexdigest()
    phase=(label+'-' if label else '')+kind
    old=next((h for h in reversed(history) if h['id']==pid and h['phase']==phase and h['input_sha256']==digest and h['mbqi']==mbqi and h.get('isolate_assertions',False)==isolate),None)
    if old:
        print(json.dumps(dict(id=pid,phase=phase,retained=True,exit_code=old['exit_code'])),flush=True)
        return old['exit_code']==0
    name=f'{len(history)+1:03}-{pid}-{phase}'
    path=checks/(name+'.dfy')
    assert not path.exists()
    path.write_text(text,encoding='utf-8',newline='\n')
    command=[str(ROOT/'nfv-tools'/'dafny'/'Dafny.exe'),'verify',str(path),'--solver-path',str(ROOT/'nfv-tools'/'dafny'/'z3'/'bin'/'z3-4.12.1.exe'),'--verification-time-limit','30','--cores','2','--allow-warnings','--show-snippets','false','--progress','Symbol']
    if mbqi:
        command+=['--solver-option','O:smt.mbqi=true']
    if isolate:
        command+=['--isolate-assertions']
    started=datetime.now(timezone.utc).isoformat()
    start=time.monotonic()
    log=path.with_suffix('.log')
    with log.open('wb') as stream:
        exit_code,wall_timed_out,interrupted_exit=run_bounded(command,stream,wall_seconds)
    output=log.read_text(encoding='utf-8',errors='replace')
    log.write_text(output,encoding='utf-8',newline='\n')
    record=dict(sequence=len(history)+1,id=pid,kind=kind,phase=phase,started_utc=started,seconds=round(time.monotonic()-start,3),exit_code=exit_code,canonical_sha256=p['sha256'],input_sha256=sha(path),input=str(path.relative_to(MODELS)),log=str(log.relative_to(MODELS)),log_sha256=sha(log),command=command,mbqi=mbqi,isolate_assertions=isolate,wall_time_limit_seconds=wall_seconds,wall_timed_out=wall_timed_out,interrupted_process_exit_code=interrupted_exit)
    history.append(record)
    history_path.write_text(json.dumps(history,indent=2)+'\n',encoding='utf-8',newline='\n')
    lines=output.splitlines()
    print(json.dumps({k:record[k] for k in ['sequence','id','phase','seconds','exit_code','input']}),flush=True)
    print('\n'.join(lines[-18:]),flush=True)
    return exit_code==0


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--phase',required=True,choices=['validity','domain','proof','refute'])
    parser.add_argument('--select',nargs='+',default=['P20','P21','P22'])
    parser.add_argument('--label',default='')
    parser.add_argument('--mbqi',action='store_true')
    parser.add_argument('--example',type=int,default=0)
    parser.add_argument('--hints',action='store_true')
    parser.add_argument('--isolate-assertions',action='store_true')
    parser.add_argument('--wall-time-limit',type=int,default=600)
    args=parser.parse_args()
    assert args.wall_time_limit>0
    seal=json.loads((ROOT/'nfv5-model-freeze.json').read_text())
    for f in seal['files']+seal['baseline_files']:
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
            checked=drivers(goals(text,p,[]),p,p['examples'],args.hints)
        elif args.phase=='refute':
            assert any(h['id']==pid and h['kind']=='proof' for h in history),'Check original complete positive goal before refutation'
            example=p['examples'][args.example]
            pins=[name+' == '+literal(example['inputs'][name]) for name in p['inputs']]
            negative='!('+' && '.join('('+g+')' for g in p['original_ensures'])+')'
            checked=drivers(goals(text,p,[negative],pins),p,[example],args.hints)
        else:
            checked=text
        failed|=not verify(pid,args.phase,args.label,checked,p,args.mbqi,args.isolate_assertions,args.wall_time_limit)
    raise SystemExit(1 if failed else 0)
