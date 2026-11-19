"""Bounded NFV restriction, shorter-property and entry-only candidate checks."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

root=Path(__file__).parent
models=root/'nfv2-models'
props={p['id']:p for p in json.loads((models/'properties.json').read_text(encoding='utf-8'))}
history_path=models/'checks.json'
history=json.loads(history_path.read_text(encoding='utf-8'))
failed=False

def signature(text,entry):
    match=re.search(r'^method '+re.escape(entry)+r'\(',text,re.M)
    assert match
    return match.start(),text.index('\n{',match.start())

def goals(text,p,new_goals,pins=(),remove=()):
    first,last=signature(text,p['entry_point'])
    rows=[]
    for row in text[first:last].splitlines():
        if re.match(r'^\s*ensures ',row) or row.strip() in {'requires '+c for c in remove}:
            assert rows[-1].startswith('// synth:')
            rows.pop()
        else:
            rows.append(row)
    tag=rows.pop()
    assert tag.startswith('// synth:')
    for pin in pins:
        rows.extend(['// synth: independent concrete input pin','  requires '+pin])
    for goal in new_goals:
        rows.extend(['// synth: explicitly identified follow-up goal','  ensures '+goal])
    rows.append(tag)
    return text[:first]+'\n'.join(rows)+text[last:]

def literal(value):
    if isinstance(value,bool): return str(value).lower()
    if isinstance(value,int): return '('+str(value)+')' if value<0 else str(value)
    assert isinstance(value,list)
    return '['+', '.join(map(literal,value))+']'

def drivers(text,p,examples):
    first,last=signature(text,p['entry_point'])
    match=re.search(r'^method \w+\(([^()]*)\) returns \(([^()]*)\)',text[first:last])
    names=[v.split(':',1)[0].strip() for v in match[1].split(',') if v.strip()]
    outputs=[v for v in match[2].split(',') if v.strip()]
    for i,w in enumerate(examples):
        assert set(w)==set(names)
        text+='\nmethod NfvDomain'+str(i)+'()\n{\n  var '+', '.join('out'+str(j) for j in range(len(outputs)))+' := '+p['entry_point']+'('+', '.join(literal(w[n]) for n in names)+');\n}\n'
    return text

def verify(pid,phase,text):
    global failed
    digest=hashlib.sha256(text.encode()).hexdigest()
    previous=next((r for r in reversed(history) if r['id']==pid and r['phase']==phase and r['input_sha256']==digest),None)
    if previous:
        print(json.dumps(dict(id=pid,phase=phase,retained=True,exit_code=previous['exit_code'])),flush=True)
        failed|=previous['exit_code']!=0
        return previous['exit_code']==0
    name=f'{len(history)+1:03}-{pid}-{phase}'
    path=models/'checks'/(name+'.dfy')
    path.write_text(text,encoding='utf-8',newline='\n')
    command=[str(root/'nfv-tools'/'dafny'/'Dafny.exe'),'verify',str(path),'--solver-path',str(root/'nfv-tools'/'dafny'/'z3'/'bin'/'z3-4.12.1.exe'),'--verification-time-limit','30','--cores','2','--allow-warnings','--show-snippets','false']
    started=datetime.now(timezone.utc).isoformat()
    start=time.monotonic()
    result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
    log=path.with_suffix('.log')
    log.write_text(result.stdout,encoding='utf-8',newline='\n')
    record=dict(id=pid,phase=phase,started_utc=started,seconds=round(time.monotonic()-start,3),exit_code=result.returncode,canonical_sha256=props[pid]['sha256'],input_sha256=digest,input=str(path.relative_to(models)),log=str(log.relative_to(models)),command=command)
    history.append(record)
    history_path.write_text(json.dumps(history,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:record[k] for k in ('id','phase','seconds','exit_code','input')}),flush=True)
    if result.returncode:
        failed=True
        print(result.stdout,flush=True)
    return result.returncode==0

def refutation(text,p,property_goals,remove=()):
    witness=p['witnesses'][0]
    negated='!('+' && '.join('('+g+')' for g in property_goals)+')'
    pins=[n+' == '+literal(v) for n,v in witness.items()]
    return drivers(goals(text,p,[negated],pins,remove),p,[witness])

for pid in ('P11','P12'):
    p=props[pid]
    text=(models/(pid+'.dfy')).read_text(encoding='utf-8')
    assert hashlib.sha256(text.encode()).hexdigest()==p['sha256']
    assert any(r['id']==pid and r['phase'].endswith('refute') and r['exit_code']==0 for r in history),'Original complete refutation must precede follow-ups'
    optional=[a['clause'] for a in p['assumptions'] if a['optional']]
    if optional:
        validity=goals(text,p,[],remove=optional)
        if verify(pid,'optional-removed-validity',validity) and verify(pid,'optional-removed-domain',drivers(validity,p,p['witnesses'])):
            verify(pid,'optional-removed-refute',refutation(text,p,p['original_ensures'],optional))
    shorter=('!discharged || X + [a] + Y != [a] + X + [b] + Z' if pid=='P11' else 'case_number >= 2 * pattern_length + 2 || admitted')
    assert len(shorter)<len(' && '.join(p['original_ensures']))
    first,last=signature(text,p['entry_point'])
    match=re.search(r'^method \w+\(([^()]*)\) returns \(([^()]*)\)',text[first:last])
    args=match[1]+', '+match[2]
    tag=re.search(r'// src: [^\n]+\nmethod '+p['entry_point'],text).group(0).split('\n')[0]
    lemma=text[:first]+tag+'\nlemma NfvShorterImplication('+args+')\n'
    for clause in [a['clause'] for a in p['assumptions']]+p['original_ensures']:
        lemma+='// synth: original applicability or entire positive property as implication premise\n  requires '+clause+'\n'
    lemma+='// synth: proposed strictly shorter consequence with all inputs and outputs free\n  ensures '+shorter+'\n// synth: proof body\n{\n'
    if pid=='P11':
        lemma+='// synth: exhibit the offset-one infix under equality\n  assert X + [a] + Y == [a] + X + [b] + Z ==> 0 <= 1 <= |X + [a] + Y| && 1 + |X + [b] + Z| <= |X + [a] + Y| && (X + [a] + Y)[1..1+|X + [b] + Z|] == X + [b] + Z;\n// synth: instantiate the existential\n  assert X + [a] + Y == [a] + X + [b] + Z ==> WordContains(X + [a] + Y, X + [b] + Z);\n'
    lemma+='// synth: proof body\n}\n'
    if verify(pid,'shorter-implied-free-inputs-and-outputs',lemma):
        verify(pid,'shorter-refute',refutation(text,p,[shorter]))
    if pid=='P12':
        old='  var limit := Unsigned32(Unsigned32(2 * pattern_length) + 2);'
        assert text.count(old)==1
        candidate=text.replace(old,'  var limit := 2 * pattern_length + 2;')
        vfirst,vlast=signature(candidate,p['entry_point'])
        assert text[:last]==candidate[:vlast],'Candidate changed a helper or original contract'
        (models/'P12-candidate.dfy').write_text(candidate,encoding='utf-8',newline='\n')
        validity=goals(candidate,p,[])
        if verify(pid,'candidate-validity',validity) and verify(pid,'candidate-domain',drivers(validity,p,p['witnesses'])):
            verify(pid,'candidate-proof',candidate)
raise SystemExit(1 if failed else 0)
