"""Validate complete batch-2 evidence and write an explicit result ledger."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

root=Path(__file__).parent
models=root/'nfv2-models'
digest=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
props=json.loads((models/'properties.json').read_text(encoding='utf-8'))
frozen=json.loads((root/'nfv2-model-freeze.json').read_text(encoding='utf-8'))
assert digest(root/'nfv2-selection.json')==frozen['selection_sha256']
for name,value in frozen['files'].items():
    assert digest(models/'frozen'/name)==value
history=json.loads((models/'checks.json').read_text(encoding='utf-8'))
assert len(history)==42
names=set()
for record in history:
    path=models/record['input']
    assert path.is_file() and digest(path)==record['input_sha256'],record['input']
    assert record['input'] not in names
    names.add(record['input'])
    log=(models/record['log']).read_text(encoding='utf-8')
    assert log.strip()
    command=record['command']
    assert command[command.index('--solver-path')+1]==str(root/'nfv-tools'/'dafny'/'z3'/'bin'/'z3-4.12.1.exe')
    assert command[command.index('--cores')+1]=='2'
    assert command[command.index('--verification-time-limit')+1]=='30'
    if record['exit_code']==0:
        assert re.search(r'Dafny program verifier finished with \d+ verified, 0 errors',log),record['input']
        assert 'time out' not in log and 'timed out' not in log
    assert not re.search(r'\b(assume|axiom)\b|\{\:|decreases\s+\*','\n'.join(l for l in path.read_text(encoding='utf-8').splitlines() if not l.strip().startswith('//'))),record['input']

def get(pid,phase):
    rows=[r for r in history if r['id']==pid and r['phase']==phase]
    assert len(rows)==1,(pid,phase)
    return rows[0]

def require(pid,phase,success=True):
    record=get(pid,phase)
    assert (record['exit_code']==0)==success,(pid,phase)
    return record['input']

outcomes=[]
for p in props:
    pid=p['id']
    assert digest(models/(pid+'.dfy'))==p['sha256']
    text=(models/(pid+'.dfy')).read_text(encoding='utf-8')
    assert re.findall(r'^\s*ensures (.+)$',text[text.index('method '+p['entry_point']):text.index('\n{',text.index('method '+p['entry_point']))],re.M)==p['original_ensures']
    records=[r for r in history if r['id']==pid]
    valid=[r for r in records if r['phase'].endswith('validity') and not r['phase'].startswith(('optional','candidate')) and r['exit_code']==0]
    domains=[r for r in records if r['phase'].endswith('domain') and not r['phase'].startswith(('optional','candidate')) and r['exit_code']==0]
    assert valid and domains
    assert valid[-1]['canonical_sha256']==p['sha256'] and domains[-1]['canonical_sha256']==p['sha256']
    original=get(pid,'proof')
    assert history.index(valid[0])<history.index(original) and history.index(domains[0])<history.index(original)
    if pid in ('P11','P12'):
        assert original['exit_code']!=0
        refute=get(pid,'annotation-refute' if pid=='P11' else 'refute')
        assert refute['exit_code']==0 and refute['canonical_sha256']==p['sha256']
        checked=(models/refute['input']).read_text(encoding='utf-8')
        negated='!('+' && '.join('('+g+')' for g in p['original_ensures'])+')'
        entry_start=checked.index('method '+p['entry_point'])
        entry_body=checked.index('\n{',entry_start)
        assert re.findall(r'^\s*ensures (.+)$',checked[entry_start:entry_body],re.M)==[negated]
        original_start=text.index('method '+p['entry_point'])
        original_body=text.index('\n{',original_start)
        assert checked[:entry_start]==text[:original_start]
        assert checked[entry_body:checked.index('\nmethod NfvDomain0()')].strip()==text[original_body:].strip()
        witness=p['witnesses'][0]
        def literal(v):
            if isinstance(v,bool):return str(v).lower()
            if isinstance(v,int):return '('+str(v)+')' if v<0 else str(v)
            return '['+', '.join(map(literal,v))+']'
        for name,value in witness.items():
            assert '  requires '+name+' == '+literal(value) in checked
        assert 'method NfvDomain0()' in checked
        require(pid,'shorter-implied-free-inputs-and-outputs')
        require(pid,'shorter-refute')
        implication=(models/get(pid,'shorter-implied-free-inputs-and-outputs')['input']).read_text(encoding='utf-8')
        short_start=implication.index('lemma NfvShorterImplication(')
        short_body=implication.index('\n{',short_start)
        header=implication[short_start:short_body]
        canonical_formals=re.search(r'^method \w+\(([^()]*)\) returns \(([^()]*)\)',text[original_start:original_body])
        free_formals=re.search(r'^lemma NfvShorterImplication\(([^()]*)\)',header)
        assert free_formals[1]==canonical_formals[1]+', '+canonical_formals[2]
        assert re.findall(r'^\s*requires (.+)$',header,re.M)==[a['clause'] for a in p['assumptions']]+p['original_ensures']
        shorter=re.findall(r'^\s*ensures (.+)$',header,re.M)
        assert len(shorter)==1 and len(shorter[0])<len(' && '.join(p['original_ensures']))
        result='refuted_translated_model'
        primary=refute['input']
    elif pid=='P13':
        assert original['exit_code']!=0
        result='unresolved_proof_obligations'
        primary=original['input']
    else:
        assert original['exit_code']==0 and original['canonical_sha256']==p['sha256']
        result='verified_translated_model'
        primary=original['input']
    classification='audit_failure' if pid=='P13' else ('refuted' if pid in ('P11','P12') else 'verified')
    outcomes.append(dict(id=pid,result=result,nfv_outcome=classification,entry_point=p['entry_point'],canonical_sha256=p['sha256'],whole_positive_property=p['original_ensures'],validity=valid[-1]['input'],domain=domains[-1]['input'],original_positive_attempt=original['input'],primary_evidence=primary,witness=p['witnesses'][0] if pid in ('P11','P12') else None))

for phase in ('optional-removed-validity','optional-removed-domain','optional-removed-refute'):
    require('P11',phase)
for phase in ('candidate-validity','candidate-domain','candidate-proof'):
    require('P12',phase)
old=(models/'P12.dfy').read_text(encoding='utf-8')
new=(models/'P12-candidate.dfy').read_text(encoding='utf-8')
assert old.replace('  var limit := Unsigned32(Unsigned32(2 * pattern_length) + 2);','  var limit := 2 * pattern_length + 2;')==new
successful=sum(r['exit_code']==0 for r in history)
assert sum('timed out' in (models/r['log']).read_text(encoding='utf-8') for r in history)==1
for script in ('make_nfv2_models.py','check_nfv2_models.py','freeze_nfv2_models.py','refresh_nfv2_proof_metadata.py','nfv2_followups.py','validate_nfv2_verification.py'):
    compile((root/script).read_text(encoding='utf-8'),script,'exec')
command=[sys.executable,r'C:\z3seq\doc\nfv-audits\c3mv-71ec455a1\check_nfv_provenance.py','--models',str(models)]
result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
assert result.returncode==0,result.stdout
old_provenance=models/'modeling-provenance.json'
if not old_provenance.exists():
    old_provenance.write_bytes((models/'provenance.json').read_bytes())
(models/'provenance.json').write_text(result.stdout,encoding='utf-8',newline='\n')
ledger=dict(checked_utc=datetime.now(timezone.utc).isoformat(),audited_head=frozen['audited_head'],source_execution=False,
    scope='Manual local NFV-methodology audit; no proved C++ correspondence or native reachability/crash evidence',
    whole_properties=7,verified=4,refuted=2,unresolved=1,verifier_checks=len(history),successful_checks=successful,
    failed_checks=len(history)-successful,timeout_checks=1,modeling_draft_checks=16,
    source_tags=sum(p['source_tags'] for p in json.loads(result.stdout)['properties']),
    computation_and_contracts='Compare using refresh_nfv2_proof_metadata.py against exact frozen baseline; only sound proof annotations changed',
    properties=outcomes,
    candidate=dict(id='P12',scope='admission prelude only; mathematical/nonwrapping threshold in entry, unchanged helpers/input contracts/entire original postcondition',validity=get('P12','candidate-validity')['input'],domain=get('P12','candidate-domain')['input'],proof=get('P12','candidate-proof')['input']),
    deferred_queue_proof='Initial relational invariants were not established and were removed as proof annotations, never from the complete positive property. Validity and concrete domains pass. The original conflict/queue relation remains unproved; this is neither a source bug nor a model refutation.')
(root/'nfv2-results.json').write_text(json.dumps(ledger,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:ledger[k] for k in ('whole_properties','verified','refuted','unresolved','verifier_checks','successful_checks','failed_checks','timeout_checks','source_tags')},indent=2))
