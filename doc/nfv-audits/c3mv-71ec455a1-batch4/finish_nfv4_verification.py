"""Validate complete failed-gate evidence and save an honest stage handoff."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).parent
MODELS=ROOT/'nfv4-models'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path,data):
    assert not path.exists()
    path.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')


seal=json.loads((ROOT/'nfv4-model-freeze.json').read_text())
for f in seal['files']:
    assert sha(ROOT/f['path'])==f['sha256']
props=json.loads((MODELS/'frozen'/'properties.json').read_text())
history=json.loads((MODELS/'checks.json').read_text())
assert len(history)==3 and [h['id'] for h in history]==['P20','P21','P22']
outcomes=[]
for p,h in zip(props,history):
    assert h['kind']=='validity' and h['exit_code']==4 and not h['mbqi']
    assert sha(MODELS/h['input'])==h['input_sha256']
    assert sha(MODELS/h['log'])==h['log_sha256']
    baseline=(MODELS/'frozen'/(p['id']+'.dfy')).read_text()
    assert (MODELS/(p['id']+'.dfy')).read_bytes()==(MODELS/'frozen'/(p['id']+'.dfy')).read_bytes()
    first=baseline.index('method '+p['entry_point']+'(')
    last=baseline.index('\n{',first)
    header=baseline[first:last]
    assert re.findall(r'^\s*ensures ([^\n]*)',header,re.M)==p['original_ensures']
    assert re.findall(r'^\s*requires ([^\n]*)',header,re.M)==[a['clause'] for a in p['assumptions']]
    header,n=re.subn(r'^// synth:[^\n]*\n[ \t]*ensures [^\n]*\n','',header,flags=re.M)
    assert n==3
    expected=baseline[:first]+header+baseline[last:]
    assert (MODELS/h['input']).read_text()==expected,'Validity must remove ONLY original entry ensures'
    log=(MODELS/h['log']).read_text()
    assert 'Error: index out of range' in log and 'timed out' not in log.lower()
    command=h['command']
    assert command[command.index('--solver-path')+1]==str(ROOT/'nfv-tools'/'dafny'/'z3'/'bin'/'z3-4.12.1.exe')
    assert command[command.index('--cores')+1]=='2'
    assert command[command.index('--verification-time-limit')+1]=='30'
    outcomes.append(dict(id=p['id'],entry=p['entry_point'],outcome='type_check_or_audit_failure',
        reason='Property-free helper well-definedness failure: unguarded indexing inside sequence-constructor lambda.',
        validity_attempt=h['sequence'],domain='not run after failed validity',whole_positive='not run after failed validity',
        refutation='not run after failed validity',optional_restrictions=[],native_finding=False,
        exact_input=h['input'],input_sha256=h['input_sha256'],exact_log=h['log'],log_sha256=h['log_sha256']))
for name in ['verify_nfv4.py','finish_nfv4_verification.py']:
    ast.parse((ROOT/name).read_text(),filename=name)
assert sha(MODELS/'draft-checks.json')==seal['draft_history_sha256']
summary=dict(whole_properties=3,verified=0,refuted=0,type_check_or_audit_failure=3,resources_exhausted=0,
    verifier_attempts=3,successful_attempts=0,failed_attempts=3,domain_attempts=0,whole_positive_attempts=0,
    refutation_attempts=0,construction_checks=20,construction_failures=3,native_executions=0,
    subprocess_wall_seconds=round(sum(h['seconds'] for h in history),3))
results=dict(batch=4,source=seal['head'],master=seal['master'],freeze_sha256=sha(ROOT/'nfv4-model-freeze.json'),
    methodology='Manual local NFV-methodology audit, not hosted official admission or C++ correspondence.',
    summary=summary,properties=outcomes,checks_sha256=sha(MODELS/'checks.json'))
save(ROOT/'nfv4-results.json',results)
followups=dict(batch=4,reason='All three sealed translations failed the first validity gate.',
    next_stage='nfv4-publish',after_publication=dict(batch=5,work='New translation revision, not new source-property coverage.',
    retained_intents=['P20','P21','P22'],required=['Preserve batch4 sealed models, every failure and all old report evidence.',
        'Use a distinct workspace and explicitly freeze the same complete intents; do not disguise a retry as three newly audited entries.',
        'Correct constructor-lambda well-definedness without changing values on the constructor evaluation indices; disclose every textual change.',
        'Keep all original input signatures/contracts, complete positive goals and thirteen example values. Do not weaken graph or semantic-cache claims.',
        'Recheck property-free validity and independent domains before attempting entire positives; maintain all-input pinning/full-conjunction refutation protocol.']),
    remaining_source_questions=['Native gpower-producer reachability/current-base cycle consequences remain unproved.',
        'Temporary-length premise sufficiency, actual conflict/core production, insertion and later cache hit remain unproved.',
        'P13 and P18 retain earlier unresolved status.'],schedule_id=2,stop_schedule=False)
save(ROOT/'nfv4-followups.json',followups)
handoff=dict(stage='nfv4-verify',status='done',recorded_utc=datetime.now(timezone.utc).isoformat(),summary=summary,
    files={name:sha(ROOT/name) for name in ['nfv4-verification.md','nfv4-results.json','nfv4-followups.json','verify_nfv4.py','finish_nfv4_verification.py']},
    checks_sha256=sha(MODELS/'checks.json'),freeze_sha256=sha(ROOT/'nfv4-model-freeze.json'),
    next_stage='nfv4-publish',schedule_id=2,stop_schedule=False)
save(ROOT/'nfv4-verification-handoff.json',handoff)
print(json.dumps(dict(summary=summary,checks_sha256=handoff['checks_sha256'],files=handoff['files'],
    handoff_sha256=sha(ROOT/'nfv4-verification-handoff.json'),next_stage='nfv4-publish'),indent=2))
