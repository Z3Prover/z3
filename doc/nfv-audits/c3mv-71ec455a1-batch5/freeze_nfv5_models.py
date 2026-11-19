"""Seal the planned revision after exact-diff, contract and resolve validation."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil

ROOT=Path(__file__).parent
MODELS=ROOT/'nfv5-models'
FROZEN=MODELS/'frozen'
TARGET=ROOT/'nfv5-model-freeze.json'
assert not FROZEN.exists() and not TARGET.exists()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


plan_path=ROOT/'nfv5-retranslation-plan.json'
assert sha(plan_path)=='c39fc8ff35ceffc30a16b50b4fbcea03f9a72b50dcc00a40e26bac179a975ae5'
assert sha(ROOT/'nfv5-retranslation-plan-freeze.json')=='7d5357ee217fe4e753187e4e8ffad4ae4ff794b3102975907287de0a3710110a'
plan=json.loads(plan_path.read_text())
props=json.loads((MODELS/'properties.json').read_text())
old=json.loads((MODELS/'baseline'/'properties.json').read_text())
history=json.loads((MODELS/'draft-checks.json').read_text())
assert len(history)==7 and all(h['exit_code']==0 for h in history)
assert history[0]['phase']=='provenance'
for h in history:
    assert sha(MODELS/h['log'])==h['log_sha256']
    for inp in h['inputs']:
        assert sha(MODELS/inp['path'])==inp['sha256']
for inp in history[0]['inputs']:
    current=ROOT/'check_nfv5_models.py' if Path(inp['path']).name=='check_nfv5_models.py' else MODELS/Path(inp['path']).name
    assert sha(current)==inp['sha256']
fingerprints=[]
changed=0
for p,prior in zip(props,old):
    assert p['id']==prior['id']
    baseline=MODELS/'baseline'/(p['id']+'.dfy')
    assert sha(baseline)==prior['sha256']
    expected=baseline.read_text()
    for edit in plan['edits']:
        if p['id'] in edit['ids']:
            assert expected.count(edit['before'])==1
            expected=expected.replace(edit['before'],edit['after'])
            changed+=1
    path=MODELS/(p['id']+'.dfy')
    assert path.read_text()==expected and sha(path)==p['sha256']
    assert set(p)==set(prior)|{'translation_revision'}
    assert all(p[k]==prior[k] for k in prior if k!='sha256')
    entry='method '+p['entry_point']+'('
    assert path.read_text().split(entry,1)[1]==baseline.read_text().split(entry,1)[1]
    header=path.read_text().split(entry,1)[1].split('\n{',1)[0]
    assert re.findall(r'^\s*requires ([^\n]*)',header,re.M)==[a['clause'] for a in p['assumptions']]
    assert re.findall(r'^\s*ensures ([^\n]*)',header,re.M)==p['original_ensures']
    for phase,suffix in [('resolve','.dfy'),('domain-resolve','-domain.dfy')]:
        check=next(h for h in history if h['id']==p['id'] and h['phase']==phase)
        assert check['inputs'][0]['sha256']==sha(MODELS/(p['id']+suffix))
    code=re.sub(r'//[^\n]*','',path.read_text())
    stable='\n'.join(line.strip() for line in code.splitlines() if line.strip() and not re.match(r'^\s*(assert|invariant|decreases)\b',line))+'\n'
    fingerprints.append(dict(id=p['id'],raw_sha256=sha(path),domain_driver_sha256=sha(MODELS/(p['id']+'-domain.dfy')),
        computation_and_contract_sha256=hashlib.sha256(stable.encode()).hexdigest(),original_ensures=p['original_ensures'],
        requires=[a['clause'] for a in p['assumptions']],helper_contracts=[dict(name=e['name'],requires=e['requires'],ensures=e['ensures']) for e in p['environment']]))
assert changed==5 and sum(len(p['examples']) for p in props)==13
for name in ['make_nfv5_models.py','check_nfv5_models.py',Path(__file__).name]:
    ast.parse((ROOT/name).read_text(),filename=name)
FROZEN.mkdir()
files=[]
for path in [MODELS/'properties.json',MODELS/'sources.json']+[MODELS/(p['id']+suffix) for p in props for suffix in ['.dfy','-domain.dfy']]+[ROOT/n for n in ['make_nfv5_models.py','check_nfv5_models.py',Path(__file__).name]]:
    dest=FROZEN/path.name
    shutil.copyfile(path,dest)
    assert sha(dest)==sha(path)
    files.append(dict(path=str(dest.relative_to(ROOT)),sha256=sha(dest)))
record=dict(recorded_utc=datetime.now(timezone.utc).isoformat(),phase='Modeling complete; provenance/resolution only, no verification or proved domain admission.',
    kind='Same-intent translation revision, not new source-property coverage.',head=plan['source'],master=plan['master'],
    baseline_publication=plan['baseline_publication'],baseline_seal_sha256=sha(ROOT/'nfv5-baseline-model-freeze.json'),
    plan_sha256=sha(plan_path),plan_freeze_sha256=sha(ROOT/'nfv5-retranslation-plan-freeze.json'),selection_sha256=plan['baseline_selection_sha256'],
    files=files,baseline_files=[dict(path=str(p.relative_to(ROOT)),sha256=sha(p)) for p in sorted((MODELS/'baseline').iterdir())],
    properties=fingerprints,report_sha256=sha(ROOT/'nfv5-modeling.md'),draft_history_sha256=sha(MODELS/'draft-checks.json'),
    retranslation_diff_sha256=sha(ROOT/'nfv5-retranslation-diff.json'),draft_checks=7,draft_failures=0,changed_body_lines=5,new_source_entries=0,
    body_defined_helpers=62,concrete_examples=13,new_verifier_attempts=0,native_executions=0,
    policy='All raw frozen and baseline files immutable. All computation, helper/entry input contracts, original whole goals and examples remain frozen. Only sound disclosed assert/invariant/decreases annotations may change. Fingerprints are textual guards, not native correspondence or proof of annotation-only equivalence.',
    next_stage='nfv5-verify',schedule_id=2,stop_schedule=False)
TARGET.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='sealed',properties=[p['id'] for p in props],files=len(files),baseline_files=len(record['baseline_files']),
    draft_checks=7,draft_failures=0,new_verifier_attempts=0,new_source_entries=0,freeze_sha256=sha(TARGET),
    report_sha256=record['report_sha256'],draft_checks_sha256=record['draft_history_sha256']),indent=2))
