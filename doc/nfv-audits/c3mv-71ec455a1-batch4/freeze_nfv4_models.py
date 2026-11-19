"""Seal resolved models, domain drivers, full contracts and exact draft history."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil

ROOT=Path(__file__).parent
MODELS=ROOT/'nfv4-models'
FROZEN=MODELS/'frozen'
TARGET=ROOT/'nfv4-model-freeze.json'
assert not FROZEN.exists() and not TARGET.exists()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert sha(ROOT/'nfv4-selection.json')=='7d7e9ff5bc259460e5dfc9b6892f7ccadc1fd8378fd10e970a585b07029bb4ce'
assert sha(ROOT/'nfv4-selection-freeze.json')=='fbcf7507cd3bf3f6c45cfd9dc6151f93dcba4c18cf5f6afba01d146a1c5ca178'
selection=json.loads((ROOT/'nfv4-selection.json').read_text())
selection_freeze=json.loads((ROOT/'nfv4-selection-freeze.json').read_text())
assert sha(ROOT/'nfv4-selection-source-inventory.json')==selection_freeze['selection_source_sha256']
assert sha(ROOT/'nfv4-selection.md')==selection_freeze['report_sha256']
for name,expected in selection_freeze['source_handoffs'].items():
    assert sha(ROOT/name)==expected
source_handoffs={
    'nfv4-subst-handoff.json':{'inventory_sha256':'nfv4-subst-source-inventory.json','extra_source_sha256':'nfv4-subst-extra-source.json','producer_ledger_sha256':'nfv4-subst-producer-ledger.json','report_sha256':'nfv4-subst-invariants.md'},
    'nfv4-core-handoff.json':{'source_inventory_sha256':'nfv4-core-source-inventory.json','provenance_ledger_sha256':'nfv4-core-provenance-ledger.json','report_sha256':'nfv4-core-provenance.md'}}
for name,fields in source_handoffs.items():
    receipt=json.loads((ROOT/name).read_text())
    for key,path in fields.items():
        assert sha(ROOT/path)==receipt[key]
props=json.loads((MODELS/'properties.json').read_text())
history=json.loads((MODELS/'draft-checks.json').read_text())
assert [p['id'] for p in props]==['P20','P21','P22']
assert history[-1]['phase']=='domain-resolve' and history[-1]['exit_code']==0
latest_provenance=next(h for h in reversed(history) if h['phase']=='provenance')
assert latest_provenance['exit_code']==0
for inp in latest_provenance['inputs']:
    current=ROOT/'check_nfv4_models.py' if Path(inp['path']).name=='check_nfv4_models.py' else MODELS/Path(inp['path']).name
    assert sha(current)==inp['sha256']
for h in history:
    assert sha(MODELS/h['log'])==h['log_sha256']
    for inp in h['inputs']:
        assert sha(MODELS/inp['path'])==inp['sha256']
assert sum(h['exit_code']!=0 for h in history)==3
fingerprints=[]
for p in props:
    selected=next(s for s in selection['properties'] if s['id']==p['id'])
    assert p['frozen_intent']==selected
    assert p['frozen_selection_sha256']==sha(ROOT/'nfv4-selection.json')
    assert p['examples']==selected['examples'] and p['inputs']==selected['inputs'] and p['outputs']==selected['outputs']
    path=MODELS/(p['id']+'.dfy')
    assert sha(path)==p['sha256']
    resolved=next(h for h in reversed(history) if h['id']==p['id'] and h['phase']=='resolve')
    domains=next(h for h in reversed(history) if h['id']==p['id'] and h['phase']=='domain-resolve')
    assert resolved['exit_code']==domains['exit_code']==0
    assert resolved['inputs'][0]['sha256']==sha(path)
    domain_path=MODELS/(p['id']+'-domain.dfy')
    assert domains['inputs'][0]['sha256']==sha(domain_path)
    assert len(re.findall(r'^method ConcreteDomain\d+\(',domain_path.read_text(),re.M))==len(p['examples'])
    assert all(not a['optional'] and a['origin']=='inferred' for a in p['assumptions'])
    assert len(p['original_ensures'])==3
    code=re.sub(r'//[^\n]*','',path.read_text())
    stable='\n'.join(line.strip() for line in code.splitlines() if line.strip() and not re.match(r'^\s*(assert|invariant|decreases)\b',line))+'\n'
    fingerprints.append(dict(id=p['id'],raw_sha256=sha(path),domain_driver_sha256=sha(domain_path),
        computation_and_contract_sha256=hashlib.sha256(stable.encode()).hexdigest(),
        original_ensures=p['original_ensures'],requires=[a['clause'] for a in p['assumptions']],
        helper_contracts=[dict(name=e['name'],requires=e['requires'],ensures=e['ensures']) for e in p['environment']]))
assert sum(len(p['examples']) for p in props)==13
FROZEN.mkdir()
files=[]
inputs=[MODELS/'properties.json',MODELS/'sources.json']+[MODELS/(p['id']+suffix) for p in props for suffix in ['.dfy','-domain.dfy']]+[ROOT/'make_nfv4_models.py',ROOT/'check_nfv4_models.py',Path(__file__)]
for path in inputs:
    dest=FROZEN/path.name
    shutil.copyfile(path,dest)
    assert sha(dest)==sha(path)
    files.append(dict(path=str(dest.relative_to(ROOT)),sha256=sha(dest)))
report_sha=sha(ROOT/'nfv4-modeling.md')
record=dict(recorded_utc=datetime.now(timezone.utc).isoformat(),phase='Modeling complete; local provenance and resolution only, no verification or proved domain admission yet.',
    head='71ec455a18702fe695d0c924a535ff9f385bd58d',master='c2460a558fc6fee3cf15cfebd2d3f642ebf77770',
    selection_sha256=sha(ROOT/'nfv4-selection.json'),selection_freeze_sha256=sha(ROOT/'nfv4-selection-freeze.json'),
    files=files,properties=fingerprints,report_sha256=report_sha,
    draft_history_sha256=sha(MODELS/'draft-checks.json'),draft_checks=len(history),draft_failures=3,
    provenance_checks=sum(h['phase']=='provenance' for h in history),resolve_checks=sum(h['phase'] in ['resolve','domain-resolve'] for h in history),
    body_defined_helpers=sum(len(p['environment']) for p in props),concrete_examples=13,new_verifier_attempts=0,native_executions=0,
    draft_failures_note='Three initial domain-resolve failures from untyped empty literals in substituted assertions; corrected only in the harness with typed concrete locals. Initial warning and all exact inputs/logs retained.',
    construction_notes=['Initial model computations and goals resolved without errors; final models were not formally verified in this stage.',
        'Per-helper source anchors were added to metadata without changing model bytes; only provenance was repeated for that edit.',
        'Before sealing, P20 original/current base-width bounds and P21 facet-count bound were made explicit as already selected unsigned representation conditions; only those two model/domain pairs were re-resolved. No positive goal or witness changed.',
        'Totalization outside well-formed domains, successful allocation, mathematical tuple/row encodings, finite-language and canonical ADT abstractions remain disclosed; no correspondence theorem or official admission claimed.',
        'Exact-transition conjuncts stay frozen even if they prevent an entry-only repair. Do not remove them to make a fix pass.'],
    policy='Keep raw frozen files immutable. Computation, every entry/helper contract, all named inputs, complete conjunctions and thirteen examples are sealed. Later model edits may only add sound disclosed proof annotations; fingerprint is an extra textual guard, not a proof of source correctness or annotation-only equivalence.',
    next_stage='nfv4-verify',schedule_id=2,stop_schedule=False)
TARGET.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='sealed',properties=[p['id'] for p in props],files=len(files),draft_checks=len(history),
    draft_failures=3,helpers=record['body_defined_helpers'],examples=13,new_verifier_attempts=0,
    freeze_sha256=sha(TARGET),report_sha256=report_sha),indent=2))
