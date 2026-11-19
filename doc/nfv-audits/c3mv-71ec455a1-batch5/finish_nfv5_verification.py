"""Finalize only completed, byte-validated whole-property/gate evidence."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).parent
MODELS=ROOT/'nfv5-models'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path,data):
    assert not path.exists(),'Never overwrite a completed handoff'
    path.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')


def input_literal(value):
    if type(value) is bool:
        return 'true' if value else 'false'
    if type(value) is int:
        return str(value) if value>=0 else '('+str(value)+')'
    return '['+','.join(input_literal(v) for v in value)+']'


if __name__=='__main__':
    seal=json.loads((ROOT/'nfv5-model-freeze.json').read_text())
    for item in seal['files']+seal['baseline_files']:
        assert sha(ROOT/item['path'])==item['sha256']
    assert sha(MODELS/'draft-checks.json')==seal['draft_history_sha256']
    props=json.loads((MODELS/'frozen'/'properties.json').read_text())
    history=json.loads((MODELS/'checks.json').read_text())
    assert [h['sequence'] for h in history]==list(range(1,len(history)+1))
    intervention_path=ROOT/'nfv5-attempt13-resource-intervention.json'
    intervention=json.loads(intervention_path.read_text())
    interrupted=next(h for h in history if h['sequence']==intervention['attempt'])
    assert interrupted['id']=='P21' and interrupted['kind']=='domain'
    assert interrupted['input']==intervention['input']
    assert interrupted['exit_code']==intervention['recorded_exit_code']!=0
    assert interrupted['seconds']==intervention['recorded_seconds']
    external_interruptions={intervention['attempt']}
    assert len(list((MODELS/'checks').glob('*.dfy')))==len(history),'An attempt is still running or interrupted; do not finalize'
    assert len(list((MODELS/'checks').glob('*.log')))==len(history)
    outcomes=[]
    for p in props:
        baseline=(MODELS/'frozen'/(p['id']+'.dfy')).read_text()
        assert (MODELS/(p['id']+'.dfy')).read_text()==baseline,'This stage has not changed frozen model computation or annotations'
        start=baseline.index('method '+p['entry_point']+'(')
        opening=baseline.index('\n{',start)
        header=baseline[start:opening]
        assert re.findall(r'^\s*requires ([^\n]*)',header,re.M)==[a['clause'] for a in p['assumptions']]
        assert re.findall(r'^\s*ensures ([^\n]*)',header,re.M)==p['original_ensures']
        removed,n=re.subn(r'^// synth:[^\n]*\n[ \t]*ensures [^\n]*\n','',header,flags=re.M)
        assert n==3
        validity=baseline[:start]+removed+baseline[opening:]
        attempts=[h for h in history if h['id']==p['id']]
        for h in attempts:
            if h['kind']!='validity':
                assert any(prior['kind']=='validity' and prior['exit_code']==0 and prior['sequence']<h['sequence'] for prior in attempts)
            if h['kind']=='proof':
                assert any(prior['kind']=='domain' and prior['exit_code']==0 and prior['sequence']<h['sequence'] for prior in attempts)
            assert sha(MODELS/h['input'])==h['input_sha256'] and sha(MODELS/h['log'])==h['log_sha256']
            checked=(MODELS/h['input']).read_text()
            if h['kind']=='validity':
                assert checked==validity
            elif h['kind']=='domain':
                blocks=checked.split('\n// Independent concrete domain/caller, not a native execution.')
                prefix=blocks[0]
                assert prefix==validity
                assert len(blocks)-1==len(p['examples'])
                for index,(example,block) in enumerate(zip(p['examples'],blocks[1:]),1):
                    assert block.startswith('\nmethod ConcreteDomain'+str(index)+'()\n{\n')
                    for name,value in example['inputs'].items():
                        pin='var '+name+': '+p['inputs'][name]+' := '+input_literal(value)+';'
                        assert block.count(pin)==1
                    calls=re.findall(r'\b'+re.escape(p['entry_point'])+r'\(([^()]*)\);',block)
                    assert calls==[','.join(p['inputs'])]
                    assert not re.search(r'\b(assume|axiom)\b',re.sub(r'//[^\n]*','',block))
            elif h['kind']=='proof':
                assert checked==baseline,'Positive verdict must check the complete original file'
            else:
                raise AssertionError('Refutation/repair acceptance needs its independent full-goal/pin/caller validator before finalization')
            cmd=h['command']
            assert cmd[cmd.index('--solver-path')+1].endswith('z3-4.12.1.exe')
            assert cmd[cmd.index('--verification-time-limit')+1]=='30' and cmd[cmd.index('--cores')+1]=='2'
            assert ('--isolate-assertions' in cmd)==h.get('isolate_assertions',False)
            assert not any(c.startswith('--filter') or c=='--dont-verify-dependencies' for c in cmd)
        assert any(h['kind']=='validity' and h['exit_code']==0 for h in attempts)
        domains=[h for h in attempts if h['kind']=='domain' and h['exit_code']==0]
        positives=[h for h in attempts if h['kind']=='proof']
        assert not positives or domains,'No positive before independent domains'
        assert not domains or positives,'Admitted domains require a whole-positive attempt before finalization'
        passed=[h for h in positives if h['exit_code']==0]
        if passed:
            outcome='verified'
            reason='Complete frozen original verified after property-free validity and independent domains.'
        elif not domains:
            outcome='resources_exhausted' if any(h['sequence'] in external_interruptions or h.get('wall_timed_out',False) or 'timed out' in (MODELS/h['log']).read_text().lower() for h in attempts) else 'type_check_or_audit_failure'
            reason='Model validity passed, but original concrete domains not admitted; whole positive/refutation blocked.'
        else:
            outcome='resources_exhausted' if any(h.get('wall_timed_out',False) or 'timed out' in (MODELS/h['log']).read_text().lower() for h in positives) else 'type_check_or_audit_failure'
            reason='Independent domains passed; complete original positive remains an unresolved proof, NOT a refutation or type-invalid model.'
        outcomes.append(dict(id=p['id'],entry=p['entry_point'],nfv_outcome=outcome,reason=reason,
            domain_admitted=bool(domains),admitted_examples=len(p['examples']) if domains else 0,
            whole_positive_attempts=[h['sequence'] for h in positives],attempts=[h['sequence'] for h in attempts],
            accepted_whole_proof=passed[-1]['sequence'] if passed else None,native_finding=False))
    for name in ['verify_nfv5.py','finish_nfv5_verification.py']:
        ast.parse((ROOT/name).read_text(),filename=name)
    summary=dict(whole_properties=3,new_source_entries=0,verified=sum(o['nfv_outcome']=='verified' for o in outcomes),
        refuted=0,resources_exhausted=sum(o['nfv_outcome']=='resources_exhausted' for o in outcomes),
        type_check_or_audit_failure=sum(o['nfv_outcome']=='type_check_or_audit_failure' for o in outcomes),
        verifier_attempts=len(history),successful_attempts=sum(h['exit_code']==0 for h in history),
        failed_attempts=sum(h['exit_code']!=0 for h in history),timeout_attempts=sum(h['sequence'] in external_interruptions or h.get('wall_timed_out',False) or 'timed out' in (MODELS/h['log']).read_text().lower() for h in history),
        externally_interrupted_attempts=sorted(external_interruptions),
        property_free_models_valid=3,admitted_examples=sum(o['admitted_examples'] for o in outcomes),
        construction_checks=7,construction_failures=0,native_executions=0)
    save(ROOT/'nfv5-results.json',dict(batch=5,recorded_utc=datetime.now(timezone.utc).isoformat(),source=seal['head'],master=seal['master'],
        kind='Same-intent retranslation; no new source-property coverage.',freeze_sha256=sha(ROOT/'nfv5-model-freeze.json'),
        checks_sha256=sha(MODELS/'checks.json'),resource_intervention_sha256=sha(intervention_path),summary=summary,outcomes=outcomes))
    print(json.dumps(dict(status='complete evidence validated',summary=summary,outcomes=outcomes,
        results_sha256=sha(ROOT/'nfv5-results.json'),checks_sha256=sha(MODELS/'checks.json')),indent=2))
