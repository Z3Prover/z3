"""Validate complete batch-3 records and produce outcome-only handoff metadata."""
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

root=Path(__file__).parent
models=root/'nfv3-models'
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
selection=root/'nfv3-selection.json'
assert digest(selection)=='0beb5b435b99a07ee85fbc6830028ee477f8b79bbd243c1f254887ef9b0da13e'
freeze_path=root/'nfv3-model-freeze.json'
assert digest(freeze_path)=='ca334079f007f6b501d24135033fe077cf62f73ae341c04dfb334ab938f2ee74'
for f in json.loads(freeze_path.read_text())['files']:assert digest(root/f['path'])==f['sha256']
props={p['id']:p for p in json.loads((models/'properties.json').read_text())}
history=json.loads((models/'checks.json').read_text())
def signature(text,entry):
    a=re.search(r'^method '+entry+r'\(',text,re.M).start()
    return text[a:text.index('\n{',a)]
def clauses(header,kind):return re.findall(r'^\s*'+kind+r' (.+)$',header,re.M)
def stable(text):
    code=re.sub(r'//[^\n]*','',text)
    return '\n'.join(r.strip() for r in code.splitlines() if r.strip() and not re.match(r'^\s*(assert|invariant|decreases)\b',r))+'\n'
def literal(value):
    if isinstance(value,bool):return str(value).lower()
    if isinstance(value,int):return '('+str(value)+')' if value<0 else str(value)
    return '['+', '.join(map(literal,value))+']'
for p in props.values():
    text=(models/(p['id']+'.dfy')).read_text()
    assert digest(models/(p['id']+'.dfy'))==p['sha256']
    assert stable(text)==stable((models/'frozen'/(p['id']+'.dfy')).read_text())
    assert clauses(signature(text,p['entry_point']),'ensures')==p['original_ensures']
for h in history:
    assert digest(models/h['input'])==h['input_sha256']
    assert digest(models/h['log'])==h['log_sha256']
    c=h['command']
    assert c[c.index('--solver-path')+1].endswith('z3-4.12.1.exe')
    assert c[c.index('--cores')+1]=='2' and c[c.index('--verification-time-limit')+1]=='30'
    assert '--allow-warnings' in c and c[c.index('--show-snippets')+1]=='false'
    if h['exit_code']==0:assert re.search(r'verified, 0 errors', (models/h['log']).read_text())
by_phase={(h['id'],h['phase']):h for h in history}
needed={'P18':['mbqi-validity','mbqi-domain','mbqi-admission'],'P19':['validity','explicit-exists-domain','visited-prefix-validity','visited-prefix-mbqi-refute','shorter-implied-free-inputs-and-outputs','shorter-refute','candidate-validity','candidate-domain','candidate-proof']}
for pid,phases in needed.items():
    for phase in phases:assert by_phase[pid,phase]['exit_code']==0
assert 'timed out after 30 seconds' in (models/by_phase['P18','mbqi-proof']['log']).read_text()
assert by_phase['P19','proof']['exit_code']!=0
p=props['P19']; w=p['witnesses'][0]['inputs']
ref=(models/by_phase['P19','visited-prefix-mbqi-refute']['input']).read_text()
header=signature(ref,p['entry_point'])
pins=[n+' == '+literal(v) for n,v in w.items()]
assert clauses(header,'requires')==[a['clause'] for a in p['assumptions']]+pins
negative='!('+' && '.join('('+g+')' for g in p['original_ensures'])+')'
assert clauses(header,'ensures')==[negative]
assert 'method ConcreteDomain0()' in ref
assert p['entry_point']+'('+', '.join(literal(v) for v in w.values())+')' in ref
short=(models/by_phase['P19','shorter-implied-free-inputs-and-outputs']['input']).read_text()
lemma=short[short.index('lemma ShorterConsequence('):].split('\n{',1)[0]
assert clauses(lemma,'requires')==[a['clause'] for a in p['assumptions']]+p['original_ensures']
assert not any(a['optional'] for a in p['assumptions'])
candidate=(models/'P19-candidate.dfy').read_text()
original=(models/'P19.dfy').read_text()
body=original.index('\n{',original.index('method '+p['entry_point']))
cbody=candidate.index('\n{',candidate.index('method '+p['entry_point']))
assert original[:body]==candidate[:cbody]
expected=original.replace('if !IdentityContains(activePointers,c,0) {','if !SemanticActive(c,activePointers,pointeeValue) {').replace('invariant forall j :: 0 <= j < i && j != oldWatch ==> IdentityContains(activePointers,canonicalPointers[lits[j]],0)','invariant forall j :: 0 <= j < i && j != oldWatch ==> SemanticActive(canonicalPointers[lits[j]],activePointers,pointeeValue)')
assert expected==candidate
for name in ('make_nfv3_models.py','check_nfv3_models.py','check_nfv3_provenance.py','freeze_nfv3_models.py','verify_nfv3.py','refresh_nfv3_annotations.py','nfv3_followups.py','validate_nfv3_verification.py'):ast.parse((root/name).read_text())
completed=subprocess.run([sys.executable,str(root/'check_nfv3_provenance.py'),'--models',str(models),'--inventory',str(root/'nfv3-coverage-source-inventory.json')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
(models/'provenance.json').write_text(completed.stdout,encoding='utf-8',newline='\n')
assert completed.returncode==0,completed.stdout
result=dict(
    batch=3,head='71ec455a18702fe695d0c924a535ff9f385bd58d',master='c2460a558fc6fee3cf15cfebd2d3f642ebf77770',
    selection_sha256=digest(selection),freeze_sha256=digest(freeze_path),checks=len(history),
    successful_checks=sum(h['exit_code']==0 for h in history),unsuccessful_checks=sum(h['exit_code']!=0 for h in history),
    timeout_checks=sum('timed out' in (models/h['log']).read_text() for h in history),
    proof_annotations='One P19 visited-prefix loop invariant and a current final-return source-tag correction 707 to 706 only; computation/helper contracts/entry domains/original goals unchanged. Historical checked inputs are byte-exact.',
    outcomes=[
        dict(id='P18',nfv_outcome='resources_exhausted',detail='Property-free validity, eight independent domains and all eight nonvacuous admissions pass with MBQI; whole original word-identity proof times out at 30 seconds. No counterexample or native bug claim.',validity=by_phase['P18','mbqi-validity']['input'],domain=by_phase['P18','mbqi-domain']['input'],nonvacuity=by_phase['P18','mbqi-admission']['input'],proof=by_phase['P18','mbqi-proof']['input']),
        dict(id='P19',nfv_outcome='refuted',classification='Local semantic-rewatch return/state model contract, missed-hit/performance only',whole_refutation=by_phase['P19','visited-prefix-mbqi-refute']['input'],witness=w,shorter_implication=by_phase['P19','shorter-implied-free-inputs-and-outputs']['input'],shorter_refutation=by_phase['P19','shorter-refute']['input'],optional_restrictions='none',entry_only_candidate=dict(validity=by_phase['P19','candidate-validity']['input'],domain=by_phase['P19','candidate-domain']['input'],full_original_property=by_phase['P19','candidate-proof']['input'],status='verified translated model repair only; no native patch'),native_solver_unsoundness=False,native_crash=False)],
    limitations=['Local methodology audit, not the hosted NFV driver or complete upstream extraction/span gates.','All outcomes concern translated projections, not C++/Dafny equivalence or native solver correctness.','P18 missing-trigger warning retained; MBQI explicitly enabled only where recorded.','Every failed proof, domain/validity failure and timeout is retained. Failed proof alone was not treated as refutation.','P13 whole-property proof, C11 global acyclicity and semantic cache-core sufficiency remain open.','No production code execution, source patch, giant allocation or native crash reproduction.'],
    history_sha256=digest(models/'checks.json'),metadata_sha256=digest(models/'properties.json'),provenance_sha256=digest(models/'provenance.json'))
(root/'nfv3-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='pass',checks=result['checks'],successful=result['successful_checks'],unsuccessful=result['unsuccessful_checks'],timeouts=result['timeout_checks'],outcomes=[dict(id=x['id'],outcome=x['nfv_outcome']) for x in result['outcomes']],results_sha256=digest(root/'nfv3-results.json')),indent=2))
