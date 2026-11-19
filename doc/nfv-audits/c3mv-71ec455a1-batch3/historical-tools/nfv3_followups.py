"""Bounded full-refutation follow-ups, keeping frozen helpers/contracts."""
import hashlib
import json
from pathlib import Path
import re
from verify_nfv3 import drivers,goals,literal,signature,verify

root=Path(__file__).parent
models=root/'nfv3-models'
p=next(p for p in json.loads((models/'properties.json').read_text()) if p['id']=='P19')
text=(models/'P19.dfy').read_text()
assert hashlib.sha256(text.encode()).hexdigest()==p['sha256']
history=json.loads((models/'checks.json').read_text())
assert any(h['id']=='P19' and h['phase']=='visited-prefix-mbqi-refute' and h['exit_code']==0 for h in history)
optional=[a['clause'] for a in p['assumptions'] if a['optional']]
assert not optional,'This frozen property has no optional restrictions; do not silently omit a removal check'
shorter='!moved || HasAbsent(lits,canonicalPointers,pointeeValue,activePointers)'
assert len(shorter)<len(' && '.join(p['original_ensures']))
first,last=signature(text,p['entry_point'])
match=re.search(r'^method \w+\(([^()]*)\) returns \(([^()]*)\)',text[first:last])
free_args=match[1]+', '+match[2]
lemma=text[:first]+'lemma ShorterConsequence('+free_args+')\n'
for clause in [a['clause'] for a in p['assumptions']]+p['original_ensures']:
    lemma+='// synth: original applicability or complete original positive premise; all inputs/outputs free\n  requires '+clause+'\n'
lemma+='// synth: strictly shorter consequence, not a replacement original goal\n  ensures '+shorter+'\n{\n}\n'
implication=verify('P19','shorter-implied-free-inputs-and-outputs',lemma,p['sha256'],True)
w=p['witnesses'][0]['inputs']
short_refutation=False
if implication:
    short_refutation=verify('P19','shorter-refute',drivers(goals(text,p,['!('+shorter+')'],[n+' == '+literal(v) for n,v in w.items()]),p,[p['witnesses'][0]]),p['sha256'],True)

old='if !IdentityContains(activePointers,c,0) {'
new='if !SemanticActive(c,activePointers,pointeeValue) {'
old_invariant='invariant forall j :: 0 <= j < i && j != oldWatch ==> IdentityContains(activePointers,canonicalPointers[lits[j]],0)'
new_invariant='invariant forall j :: 0 <= j < i && j != oldWatch ==> SemanticActive(canonicalPointers[lits[j]],activePointers,pointeeValue)'
assert text.count(old)==text.count(old_invariant)==1
candidate=text.replace(old,new).replace(old_invariant,new_invariant)
vfirst,vlast=signature(candidate,p['entry_point'])
assert candidate[:vlast]==text[:last],'Candidate changed a helper, input or original goal'
candidate_path=models/'P19-candidate.dfy'
assert not candidate_path.exists() or candidate_path.read_text()==candidate
candidate_path.write_text(candidate,encoding='utf-8',newline='\n')
validity=verify('P19','candidate-validity',goals(candidate,p,[]),p['sha256'],True)
domain=False; proof=False
if validity:
    domain=verify('P19','candidate-domain',drivers(goals(candidate,p,[]),p,p['witnesses']),p['sha256'],True)
    if domain:proof=verify('P19','candidate-proof',candidate,p['sha256'],True)
result=dict(property='P19',optional_restrictions=[],optional_removal='not applicable: no optional requires in frozen property',shorter=shorter,shorter_implication=implication,shorter_refutation=short_refutation,implication_inputs_outputs='all free; no witness pins',candidate=dict(path=candidate_path.name,sha256=hashlib.sha256(candidate.encode()).hexdigest(),change='Entry guard uses the existing SemanticActive helper instead of IdentityContains; only the proof invariant is adapted to the new guard.',helpers_and_original_contracts_unchanged=True,validity=validity,domain=domain,whole_original_property=proof),limits='Entry-only mathematical model repair, not a native C++ patch, compiled test, full cache-core proof or production-correctness result.')
(root/'nfv3-followups.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
raise SystemExit(0 if implication and short_refutation and validity and domain and proof else 1)
