"""Export explicit audit artifacts, preserving every checked byte."""
import hashlib
import json
from pathlib import Path

source=Path(__file__).parent
target=Path(r'C:\z3seq\doc\nfv-audits\c3mv-71ec455a1-batch3')
artifacts=('nfv3-p12-source-trace.md','nfv3-p12-source-inventory.json','nfv3-coverage.md','nfv3-coverage-ledger.json','nfv3-coverage-source-inventory.json','nfv3-selection.json','nfv3-selection-freeze.json','nfv3-selection.md','nfv3-model-freeze.json','nfv3-modeling.md','nfv3-results.json','nfv3-followups.json','nfv3-verification.md','nfv-methodology.md')
scripts=('capture_nfv3_p12.py','capture_nfv3_coverage.py','select_nfv3.py','make_nfv3_models.py','check_nfv3_models.py','check_nfv3_provenance.py','freeze_nfv3_models.py','refresh_nfv3_annotations.py','verify_nfv3.py','nfv3_followups.py','validate_nfv3_verification.py','export_nfv3_audit.py')
normalizations=[]
def copy(original,destination,exact=False):
    assert original.is_file() and not original.is_symlink()
    assert destination.resolve().is_relative_to(target.resolve())
    raw=original.read_bytes()
    published=raw if exact else raw.replace(b'\r\n',b'\n')
    destination.parent.mkdir(exist_ok=True,parents=True)
    assert not destination.exists() or destination.read_bytes()==published,destination
    destination.write_bytes(published)
    if raw!=published:normalizations.append(dict(path=str(destination.relative_to(target)),original_sha256=hashlib.sha256(raw).hexdigest(),published_sha256=hashlib.sha256(published).hexdigest(),change='CRLF to LF only; no checked input/log/JSON modified'))
for path in sorted((source/'nfv3-models').rglob('*')):
    if path.is_file():
        assert path.suffix in ('.dfy','.json','.log','.py')
        copy(path,target/'nfv3-models'/path.relative_to(source/'nfv3-models'),True)
for name in artifacts:copy(source/name,target/name,not name.endswith('.md'))
for name in scripts:copy(source/name,target/'historical-tools'/name)
copy(source/'check_nfv3_provenance.py',target/'check_nfv3_provenance.py')
for name in ('.gitattributes','README.md','replay_checks.py','validate_publication.py'):
    p=target/name; raw=p.read_bytes(); p.write_bytes(raw.replace(b'\r\n',b'\n'))
history=json.loads((source/'nfv3-models'/'checks.json').read_text())
corrections=dict(source_tag=dict(path='nfv3-models/P19.dfy and P19-candidate.dfy',old_line=707,old_quote='}',corrected_line=706,corrected_quote='return false;',effect='Source-comment correction only; all historical verifier inputs and frozen baselines retained byte-exact. No changed computation, domain, helper contract or whole goal.'),current_model_sha256=hashlib.sha256((target/'nfv3-models'/'P19.dfy').read_bytes()).hexdigest(),current_candidate_sha256=hashlib.sha256((target/'nfv3-models'/'P19-candidate.dfy').read_bytes()).hexdigest(),verified_full_refutation_sha256=next(h['input_sha256'] for h in history if h['phase']=='visited-prefix-mbqi-refute'),verified_candidate_sha256=next(h['input_sha256'] for h in history if h['phase']=='candidate-proof'),pre_freeze_events='Coverage broad path-disjointness assertion and selection attached-comment span assertion were corrected before modeling; retained in the respective ledger/selection. Neither is a verifier check.',raw_crlf_exception='nfv3-models/drafts/001-provenance/check_nfv3_provenance.py')
(target/'publication-corrections.json').write_text(json.dumps(corrections,indent=2)+'\n',encoding='utf-8',newline='\n')
(target/'export-notes.json').write_text(json.dumps(dict(scope='All checked Dafny inputs, provenance inputs, logs and JSON copied byte-exact. Only nonchecked documents/authoring scripts normalized to LF; one historical checked Python input retained as raw CRLF with a single-path -text attribute.',normalizations=normalizations),indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='exported',files=sum(p.is_file() for p in target.rglob('*')),exact_model_evidence_files=sum(p.is_file() for p in (target/'nfv3-models').rglob('*')),normalized_documents_scripts=len(normalizations)),indent=2))
