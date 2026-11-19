"""Apply only the pre-frozen batch-five translation edits; keep old evidence."""
import ast
import copy
import difflib
import hashlib
import json
from pathlib import Path
import shutil

ROOT=Path(__file__).parent
OLD=Path(r'C:\z3seq\doc\nfv-audits\c3mv-71ec455a1-batch4')
OUT=ROOT/'nfv5-models'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


plan_path=ROOT/'nfv5-retranslation-plan.json'
assert sha(plan_path)=='c39fc8ff35ceffc30a16b50b4fbcea03f9a72b50dcc00a40e26bac179a975ae5'
assert sha(ROOT/'nfv5-retranslation-plan-freeze.json')=='7d5357ee217fe4e753187e4e8ffad4ae4ff794b3102975907287de0a3710110a'
plan=json.loads(plan_path.read_text())
assert not (OUT/'frozen').exists(),'Never regenerate sealed computation'
assert sha(OLD/'nfv4-model-freeze.json')==plan['baseline_model_seal_sha256']
assert sha(OLD/'nfv4-selection.json')==plan['baseline_selection_sha256']
props=json.loads((OLD/'nfv4-models'/'frozen'/'properties.json').read_text())
OUT.mkdir(exist_ok=True)
baseline=OUT/'baseline'
baseline.mkdir(exist_ok=True)
shutil.copyfile(OLD/'nfv4-models'/'frozen'/'properties.json',baseline/'properties.json')
shutil.copyfile(OLD/'nfv4-models'/'frozen'/'sources.json',OUT/'sources.json')
shutil.copyfile(OLD/'nfv4-selection.json',ROOT/'nfv5-original-selection.json')
shutil.copyfile(OLD/'nfv4-model-freeze.json',ROOT/'nfv5-baseline-model-freeze.json')
metadata=[]
changes=[]
for p in props:
    old_path=OLD/'nfv4-models'/'frozen'/(p['id']+'.dfy')
    assert sha(old_path)==p['sha256']
    shutil.copyfile(old_path,baseline/old_path.name)
    before=old_path.read_text()
    after=before
    helpers=[]
    for edit in plan['edits']:
        if p['id'] in edit['ids']:
            assert after.count(edit['before'])==1
            after=after.replace(edit['before'],edit['after'])
            helpers.append(edit['helper'])
    target=OUT/old_path.name
    target.write_text(after,encoding='utf-8',newline='\n')
    revised=copy.deepcopy(p)
    revised['sha256']=sha(target)
    revised['translation_revision']=dict(batch=5,baseline_publication=plan['baseline_publication'],
        baseline_model_sha256=p['sha256'],plan_sha256=sha(plan_path),changed_helpers=helpers,
        interpretation='Explicit new translation computation, not an annotation-only repair of sealed batch4 or new source-property coverage. Constructor evaluated-index values retained; no native equivalence claimed.')
    for key in ['inputs','outputs','assumptions','original_ensures','environment','examples','frozen_intent','source_tags']:
        assert revised[key]==p[key]
    metadata.append(revised)
    diff=list(difflib.unified_diff(before.splitlines(),after.splitlines(),fromfile='batch4/'+old_path.name,tofile='batch5/'+old_path.name,lineterm='',n=1))
    changes.append(dict(id=p['id'],before_sha256=p['sha256'],after_sha256=sha(target),changed_helpers=helpers,unified_diff=diff))
assert sum(len(c['changed_helpers']) for c in changes)==5
(OUT/'properties.json').write_text(json.dumps(metadata,indent=2)+'\n',encoding='utf-8',newline='\n')
(ROOT/'nfv5-retranslation-diff.json').write_text(json.dumps(changes,indent=2)+'\n',encoding='utf-8',newline='\n')
checker=(OLD/'check_nfv4_models.py').read_text()
assert checker.count("'nfv4-models'")==1
checker=checker.replace("'nfv4-models'","'nfv5-models'").replace('batch-four','batch-five')
ast.parse(checker,filename='check_nfv5_models.py')
(ROOT/'check_nfv5_models.py').write_text(checker,encoding='utf-8',newline='\n')
print(json.dumps(dict(status='new revision authored',whole_properties=3,new_source_entries=0,
    changed_body_lines=5,examples=sum(len(p['examples']) for p in metadata),new_verifier_attempts=0,
    models=[dict(id=p['id'],sha256=p['sha256']) for p in metadata]),indent=2))
