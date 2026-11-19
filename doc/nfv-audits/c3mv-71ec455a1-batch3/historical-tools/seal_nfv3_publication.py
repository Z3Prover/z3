"""Seal the new report after exact evidence and portable-tool validation."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

repo=Path(r'C:\z3seq')
source=Path(__file__).parent
root=repo/'doc'/'nfv-audits'/'c3mv-71ec455a1-batch3'
assert not (root/'manifest.json').exists()
for name in ('smoke_nfv3_tools.py','seal_nfv3_publication.py'):
    raw=(source/name).read_bytes().replace(b'\r\n',b'\n')
    (root/'historical-tools'/name).write_bytes(raw)
git=lambda *a:subprocess.check_output(['git',*a],cwd=repo,text=True).strip()
assert git('branch','--show-current')=='c3mv'
assert git('rev-parse','HEAD')=='146f70d7ddf5507fdf731af2511edf4c5f669fc5'
assert not git('diff','--cached','--name-only')
assert git('rev-parse','HEAD:src')==git('rev-parse','71ec455a18702fe695d0c924a535ff9f385bd58d:src')
files=[]
for path in sorted(root.rglob('*')):
    if path.is_file():
        assert not path.is_symlink()
        raw=path.read_bytes()
        relative=str(path.relative_to(root)).replace('\\','/')
        if relative!='nfv3-models/drafts/001-provenance/check_nfv3_provenance.py':assert b'\r\n' not in raw,relative
        files.append(dict(path=relative,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
manifest=dict(format='manual-nfv-audit-bundle-v1',head='71ec455a18702fe695d0c924a535ff9f385bd58d',master='c2460a558fc6fee3cf15cfebd2d3f642ebf77770',merge_base='437536cd64a544a1c329fc57d83e56e294fdf47c',nfv_upstream='599726579274cfeb1c0915414b911371527a9870',source_tree=git('rev-parse','HEAD:src'),previous_publication=git('rev-parse','HEAD'),previous_report_trees={n:git('rev-parse','HEAD:doc/nfv-audits/'+n) for n in ('c3mv-71ec455a1','c3mv-71ec455a1-batch2')},selection_sha256=hashlib.sha256((root/'nfv3-selection.json').read_bytes()).hexdigest(),results_sha256=hashlib.sha256((root/'nfv3-results.json').read_bytes()).hexdigest(),audit_verifier_attempts=18,tool_verifier_invocations=5,files=files)
(root/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='sealed',published_files=len(files)+1,manifest_sha256=hashlib.sha256((root/'manifest.json').read_bytes()).hexdigest(),source_tree=manifest['source_tree']),indent=2))
