"""Copy exact historical evidence into a NEW publication; never rewrite it."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

SOURCE=Path(__file__).parent
REPO=Path(r'C:\z3seq')
OUT=REPO/'doc'/'nfv-audits'/'c3mv-71ec455a1-batch4'
PREVIOUS='13cfdf0d3f046886dd16ae6aef2c9853679b4877'
PIN='71ec455a18702fe695d0c924a535ff9f385bd58d'


def git(*args):
    return subprocess.check_output(['git',*args],cwd=REPO,text=True).strip()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert not OUT.exists()
assert git('branch','--show-current')=='c3mv' and git('rev-parse','HEAD')==PREVIOUS
assert not git('status','--porcelain=v1')
assert git('rev-parse','HEAD:src')==git('rev-parse',PIN+':src')
inventories=['nfv4-subst-source-inventory.json','nfv4-subst-extra-source.json','nfv4-core-source-inventory.json','nfv4-selection-source-inventory.json','nfv4-models\\sources.json']
identities={}
excerpts={}
for name in inventories:
    data=json.loads((SOURCE/name).read_text())
    assert data['head']==PIN
    for f in data['files']:
        pair=(f['blob'],f['sha256'])
        assert f['path'] not in identities or identities[f['path']]==pair
        identities[f['path']]=pair
        for row in f.get('excerpts',[]):
            key=(f['path'],row['line'])
            assert key not in excerpts or excerpts[key]==row['text']
            excerpts[key]=row['text']
for path,(blob,digest) in identities.items():
    assert git('rev-parse',PIN+':'+path)==blob
    raw=subprocess.check_output(['git','show',PIN+':'+path],cwd=REPO)
    assert hashlib.sha256(raw).hexdigest()==digest
    lines=raw.decode('utf-8').splitlines()
    for (name,line),text in excerpts.items():
        if name==path:
            assert lines[line-1]==text,(path,line)
OUT.mkdir(parents=True)
shutil.copytree(SOURCE/'nfv4-models',OUT/'nfv4-models')
for path in SOURCE.glob('nfv4-*'):
    if path.is_file() and path.name!='nfv4-publication-readme.md':
        shutil.copyfile(path,OUT/path.name)
historical=['capture_nfv4_substitutions.py','finish_nfv4_substitutions.py','capture_nfv4_core.py','select_nfv4.py','make_nfv4_models.py','check_nfv4_models.py','freeze_nfv4_models.py','verify_nfv4.py','finish_nfv4_verification.py']
for name in historical:
    shutil.copyfile(SOURCE/name,OUT/name)
fresh=['assemble_nfv4_publication.py','validate_nfv4_publication.py','replay_nfv4_checks.py','test_nfv4_replay.py','seal_nfv4_publication.py']
for name in fresh:
    (OUT/name).write_bytes((SOURCE/name).read_bytes().replace(b'\r\n',b'\n'))
(OUT/'README.md').write_bytes((SOURCE/'nfv4-publication-readme.md').read_bytes().replace(b'\r\n',b'\n'))
exceptions=sorted(p.relative_to(OUT).as_posix() for p in OUT.rglob('*') if p.is_file() and b'\r\n' in p.read_bytes())
(OUT/'.gitattributes').write_text('* text eol=lf\n'+''.join(p+' -text\n' for p in exceptions),encoding='utf-8',newline='\n')
notes=dict(policy='Exact historical bytes, including CRLF, are preserved. Fresh publication prose/tools use LF. Attributes exempt every hashed CRLF-bearing historical file from conversion.',raw_crlf_exceptions=exceptions,historical_tools=historical,portable_tools=['validate_nfv4_publication.py','replay_nfv4_checks.py'],no_historical_bytes_changed=True)
(OUT/'export-notes.json').write_text(json.dumps(notes,indent=2)+'\n',encoding='utf-8',newline='\n')
preflight=dict(recorded_utc=datetime.now(timezone.utc).isoformat(),previous_publication=PREVIOUS,source=PIN,
    source_tree=git('rev-parse','HEAD:src'),stash=git('rev-parse','refs/stash'),branch='c3mv',
    previous_report_trees={n:git('rev-parse','HEAD:doc/nfv-audits/'+n) for n in ['c3mv-71ec455a1','c3mv-71ec455a1-batch2','c3mv-71ec455a1-batch3']},
    source_files_independently_raw_hash_checked=len(identities),source_excerpt_lines_independently_checked=len(excerpts),source_identity_check='All five current source inventories deduplicated; blob IDs, raw SHA-256 and exact numbered excerpts checked against pinned Git blobs; no source execution.',
    shell_preflight_note='Initial PowerShell directory listing had an invalid Filter array and exited1 before Git inspection. Corrected read-only preflight succeeded; not a verifier attempt.')
(OUT/'publication-preflight.json').write_text(json.dumps(preflight,indent=2)+'\n',encoding='utf-8',newline='\n')
for path in OUT.rglob('*'):
    if path.is_file() and (SOURCE/path.relative_to(OUT)).is_file() and path.name not in fresh:
        assert sha(path)==sha(SOURCE/path.relative_to(OUT))
print(json.dumps(dict(status='assembled',files=sum(p.is_file() for p in OUT.rglob('*')),source_files=len(identities),raw_crlf_exceptions=len(exceptions),bundle=str(OUT)),indent=2))
