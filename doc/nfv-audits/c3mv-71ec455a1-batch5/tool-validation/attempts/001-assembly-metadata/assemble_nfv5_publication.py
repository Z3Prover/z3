"""Export exact historical bytes into a new, source-checked publication candidate."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

SOURCE=Path(__file__).parent
REPO=Path(r'C:\z3seq')
OUT=REPO/'doc'/'nfv-audits'/'c3mv-71ec455a1-batch5'
PREVIOUS='f975e94d9830bcca332b309df422b364c6e99191'
PIN='71ec455a18702fe695d0c924a535ff9f385bd58d'


def git(*args):
    return subprocess.check_output(['git','--no-pager',*args],cwd=REPO,text=True).strip()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert not OUT.exists()
assert git('branch','--show-current')=='c3mv' and git('rev-parse','HEAD')==PREVIOUS
assert not git('status','--porcelain=v1','-uall')
assert git('rev-parse','HEAD:src')==git('rev-parse',PIN+':src')
assert sha(SOURCE/'nfv5-verification-handoff.json')=='b91f3044b61788a022dab4d72dd0c3346465bb2893dfd8c1ba268f883d0451db'
for f in json.loads((SOURCE/'nfv5-verification-handoff.json').read_text())['files']:
    assert sha(SOURCE/f['path'])==f['sha256']
sources=json.loads((SOURCE/'nfv5-models'/'sources.json').read_text())
assert sources['head']==PIN
excerpts=0
for f in sources['files']:
    assert git('rev-parse',PIN+':'+f['path'])==f['blob']
    raw=subprocess.check_output(['git','show',PIN+':'+f['path']],cwd=REPO)
    assert hashlib.sha256(raw).hexdigest()==f['sha256']
    lines=raw.decode('utf-8').splitlines()
    for row in f['excerpts']:
        assert lines[row['line']-1]==row['text']
        excerpts+=1
OUT.mkdir(parents=True)
shutil.copytree(SOURCE/'nfv5-models',OUT/'nfv5-models')
for path in SOURCE.glob('nfv5-*'):
    if path.is_file() and path.name!='nfv5-publication-readme.md':
        shutil.copyfile(path,OUT/path.name)
historical=['make_nfv5_models.py','check_nfv5_models.py','freeze_nfv5_models.py',
    'verify_nfv5.py','finish_nfv5_verification.py','seal_nfv5_verification.py','test_nfv5_watchdog.py','nfv-methodology.md']
for name in historical:
    shutil.copyfile(SOURCE/name,OUT/name)
fresh=['assemble_nfv5_publication.py','seal_nfv5_publication.py','validate_nfv5_publication.py','replay_nfv5_checks.py','test_nfv5_replay.py']
for name in fresh:
    (OUT/name).write_bytes((SOURCE/name).read_bytes().replace(b'\r\n',b'\n'))
(OUT/'README.md').write_bytes((SOURCE/'nfv5-publication-readme.md').read_bytes().replace(b'\r\n',b'\n'))
exceptions=sorted(p.relative_to(OUT).as_posix() for p in OUT.rglob('*') if p.is_file() and b'\r\n' in p.read_bytes())
(OUT/'.gitattributes').write_text('* text eol=lf\n'+''.join(p+' -text\n' for p in exceptions),encoding='utf-8',newline='\n')
(OUT/'export-notes.json').write_text(json.dumps(dict(policy='Historical bytes preserved exactly, including CRLF; only fresh publication tools/prose normalized before hashing.',
    raw_crlf_exceptions=exceptions,historical_tools=historical,portable_tools=fresh[2:],no_historical_bytes_changed=True),indent=2)+'\n',encoding='utf-8',newline='\n')
previous_names=['c3mv-71ec455a1','c3mv-71ec455a1-batch2','c3mv-71ec455a1-batch3','c3mv-71ec455a1-batch4']
preflight=dict(recorded_utc=datetime.now(timezone.utc).isoformat(),previous_publication=PREVIOUS,source=PIN,
    master=sources['master'],source_tree=git('rev-parse','HEAD:src'),stash=git('rev-parse','refs/stash'),branch='c3mv',
    previous_report_trees={n:git('rev-parse','HEAD:doc/nfv-audits/'+n) for n in previous_names},
    source_files_independently_raw_hash_checked=len(sources['files']),source_excerpt_lines_independently_checked=excerpts,
    observed_remote_master='bcad05a7bf7dd9b82bd7a665018e0480e737264b',
    master_note='Observed after verification. Not the baseline of this sealed batch; reconcile in next batch.')
(OUT/'publication-preflight.json').write_text(json.dumps(preflight,indent=2)+'\n',encoding='utf-8',newline='\n')
for path in OUT.rglob('*'):
    origin=SOURCE/path.relative_to(OUT)
    if path.is_file() and origin.is_file() and path.name not in fresh:
        assert sha(path)==sha(origin)
print(json.dumps(dict(status='assembled',files=sum(p.is_file() for p in OUT.rglob('*')),
    source_files=len(sources['files']),excerpt_lines=excerpts,crlf_exceptions=len(exceptions),bundle=str(OUT)),indent=2))
