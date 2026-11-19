"""Validate portable tools separately, then seal every exported evidence byte."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

SOURCE=Path(__file__).parent
REPO=Path(r'C:\z3seq')
ROOT=REPO/'doc'/'nfv-audits'/'c3mv-71ec455a1-batch4'
assert not (ROOT/'manifest.json').exists()
OUT=ROOT/'tool-validation'
OUT.mkdir(exist_ok=True)
assert not (OUT/'results.json').exists()
DAFNY=SOURCE/'nfv-tools'/'dafny'/'Dafny.exe'
SOLVER=SOURCE/'nfv-tools'/'dafny'/'z3'/'bin'/'z3-4.12.1.exe'


def run(command,log):
    result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
    (OUT/log).write_text(result.stdout,encoding='utf-8',newline='\n')
    assert result.returncode==0,(log,result.returncode,result.stdout)
    return result


dv=run([str(DAFNY),'--version'],'dafny-version.log').stdout.strip()
zv=run([str(SOLVER),'--version'],'solver-version.log').stdout.strip()
assert dv.startswith('4.11.0') and zv.startswith('Z3 version 4.12.1 ')
unit=run([sys.executable,str(ROOT/'test_nfv4_replay.py'),'--bundle',str(ROOT)],'unit-tests.log')
external=SOURCE/'nfv4-publication-replay-002'
command=[sys.executable,str(ROOT/'replay_nfv4_checks.py'),'--bundle',str(ROOT),'--dafny',str(DAFNY),'--solver',str(SOLVER),'--output',str(external)]
replay=run(command,'replay-driver.log')
shutil.copytree(external,OUT/'replay')
record=dict(status='pass',recorded_utc=datetime.now(timezone.utc).isoformat(),live_verifier_invocations=3,
    audit_verifier_attempts=3,distinction='These three live replays and two mocked unit tests validate tools, not new audit properties or native source.',
    dafny_version=dv,solver_version=zv,unit_exit=unit.returncode,replay_exit=replay.returncode,replay_command=command,
    tests=['Earlier exit mismatch remains failure despite a later match.','Changed model hash rejected before verifier execution.','All three exact audit inputs replay their expected exit4 failures.'],
    failed_tool_launches=[dict(receipt='attempts/001-output-isolation/receipt.json',live_verifier_invocations=0,reason='Initial output path was inside the bundle; replay guard rejected it. Exact original tools/log retained; corrected output is external.')])
(OUT/'results.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8',newline='\n')
preflight=json.loads((ROOT/'publication-preflight.json').read_text())
git=lambda *args:subprocess.check_output(['git',*args],cwd=REPO,text=True).strip()
assert git('branch','--show-current')=='c3mv' and git('rev-parse','HEAD')==preflight['previous_publication']
assert not git('diff','--cached','--name-only')
assert git('rev-parse','HEAD:src')==preflight['source_tree']
assert git('rev-parse','refs/stash')==preflight['stash']
notes=json.loads((ROOT/'export-notes.json').read_text())
notes['raw_crlf_exceptions']=sorted(p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file() and b'\r\n' in p.read_bytes())
(ROOT/'.gitattributes').write_text('* text eol=lf\n'+''.join(p+' -text\n' for p in notes['raw_crlf_exceptions']),encoding='utf-8',newline='\n')
(ROOT/'export-notes.json').write_text(json.dumps(notes,indent=2)+'\n',encoding='utf-8',newline='\n')
files=[]
for path in sorted(ROOT.rglob('*')):
    if path.is_file():
        assert not path.is_symlink()
        raw=path.read_bytes()
        files.append(dict(path=path.relative_to(ROOT).as_posix(),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
manifest=dict(format='manual-nfv-audit-bundle-v1',head=preflight['source'],master='c2460a558fc6fee3cf15cfebd2d3f642ebf77770',
    merge_base='437536cd64a544a1c329fc57d83e56e294fdf47c',nfv_upstream='599726579274cfeb1c0915414b911371527a9870',
    previous_publication=preflight['previous_publication'],previous_report_trees=preflight['previous_report_trees'],
    source_tree=preflight['source_tree'],audit_verifier_attempts=3,live_tool_verifier_invocations=3,
    results_sha256=hashlib.sha256((ROOT/'nfv4-results.json').read_bytes()).hexdigest(),files=files)
(ROOT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='sealed',files=len(files)+1,manifest_sha256=hashlib.sha256((ROOT/'manifest.json').read_bytes()).hexdigest(),live_tool_verifier_invocations=3),indent=2))
