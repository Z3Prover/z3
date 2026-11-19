"""Retain exact draft inputs and full provenance/resolve diagnostics."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

root=Path(__file__).parent
models=root/'nfv2-models'
directory=models/'drafts'
directory.mkdir(exist_ok=True)
history_path=models/'draft-checks.json'
history=json.loads(history_path.read_text(encoding='utf-8')) if history_path.exists() else []
props=json.loads((models/'properties.json').read_text(encoding='utf-8'))
failed=False

def run(ident,phase,command,artifact):
    global failed
    start=time.monotonic()
    completed=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
    log=directory/(artifact+'.log')
    log.write_text(completed.stdout,encoding='utf-8',newline='\n')
    record=dict(id=ident,phase=phase,recorded_utc=datetime.now(timezone.utc).isoformat(),
                seconds=round(time.monotonic()-start,3),exit_code=completed.returncode,command=command,
                input=artifact,log=str(log.relative_to(models)))
    history.append(record)
    history_path.write_text(json.dumps(history,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:record[k] for k in ('id','phase','seconds','exit_code','input')}),flush=True)
    if completed.returncode:
        failed=True
        print(completed.stdout,flush=True)

name=f'{len(history)+1:03}-provenance'
snapshot=directory/name
snapshot.mkdir()
for path in [models/'properties.json']+[models/(p['id']+'.dfy') for p in props]:
    shutil.copyfile(path,snapshot/path.name)
run('all','provenance',[sys.executable,r'C:\z3seq\doc\nfv-audits\c3mv-71ec455a1\check_nfv_provenance.py','--models',str(snapshot)],name)
for prop in props:
    name=f'{len(history)+1:03}-{prop["id"]}-resolve'
    snapshot=directory/(name+'.dfy')
    shutil.copyfile(models/(prop['id']+'.dfy'),snapshot)
    run(prop['id'],'resolve',[str(root/'nfv-tools'/'dafny'/'Dafny.exe'),'resolve',str(snapshot),'--allow-warnings','--show-snippets','false'],name)
    history[-1]['input_sha256']=hashlib.sha256(snapshot.read_bytes()).hexdigest()
    history_path.write_text(json.dumps(history,indent=2)+'\n',encoding='utf-8',newline='\n')
raise SystemExit(1 if failed else 0)
