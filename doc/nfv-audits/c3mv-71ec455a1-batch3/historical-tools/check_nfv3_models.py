"""Preserve every draft provenance/resolve input and complete diagnostic log."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

root=Path(__file__).parent
models=root/'nfv3-models'
drafts=models/'drafts'
drafts.mkdir(exist_ok=True)
history_path=models/'draft-checks.json'
history=json.loads(history_path.read_text()) if history_path.exists() else []
props=json.loads((models/'properties.json').read_text())
failed=False
def run(ident,phase,command,artifact,input_files):
    global failed
    start=time.monotonic()
    completed=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
    log=drafts/(artifact+'.log')
    log.write_text(completed.stdout,encoding='utf-8',newline='\n')
    record=dict(id=ident,phase=phase,recorded_utc=datetime.now(timezone.utc).isoformat(),seconds=round(time.monotonic()-start,3),exit_code=completed.returncode,command=command,input=artifact,inputs=[dict(path=str(p.relative_to(models)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in input_files],log=str(log.relative_to(models)),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
    history.append(record)
    history_path.write_text(json.dumps(history,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:record[k] for k in ('id','phase','seconds','exit_code','input')}),flush=True)
    if completed.returncode:
        failed=True
        print(completed.stdout,flush=True)

name=f'{len(history)+1:03}-provenance'
snapshot=drafts/name
snapshot.mkdir()
for p in [models/'properties.json',root/'check_nfv3_provenance.py',root/'nfv3-coverage-source-inventory.json']+[models/(p['id']+'.dfy') for p in props]:
    shutil.copyfile(p,snapshot/p.name)
run('all','provenance',[sys.executable,str(snapshot/'check_nfv3_provenance.py'),'--models',str(snapshot),'--inventory',str(snapshot/'nfv3-coverage-source-inventory.json')],name,list(snapshot.iterdir()))
for prop in props:
    name=f'{len(history)+1:03}-{prop["id"]}-resolve'
    snapshot=drafts/(name+'.dfy')
    shutil.copyfile(models/(prop['id']+'.dfy'),snapshot)
    run(prop['id'],'resolve',[str(root/'nfv-tools'/'dafny'/'Dafny.exe'),'resolve',str(snapshot),'--allow-warnings','--show-snippets','false'],name,[snapshot])
raise SystemExit(1 if failed else 0)
