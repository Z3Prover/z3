"""Replay exact byte-checked Dafny artifacts using explicitly trusted tools."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--dafny',type=Path,required=True)
parser.add_argument('--solver',type=Path,required=True)
parser.add_argument('--select',nargs='+')
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
root=Path(__file__).resolve().parent
models=root/'nfv3-models'
output=args.output.resolve()
assert not output.is_relative_to(root),'Output must be outside the immutable report'
assert not output.exists(),'Use a new output directory'
checks=json.loads((models/'checks.json').read_text(encoding='utf-8'))
number=lambda c:Path(c['input'].replace('\\','/')).name.split('-')[0]
assert not args.select or set(args.select)<={number(c) for c in checks},'Unknown check number'
chosen=[c for c in checks if not args.select or number(c) in args.select]
output.mkdir(parents=True)
results=[]
for check in chosen:
    relative=Path(check['input'].replace('\\','/'))
    path=(models/relative).resolve()
    assert path.is_relative_to(models.resolve())
    assert hashlib.sha256(path.read_bytes()).hexdigest()==check['input_sha256']
    command=[str(args.dafny.resolve()),'verify',str(path),'--solver-path',str(args.solver.resolve()),'--verification-time-limit','30','--cores','2','--allow-warnings','--show-snippets','false']
    if check.get('mbqi',False):
        assert check['command'][check['command'].index('--solver-option')+1]=='O:smt.mbqi=true'
        command+=['--solver-option','O:smt.mbqi=true']
    start=time.monotonic()
    completed=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
    log=output/(relative.stem+'.log')
    log.write_text(completed.stdout,encoding='utf-8',newline='\n')
    record=dict(input=str(relative),input_sha256=check['input_sha256'],expected_exit=check['exit_code'],actual_exit=completed.returncode,matched=check['exit_code']==completed.returncode,seconds=round(time.monotonic()-start,3),command=command,log=log.name)
    results.append(record)
    (output/'results.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:record[k] for k in ('input','expected_exit','actual_exit','matched')}),flush=True)
raise SystemExit(0 if all(r['matched'] for r in results) else 1)
