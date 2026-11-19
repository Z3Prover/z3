"""Replay byte-checked batch-four models using explicitly trusted tools."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time


def at(base,name):
    path=(base/Path(name.replace('\\','/'))).resolve()
    assert path.is_relative_to(base.resolve()),'Evidence path escapes bundle'
    return path


def run_checks(bundle,chosen,dafny,solver,output):
    bundle=bundle.resolve()
    output=output.resolve()
    assert not output.is_relative_to(bundle),'Use output outside immutable bundle'
    assert not output.exists(),'Use a new output directory'
    models=bundle/'nfv4-models'
    for check in chosen:
        assert hashlib.sha256(at(models,check['input']).read_bytes()).hexdigest()==check['input_sha256']
    output.mkdir(parents=True)
    results=[]
    for check in chosen:
        path=at(models,check['input'])
        command=[str(dafny.resolve()),'verify',str(path),'--solver-path',str(solver.resolve()),'--verification-time-limit','30','--cores','2','--allow-warnings','--show-snippets','false']
        if check.get('mbqi',False):
            assert check['command'][check['command'].index('--solver-option')+1]=='O:smt.mbqi=true'
            command+=['--solver-option','O:smt.mbqi=true']
        start=time.monotonic()
        completed=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
        log=output/(path.stem+'.log')
        log.write_text(completed.stdout,encoding='utf-8',newline='\n')
        results.append(dict(sequence=check['sequence'],input=check['input'],input_sha256=check['input_sha256'],expected_exit=check['exit_code'],actual_exit=completed.returncode,matched=check['exit_code']==completed.returncode,seconds=round(time.monotonic()-start,3),command=command,log=log.name,log_sha256=hashlib.sha256(log.read_bytes()).hexdigest()))
        (output/'results.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8',newline='\n')
        print(json.dumps({k:results[-1][k] for k in ['sequence','expected_exit','actual_exit','matched']}),flush=True)
    return 0 if all(r['matched'] for r in results) else 1


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--dafny',type=Path,required=True)
    parser.add_argument('--solver',type=Path,required=True)
    parser.add_argument('--select',type=int,nargs='+')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    checks=json.loads((args.bundle/'nfv4-models'/'checks.json').read_text(encoding='utf-8'))
    assert not args.select or set(args.select)<={c['sequence'] for c in checks},'Unknown check number'
    chosen=[c for c in checks if not args.select or c['sequence'] in args.select]
    raise SystemExit(run_checks(args.bundle,chosen,args.dafny,args.solver,args.output))
