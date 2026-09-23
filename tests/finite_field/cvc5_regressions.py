#!/usr/bin/env python3
"""Compare the QF_FF cases in an external cvc5 checkout, without copying them.
Solver-specific incremental/model-check options are removed; formulas and
expected answers are unchanged. Timing-specific and non-QF_FF cases are excluded.
"""
import argparse
import json
import re
import statistics
import subprocess
import time
from pathlib import Path


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--suite',type=Path,required=True)
    ap.add_argument('--z3',default='build-ff-cmake/z3')
    ap.add_argument('--cvc5',required=True)
    ap.add_argument('--out',type=Path,default=Path('tests/finite_field/results/cvc5-regressions.json'))
    ap.add_argument('--repeat',type=int,default=3)
    ap.add_argument('--timeout',type=float,default=10)
    args=ap.parse_args();rows=[];failed=False
    for path in sorted(args.suite.glob('*.smt2')):
        text=path.read_text()
        expected=re.findall(r'; EXPECT: (sat|unsat|unknown)\b',text)
        if '(set-logic QF_FF)' not in text or not expected or 'unknown' in expected:continue
        text=re.sub(r'^\(set-option :(?:incremental|check-models)[^\n]*\n','',text,flags=re.M)
        row={'case':path.name,'expected':expected}
        for label,cmd in [('z3',[args.z3,'-in']),('cvc5',[args.cvc5,'--lang=smt2','--incremental']),('cvc5_split',[args.cvc5,'--lang=smt2','--incremental','--ff-solver=split'])]:
            durations=[];actual=[];error=''
            for _ in range(args.repeat):
                start=time.perf_counter()
                try:
                    r=subprocess.run(cmd,input=text,text=True,capture_output=True,timeout=args.timeout)
                    durations.append(time.perf_counter()-start)
                    actual=re.findall(r'^(sat|unsat|unknown)$',r.stdout,re.M)
                    if r.returncode or '(error' in r.stdout:error=r.stderr+r.stdout;break
                except subprocess.TimeoutExpired:actual=['timeout'];break
            row[label]={'actual':actual,'seconds':statistics.median(durations) if durations else args.timeout}
            if error:row[label]['error']=error
            failed |= bool(error) or actual!=expected
        rows.append(row);print(json.dumps(row),flush=True)
        args.out.parent.mkdir(parents=True,exist_ok=True)
        args.out.write_text(json.dumps(rows,indent=2)+'\n')
    for label in ['z3','cvc5','cvc5_split']:
        passed=sum(not row[label].get('error') and row[label]['actual']==row['expected'] for row in rows)
        print(f'{label}: {passed}/{len(rows)} upstream regression cases passed')
    raise SystemExit(1 if failed else 0)

if __name__=='__main__':main()
