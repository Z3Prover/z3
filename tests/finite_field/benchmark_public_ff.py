#!/usr/bin/env python3
"""Run public QF_FF benchmarks unchanged; independently evaluate every SAT model."""
import argparse
import hashlib
import json
import math
import re
import statistics
from pathlib import Path
from benchmark_zk import run_once


def sexprs(text):
    tokens=re.findall(r';[^\n]*|\(|\)|\|[^|]*\||"(?:[^"]|"")*"|[^\s()]+',text)
    stack=[[]]
    for token in tokens:
        if token.startswith(';'): continue
        if token=='(': stack.append([])
        elif token==')':
            value=stack.pop();stack[-1].append(value)
        else: stack[-1].append(token)
    assert len(stack)==1
    return stack[0]


def evaluate(node,env,p):
    if isinstance(node,str):
        if node=='true':return True
        if node=='false':return False
        if node.startswith('#f'):return int(node[2:].split('m')[0])%p
        return env[node]
    if node[0]=='let':
        env=env.copy()
        while isinstance(node,list) and node[0]=='let':
            values={name:evaluate(value,env,p) for name,value in node[1]}
            env.update(values);node=node[2]
        return evaluate(node,env,p)
    if node[0]=='as':return int(node[1][2:])%p
    op=node[0]
    if op=='ite':return evaluate(node[2] if evaluate(node[1],env,p) else node[3],env,p)
    values=[evaluate(x,env,p) for x in node[1:]]
    if op=='ff.add':return sum(values)%p
    if op=='ff.mul':return math.prod(values)%p
    if op=='ff.neg':return -values[0]%p
    if op=='ff.bitsum':return sum((1<<i)*x for i,x in enumerate(values))%p
    if op=='=':return all(x==values[0] for x in values[1:])
    if op=='distinct':return len(set(values))==len(values)
    if op=='not':return not values[0]
    if op=='and':return all(values)
    if op=='or':return any(values)
    if op=='=>':return not values[0] or values[1]
    if op=='xor':return bool(sum(values)%2)
    raise ValueError(('unsupported operator',op))


def validate(smt,model):
    commands=sexprs(smt)
    p=int(re.search(r'\(_ FiniteField (\d+)\)',smt)[1])
    names=[x[1] for x in commands if x[0]=='declare-fun' and x[2]==[]]
    assignments=next(x for x in sexprs(model) if isinstance(x,list) and len(x)==len(names) and all(isinstance(y,list) and len(y)==2 and y[0] in names for y in x))
    env={name:evaluate(value,{},p) for name,value in assignments}
    assert set(env)==set(names)
    assert all(evaluate(x[1],env,p) is True for x in commands if x[0]=='assert')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--suite',type=Path,default=Path('/private/tmp/ff-public-cav23'))
    ap.add_argument('--manifest',type=Path,default=Path(__file__).with_name('fixtures')/'cav23-manifest.json')
    ap.add_argument('--z3',default='build-ff-cmake/z3');ap.add_argument('--cvc5',required=True)
    ap.add_argument('--baseline')
    ap.add_argument('--only',default='',help='comma-separated solver labels')
    ap.add_argument('--filter',default='')
    ap.add_argument('--timeout',type=float,default=3);ap.add_argument('--repeat',type=int,default=3)
    ap.add_argument('--out',type=Path,default=Path('tests/finite_field/results/public-cav23.json'))
    args=ap.parse_args();manifest=json.loads(args.manifest.read_text())
    commands={'z3':[args.z3,'-in'],'z3_simplify':[args.z3,'-in'],
              'z3_raw':[args.z3,'-in'],
              'cvc5':[args.cvc5,'--lang=smt2',f'--tlimit-per={int(args.timeout*1000)}'],
              'cvc5_split':[args.cvc5,'--lang=smt2','--ff-solver=split',f'--tlimit-per={int(args.timeout*1000)}']}
    if args.baseline: commands['baseline']=[args.baseline,'-in']
    if args.only: commands={k:v for k,v in commands.items() if k in args.only.split(',')}
    assert commands
    report=dict(source=manifest['source'],selection=manifest['selection'],timeout_seconds=args.timeout,repeat=args.repeat,
                input_manifest_sha256=hashlib.sha256(args.manifest.read_bytes()).hexdigest(),
                binaries={k:hashlib.sha256(Path(v[0]).read_bytes()).hexdigest() for k,v in commands.items()},
                expected_status='not supplied by input; compare definite solver answers and independently check SAT models',cases=[])
    failed=False
    for entry in manifest['files']:
        if args.filter and args.filter not in entry['file']: continue
        data=(args.suite/entry['file']).read_bytes();assert hashlib.sha256(data).hexdigest()==entry['sha256']
        original=data.decode();assert len(re.findall(r'\(check-sat\)',original))==1
        prefix=re.sub(r'\(check-sat\)','',original)
        names=[x[1] for x in sexprs(original) if x[0]=='declare-fun' and x[2]==[]]
        row=dict(case=entry['file'],property=entry['property'],mutation=entry['mutation'],compiler=entry['compiler'],terms=entry['terms'],solvers={})
        for label,cmd in commands.items():
            z3=label.startswith('z3') or label=='baseline'
            header=f'(set-option :timeout {int(args.timeout*1000)})\n' if z3 else ''
            check='(check-sat-using (then ff-simplify (or-else ff-solve ff-sat (then ff2bv qfbv))))\n' if label=='z3_simplify' else '(check-sat)\n'
            if label=='z3_raw':check='(check-sat-using (or-else ff-solve ff-sat (then ff2bv qfbv)))\n'
            stats='(get-info :all-statistics)\n' if z3 else ''
            runs=[]
            for _ in range(args.repeat):
                run=run_once(cmd,header+prefix+check+stats,args.timeout+2)
                if run['result']!='error':run.pop('stdout');run.pop('stderr')
                runs.append(run)
                if run['result'] not in ['sat','unsat']:break
            item=dict(result=runs[-1]['result'],seconds=statistics.median(x['seconds'] for x in runs),peak_rss_mib=max(x['peak_rss_mib'] for x in runs),runs=runs)
            assert len({x['result'] for x in runs})==1
            if item['result']=='sat':
                model=run_once(cmd,header+'(set-option :produce-models true)\n'+prefix+check+'(get-value ('+' '.join(names)+'))\n',args.timeout+2)
                if model['result']=='sat':validate(original,model['stdout']);item['model_validated']=True
                else:item['model_validated']=False;item['model_run_result']=model['result'];failed=True
            failed |= item['result']=='error'
            row['solvers'][label]=item
        definite={v['result'] for v in row['solvers'].values() if v['result'] in ['sat','unsat']}
        assert len(definite)<=1,('solver disagreement',row)
        report['cases'].append(row);args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(json.dumps(report,indent=2)+'\n')
        print(entry['file'],json.dumps({k:(v['result'],round(v['seconds'],4)) for k,v in row['solvers'].items()}),flush=True)
    print(f"{len(report['cases'])} public cases recorded; errors/missing SAT validation: {failed}")
    return int(failed)


if __name__=='__main__':raise SystemExit(main())
