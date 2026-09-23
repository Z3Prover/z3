#!/usr/bin/env python3
"""Independently check all current single-query SAT results outside timing."""
import collections,concurrent.futures,hashlib,json
from pathlib import Path
from benchmark_artifacts import run,prepare
from benchmark_public_ff import sexprs
from validate_artifact_models import validate
from cav_data import current_rows
ROOT=Path(__file__).resolve().parents[2];OUT=ROOT/'tests/finite_field/results/cav-overview';CORPUS=Path('/private/tmp/ff-paper-corpus')
rows=list(current_rows().values());assert len(rows)==4212
binary=json.loads((OUT/'metadata.json').read_text())['binary'];path=OUT/'models.jsonl'
if not path.exists():
 with path.open('w') as f:
  for g in ['prior-final','fresh-final','confirm-final']:
   for l in (ROOT/'tests/finite_field/results/performance-round7'/g/'models.jsonl').read_text().splitlines():
    x=json.loads(l)
    if x['variant']=='candidate':x.update(sha256=x['case'],solver='z3',source='round7/'+g);f.write(json.dumps(x)+'\n')
done={json.loads(l)['sha256'] for l in path.read_text().splitlines()};targets=[x for x in rows if x['result']=='sat' and x['sha256'] not in done]
def check(row):
 h=row['sha256'];original=(CORPUS/'inputs'/(h+'.smt2')).read_text();assert hashlib.sha256(original.encode()).hexdigest()==h
 commands=sexprs(original);names=[c[1] for c in commands if c[0]=='declare-const' or (c[0]=='declare-fun' and c[2]==[])]
 smt='(set-option :produce-models true)\n'+prepare(original, solver='z3')
 if names:smt+='\n(get-value ('+' '.join(names)+'))\n'
 r=run(dict(command=[binary,'-in'],smt=smt,checks=1,timeout=30,memory_mib=4096,output_limit=None));out=dict(sha256=h,solver='z3',model_result=r['result'],source='cav-completion')
 try:
  assert r['result']=='sat',r['result'];out.update(validation='valid',assertions=validate(original,r['stdout']))
 except Exception as e:out.update(validation='failed',detail=repr(e),replay=r)
 return out
print(len(done),'reused;',len(targets),'new model checks',flush=True)
with path.open('a',buffering=1) as f,concurrent.futures.ThreadPoolExecutor(4) as pool:
 for i,future in enumerate(concurrent.futures.as_completed([pool.submit(check,x) for x in targets]),1):
  x=future.result();f.write(json.dumps(x)+'\n')
  if i%100==0 or x['validation']!='valid':print(i,len(targets),x['validation'],flush=True)
result=[json.loads(l) for l in path.read_text().splitlines()];counts=collections.Counter(x['validation'] for x in result);print(dict(counts),flush=True)
assert len(result)==sum(x['result']=='sat' for x in rows);assert counts.get('failed',0)==0
