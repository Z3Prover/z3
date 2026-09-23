#!/usr/bin/env python3
"""Complete current-binary coverage without mixing historical Z3 revisions."""
import collections,concurrent.futures,hashlib,json,platform,random,shutil,time
from pathlib import Path
from benchmark_artifacts import run,prepare
from artifact_analysis import load
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'tests/finite_field/results/cav-overview';OUT.mkdir(exist_ok=True)
CORPUS=Path('/private/tmp/ff-paper-corpus');BINARY=Path('/private/tmp/ff-round7/binaries/retained')
manifest,members,refs=load(ROOT/'tests/finite_field/results/paper-artifacts')
hashbin=hashlib.sha256(BINARY.read_bytes()).hexdigest();assert hashbin=='14772994298957b7b5c9d402b7e830b6b542e48077fcf20d46845aeeb83f249e'
meta=dict(binary=str(BINARY),binary_sha256=hashbin,timeout=10,memory_mib=4096,jobs=8,seed=20260923,platform=platform.platform(),reused='1118 exact-input/binary matches from performance-round7; no parameter overrides',reference='historical cvc5 1.3.4 runs; adjudications applied at analysis',created=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
if not (OUT/'metadata.json').exists():(OUT/'metadata.json').write_text(json.dumps(meta,indent=2))
path=OUT/'z3-runs.jsonl'
if not path.exists():
 with path.open('w') as f:
  for group in ['prior-final','fresh-final','confirm-final']:
   folder=ROOT/'tests/finite_field/results/performance-round7'/group
   assert json.loads((folder/'metadata.json').read_text())['configs']['candidate']['binary_sha256']==hashbin
   for line in (folder/'runs.jsonl').read_text().splitlines():
    x=json.loads(line)
    if x['variant']=='candidate' and x['case'] in members:
     x.update(sha256=x['case'],solver='z3',measurement_source='performance-round7/'+group)
     f.write(json.dumps(x)+'\n')
done={json.loads(l)['sha256'] for l in path.read_text().splitlines()};assert len(done)>=1118
hashes=sorted(set(members)-done);random.Random(20260923).shuffle(hashes)
for _ in range(3):run(dict(command=[str(BINARY),'-in'],smt='(set-logic QF_FF)\n(declare-const x (_ FiniteField 7))\n(assert (= x (as ff2 (_ FiniteField 7))))\n(check-sat)\n',checks=1,timeout=10))
def task(h):
 data=(CORPUS/'inputs'/(h+'.smt2')).read_bytes();assert hashlib.sha256(data).hexdigest()==h
 smt=prepare(data.decode());checks=members[h][0]['checks']
 x=run(dict(command=[str(BINARY),'-in'],smt=smt,checks=checks,timeout=10,memory_mib=4096))
 x.update(sha256=h,solver='z3',input_sha256=hashlib.sha256(smt.encode()).hexdigest(),measurement_source='cav-completion',path=str(CORPUS/'inputs'/(h+'.smt2')))
 if x['result'] in ['sat','unsat']:x.pop('stdout')
 return x
print(len(done),'reused;',len(hashes),'new runs',flush=True)
with path.open('a',buffering=1) as f,concurrent.futures.ThreadPoolExecutor(8) as pool:
 for i,future in enumerate(concurrent.futures.as_completed([pool.submit(task,h) for h in hashes]),1):
  x=future.result();f.write(json.dumps(x)+'\n')
  if i%50==0:print(i,'/',len(hashes),x['result'],flush=True)
print('COMPLETE',flush=True)
