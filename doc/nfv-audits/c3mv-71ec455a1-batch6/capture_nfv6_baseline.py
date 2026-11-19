"""Capture fetched master drift and coverage identity; never execute source."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

ROOT=Path(__file__).parent
REPO=Path(r'C:\z3seq')
SOURCE='71ec455a18702fe695d0c924a535ff9f385bd58d'
OLD='c2460a558fc6fee3cf15cfebd2d3f642ebf77770'
PUBLISHED='4be813a75bdc59574df23da8ce5805a262171ba9'


def raw(*args):
    return subprocess.check_output(['git','--no-pager',*args],cwd=REPO)


def git(*args):
    return raw(*args).decode('utf-8').strip()


def paths(a,b):
    return set(filter(None,git('diff','--no-renames','--name-only',a,b).splitlines()))


def blobs(revision,names):
    result={}
    for row in raw('ls-tree','-r','-z',revision,'--',*names).split(b'\0'):
        if row:
            meta,name=row.split(b'\t',1)
            result[name.decode()]=meta.split()[2].decode()
    return result


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert not (ROOT/'nfv6-baseline.json').exists()
assert git('branch','--show-current')=='c3mv' and git('rev-parse','HEAD')==PUBLISHED
assert not git('status','--porcelain=v1','-uall')
assert git('rev-parse','HEAD:src')==git('rev-parse',SOURCE+':src')=='caa5a9922f074f9f4adc8f7c98e1685be9626503'
assert git('rev-parse','refs/stash')=='7af7fad70e9cea38601c67ff00d89f6b5576c2d6'
master=git('rev-parse','refs/remotes/origin/master')
assert master=='bcad05a7bf7dd9b82bd7a665018e0480e737264b'
assert subprocess.run(['git','merge-base','--is-ancestor',OLD,master],cwd=REPO).returncode==0
base=git('merge-base',SOURCE,master)
assert base=='437536cd64a544a1c329fc57d83e56e294fdf47c'
branch,direct,drift=paths(base,SOURCE),paths(master,SOURCE),paths(OLD,master)
model_paths=set()
selected=[]
for folder in ['nfv-models','nfv2-models','nfv3-models','nfv5-models']:
    for p in json.loads((ROOT/folder/'properties.json').read_text(encoding='utf-8-sig')):
        model_paths.add(p['path'])
        selected.append(dict(id=p['id'],path=p['path'],entry=p['entry_point'],span=p.get('source_span')))
before,after,source=[blobs(r,sorted(drift)) for r in [OLD,master,SOURCE]]
rows=[]
for name in sorted(drift):
    rows.append(dict(path=name,kind='build' if name.endswith('CMakeLists.txt') else 'test' if name.startswith('src/test/') else 'production',
        overlaps_branch_delta=name in branch,overlaps_selected_entry_path=name in model_paths,
        old_master_blob=before.get(name),new_master_blob=after.get(name),source_blob=source.get(name),
        source_equals_old_master=source.get(name)==before.get(name)))
patch=ROOT/'nfv6-master-drift.patch'
assert not patch.exists()
patch.write_bytes(raw('diff','--no-ext-diff','--binary',OLD,master,'--','src'))
commits=[]
for line in git('log','--format=%H%x09%s',OLD+'..'+master).splitlines():
    oid,subject=line.split('\t',1)
    commits.append(dict(commit=oid,subject=subject))
prior_names=['c3mv-71ec455a1','c3mv-71ec455a1-batch2','c3mv-71ec455a1-batch3','c3mv-71ec455a1-batch4','c3mv-71ec455a1-batch5']
data=dict(stage='nfv6-reconcile',status='source-only capture complete',recorded_utc=datetime.now(timezone.utc).isoformat(),
    production_source=SOURCE,publication_head=PUBLISHED,old_master=OLD,master=master,merge_base=base,
    source_tree=git('rev-parse','HEAD:src'),stash=git('rev-parse','refs/stash'),branch='c3mv',worktree_clean=True,
    commits=commits,master_drift=rows,master_drift_patch_sha256=sha(patch),
    counts=dict(branch_files=len(branch),branch_src=sum(p.startswith('src/') for p in branch),
        direct_files=len(direct),direct_src=sum(p.startswith('src/') for p in direct),
        drift_files=len(drift),drift_production=sum(r['kind']=='production' for r in rows)),
    branch_changed_paths=sorted(branch),direct_master_to_source_paths=sorted(direct),
    master_drift_overlap_branch=sorted(drift&branch),master_drift_overlap_selected_entry_paths=sorted(drift&model_paths),
    primary_entries=selected,previous_report_trees={n:git('rev-parse','HEAD:doc/nfv-audits/'+n) for n in prior_names},
    reviewed_production_patch_paths=[r['path'] for r in rows if r['kind']=='production'],
    semantics='Master-only new changes are not c3mv-introduced regressions. Path nonoverlap does not establish semantic independence or verify native integration.',
    next_stage='nfv6-coverage',native_executions=0,verifier_invocations=0,new_selected_properties=0,schedule_id=2,stop_schedule=False)
(ROOT/'nfv6-baseline.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='captured',master=master,merge_base=base,counts=data['counts'],
    overlaps_branch=data['master_drift_overlap_branch'],overlaps_selected=data['master_drift_overlap_selected_entry_paths'],
    production_source_equals_old_master=[r['path'] for r in rows if r['kind']=='production' and r['source_equals_old_master']],
    baseline_sha256=sha(ROOT/'nfv6-baseline.json'),patch_sha256=sha(patch)),indent=2))
