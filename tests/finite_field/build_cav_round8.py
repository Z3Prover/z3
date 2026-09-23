#!/usr/bin/env python3
"""Build the round-8 paper update without mixing old/default binary results.

Reads frozen logs only. Does not run solvers or resume the paused comparison.
The historical paper directory is preserved; outputs go to z3-qfff-cav-round8.
"""
import collections, csv, json, shutil, zipfile
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
SOURCES = ROOT / 'doc/papers/qf_ff'
OUT = ROOT / 'output/pdf/z3-qfff-cav-round8'
OUT.mkdir(parents=True, exist_ok=True)
# The checked archive contains only frozen report inputs, not solver binaries.
EVIDENCE = OUT / '.source-evidence'
with zipfile.ZipFile(SOURCES / 'evidence.zip') as archive:
    for name in archive.namelist():
        assert not Path(name).is_absolute() and '..' not in Path(name).parts
    archive.extractall(EVIDENCE)
OLD = EVIDENCE / 'historical'
DATA = EVIDENCE / 'round8'
SOLVED = {'sat', 'unsat', 'multi'}
ORDER = ['TV', 'TV-pureFF', 'CirC-D', 'CirC-S', 'QED2', 'Seq', 'Small', 'ASHR', 'Examples', 'Real']
KEYS = ['cvc5', 'cvc5_split', 'baseline', 'model_search']
LABELS = ['cvc5 GB\n1.3.4', 'cvc5 split\n1.3.4', 'Z3+FF\nprevious', 'Z3+FF\nnew policy']
COLORS = ['#7661a6', '#dc8527', '#8d9ca5', '#087f8c']

def readrows(path):
    return [json.loads(l) for l in path.read_text().splitlines() if l.strip()]

def solved(row): return row['result'] in SOLVED

# Copy only immutable historical figures/text, never stale PDFs or archives.
for name in ['llncs.cls', 'splncs04.bst', 'references.bib', 'numbers.tex',
             'category-coverage.pdf', 'runtime-overview.pdf', 'all-input-statuses-paper.pdf']:
    shutil.copy2(OLD / name, OUT / name)
refs = json.loads((EVIDENCE / 'reference-rows.json').read_text())
real_hashes = json.loads((EVIDENCE / 'real-input-hashes.json').read_text())
pairs = collections.defaultdict(dict)
for x in readrows(DATA / 'wide-clean/runs.jsonl'):
    assert x['variant'] not in pairs[x['case']]
    assert x['variant'] in KEYS[2:] and x['result'] != 'infrastructure_error'
    assert x['source_sha256'] == (real_hashes[x['case']] if x['family'] == 'Real' else x['case'])
    pairs[x['case']][x['variant']] = x
assert len(pairs) == 1256 and all(set(rr) == set(KEYS[2:]) for rr in pairs.values())
rows = {h: {**refs[h], **rr} for h, rr in pairs.items()}
assert all(set(rr) == set(KEYS) for rr in rows.values())
for rr in rows.values():
    assert len({tuple(r['answers']) for r in rr.values() if solved(r)}) <= 1
families = {f: [h for h in pairs if pairs[h]['baseline']['family'] == f] for f in ORDER}
assert sum(map(len, families.values())) == len(pairs)

def stats(hashes):
    return {'n': len(hashes), 'solved': {k: sum(solved(rows[h][k]) for h in hashes) for k in KEYS},
            'cvc_only': sum(not solved(rows[h]['model_search']) and any(solved(rows[h][k]) for k in KEYS[:2]) for h in hashes),
            'none': sum(not any(solved(rows[h][k]) for k in [*KEYS[:2], 'model_search']) for h in hashes)}
summary = {'population': '1,248 selected paper inputs plus 8 separate real-project diagnostics',
           'reference': 'Historical cvc5 1.3.4; no completed current-version comparison',
           'z3_measurement': json.loads((DATA / 'wide-clean/metadata.json').read_text()),
           'final_policy': json.loads((DATA / 'decision.json').read_text()),
           'families': {f: stats(hs) for f, hs in families.items()},
           'paper': stats([h for f, hs in families.items() if f != 'Real' for h in hs]),
           'real': stats(families['Real']), 'paired': stats(list(pairs))}
assert summary['paired']['solved']['baseline'] == 886
assert summary['paired']['solved']['model_search'] == 888
common = [rr for rr in rows.values() if all(solved(rr[k]) for k in KEYS[2:])]
assert len(common) == 886
assert not any(solved(rr['baseline']) and not solved(rr['model_search']) for rr in rows.values())
recorded = json.loads((DATA / 'clean-summary.json').read_text())['total']
for k, field in [('baseline', 'baseline_seconds'), ('model_search', 'candidate_seconds')]:
    assert abs(sum(rr[k]['seconds'] for rr in common) - recorded[field]) < 1e-8
models = readrows(DATA / 'wide-clean/models.jsonl')
assert len(models) == 559 and all(x['validation'] == 'valid' for x in models)
assert len({(x['case'], x['variant']) for x in models}) == len(models)
assert sum(rr[k]['result'] == 'sat' for rr in rows.values() for k in KEYS[2:]) == len(models)
regressions = json.loads((DATA / 'regressions-retained.json').read_text())
assert len(regressions) == 16 and all(x['returncode'] == 0 for x in regressions)
(OUT / 'round8-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
flat=[]
for h, rr in sorted(rows.items()):
    for k in KEYS:
        flat.append({'case':h,'source_sha256':rr['baseline']['source_sha256'],
                     'family':rr['baseline']['family'],'cohort':rr['baseline']['cohort'],
                     'name':rr['baseline']['name'],'solver':k,'result':rr[k]['result'],
                     'seconds':rr[k]['seconds'],'measurement': 'historical-cvc5-1.3.4' if k in KEYS[:2] else 'round8-wide-clean'})
with (OUT / 'round8-results.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(flat[0]));w.writeheader();w.writerows(flat)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'axes.spines.top':False,
                     'axes.spines.right':False,'pdf.fonttype':42,'ps.fonttype':42})

def save(fig, name):
    for ext in ['pdf','png','svg']: fig.savefig(OUT / (name+'.'+ext), dpi=190)
    plt.close(fig)

# Side-by-side categories with same inputs in every solver column.
def coverage(large=False):
    fig,(a,b)=plt.subplots(1,2,figsize=(10,6.3) if large else (6.6,4.5),
                           gridspec_kw={'width_ratios':[3.3,2]},layout='constrained')
    dd=[summary['families'][f] for f in ORDER]
    ar=np.array([[d['solved'][k]/d['n'] for k in KEYS] for d in dd])
    a.imshow(ar,vmin=0,vmax=1,cmap='YlGnBu',aspect='auto')
    for i,d in enumerate(dd):
        for j,k in enumerate(KEYS):
            a.text(j,i,f"{d['solved'][k]}/{d['n']}",ha='center',va='center',
                   fontsize=10 if large else 8,color='white' if ar[i,j]>.60 else '#16232e')
    a.set_xticks(range(4),LABELS,fontsize=10 if large else 8)
    a.xaxis.tick_top();a.tick_params(length=0)
    a.set_yticks(range(10),[f if f!='Real' else 'Real projects*' for f in ORDER])
    a.set_title('Coverage at 10 seconds',pad=40,fontweight='bold',fontsize=12 if large else 10)
    for s in a.spines.values():s.set_visible(False)
    a.set_xticks(np.arange(-.5,4,1),minor=True);a.set_yticks(np.arange(-.5,10,1),minor=True)
    a.grid(which='minor',color='white',linewidth=2);a.tick_params(which='minor',length=0)
    a.axhline(8.5,color='#263c46',lw=1.5)
    yy=np.arange(10);miss=[d['cvc_only'] for d in dd];none=[d['none'] for d in dd]
    b.barh(yy,miss,color='#c74732',label='cvc5 GB or split solves')
    b.barh(yy,none,left=miss,color='#d5dadd',label='None of the three solves')
    for i,(m,n) in enumerate(zip(miss,none)):b.text(m+n+3,i,f'{m} / {m+n}',va='center',fontsize=9 if large else 8)
    b.set_ylim(9.5,-.5);b.set_yticks([]);b.set_xlim(0,max(m+n for m,n in zip(miss,none))*1.40)
    b.set_title('Remaining new-policy misses',pad=40,fontweight='bold',fontsize=12 if large else 10)
    b.set_xlabel('Inputs; labels: cvc5-only / all misses',fontsize=9 if large else 8)
    b.grid(axis='x',alpha=.2);b.set_axisbelow(True)
    if large:
        fig.set_layout_engine('constrained', rect=(0, .13, 1, .87))
        fig.legend(*b.get_legend_handles_labels(),loc='lower center',bbox_to_anchor=(.57,.060),ncol=2,frameon=False,fontsize=9)
    else:
        fig.legend(*b.get_legend_handles_labels(),loc='outside lower center',ncol=2,frameon=False,fontsize=8)
    if large:
        fig.suptitle('Updated QF_FF comparison: 1,248 paper inputs + 8 real-project queries',fontsize=14,fontweight='bold')
        fig.text(.5,.008,'Historical cvc5 1.3.4 reference; paired Z3 previous/new policy. New cvc5-main campaign remains paused.\n*Real projects are separate diagnostics. Selected subset, not a new full-corpus result.',fontsize=9,ha='center',va='bottom')
    return fig
save(coverage(), 'round8-category-coverage')
save(coverage(True), 'round8-benchmark-overview')

fig,(a,b)=plt.subplots(1,2,figsize=(6.6,2.9),layout='constrained')
for k,label,c in zip(KEYS[2:],['Previous default','New policy'],COLORS[2:]):
    ts=sorted(rr[k]['seconds'] for rr in rows.values() if solved(rr[k]))
    a.plot(range(1,len(ts)+1),ts,label=f'{label} ({len(ts)})',color=c,lw=1.7)
a.set(yscale='log',ylim=(.005,12),xlabel='Inputs solved',ylabel='Wall seconds',title='Paired Z3 cactus')
a.legend(fontsize=8,frameon=False);a.grid(alpha=.2)
for rr in rows.values():
    x=rr['baseline'];y=rr['model_search']
    if not(solved(x) or solved(y)):continue
    b.scatter(x['seconds'] if solved(x) else 12,y['seconds'] if solved(y) else 12,
              s=10 if solved(x) and solved(y) else 30,alpha=.55,
              color='#087f8c' if solved(x) and solved(y) else '#c74732',edgecolors='none')
b.plot([.005,15],[.005,15],ls='--',lw=.8,color='#5d6870')
b.set(xscale='log',yscale='log',xlim=(.005,15),ylim=(.005,15),
      xlabel='Previous default (seconds)',ylabel='New policy (seconds)',title='Below diagonal = faster')
b.set_xticks([.01,.1,1,12],['0.01','0.1','1','T/O']);b.grid(alpha=.2)
save(fig,'round8-paired-runtime')
# cvc5 timing is historical: plot descriptively, never call it a paired speedup.
fig,(a,b)=plt.subplots(1,2,figsize=(6.6,2.9),layout='constrained')
for k,label,c in zip(KEYS,['cvc5 GB 1.3.4','cvc5 split 1.3.4','Z3 previous','Z3 new policy'],COLORS):
    ts=sorted(rr[k]['seconds'] for h,rr in rows.items() if h not in families['Real'] and solved(rr[k]))
    a.plot(range(1,len(ts)+1),ts,label=f'{label} ({len(ts)})',color=c,lw=1.3)
    ratios=sorted(rr[k]['seconds']/min(x['seconds'] for x in rr.values() if solved(x)) for h,rr in rows.items() if h not in families['Real'] and solved(rr[k]))
    b.step(ratios,np.arange(1,len(ratios)+1)/1248,where='post',color=c,lw=1.3)
a.set(yscale='log',ylim=(.003,12),xlabel='Paper inputs solved',ylabel='Wall seconds',title='Selected 1,248 paper inputs')
a.legend(fontsize=7,frameon=False);a.grid(alpha=.2)
b.set(xscale='log',xlim=(1,1000),ylim=(0,1),xlabel='Factor of fastest success',ylabel='Fraction of 1,248 inputs',title='Descriptive performance profile');b.grid(alpha=.2)
save(fig,'round8-reference-runtime')
# Compact, independent repetitions reveal both gains and latency costs.
iso=json.loads((DATA/'isolated-summary.json').read_text())
names=['Cyclic Example','Montgomery2Edwards','MACI Merkle','Small system14','BitElementMulAny']
lookup=['sec4_triangular','Montgomery2Edwards','maci-merkle','system14','BitElementMulAny']
fig,a=plt.subplots(figsize=(7.2,3.2),layout='constrained')
for i,(name,key) in enumerate(zip(names,lookup)):
    dd=next(v for n,v in iso.items() if key in n)
    for k,offset,color in [('baseline',-.14,COLORS[2]),('model_search',.14,COLORS[3])]:
        d=dd[k];t=10 if 'timeout' in d['results'] else d['median_seconds']
        a.barh(i+offset,t,height=.26,color=color,label=('Previous default' if k=='baseline' else 'New policy') if i==0 else None)
        a.text(t*1.1,i+offset,'timeout' if 'timeout' in d['results'] else f'{t:.3f} s',va='center',fontsize=8)
a.set_xscale('log');a.set_xlim(.01,40);a.set_yticks(range(5),names);a.invert_yaxis();a.set_xlabel('Median seconds, three isolated repetitions');a.grid(axis='x',alpha=.2);a.set_axisbelow(True);a.legend(frameon=False,loc='lower right',fontsize=8)
save(fig,'round8-isolated')

# Numeric appendix table is generated directly from the joins above.
table = '\n'.join(f"{f if f!='Real' else 'Real (separate)'} & {d['n']} & " + ' & '.join(str(d['solved'][k]) for k in KEYS) + f" & {d['cvc_only']} \\\\" for f,d in summary['families'].items())
(OUT/'round8-numbers.tex').write_text('\\newcommand{\\RoundEightRows}{'+table+'}\n')
shutil.copy2(SOURCES / 'paper.tex', OUT / 'paper.tex')
print(json.dumps({k:summary[k] for k in ['paper','real','paired']},indent=2))
