#!/usr/bin/env python3
"""Summarize a completed versioned FMCAD comparison and draw coverage figures."""
import argparse,collections,csv,json,re,statistics
from pathlib import Path


EXPLORER = Path(__file__).with_name('ff_paper_explorer.html').read_text()

def category(member):
    m=re.search(r'compilation-(deterministic|sound)-.*-ff-(circ|zokcirc|zokref)-',member)
    return (dict(circ='CirC',zokcirc='ZoKrates/CirC',zokref='ZoKrates/ref')[m[2]]+' / '+dict(deterministic='determinism',sound='soundness')[m[1]]) if m else 'Other'


def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);ap.add_argument('--extra',type=Path);args=ap.parse_args();out=args.directory
    rows=list(map(json.loads,(out/'runs.jsonl').read_text().splitlines()));meta=json.loads((out/'metadata.json').read_text());selection=json.loads((out/'selection.json').read_text())
    if args.extra:
        extra=json.loads((args.extra/'metadata.json').read_text())
        assert all(meta[k]==extra[k] for k in ['timeout','jobs','memory_mib','python','distinct'])
        assert json.loads((args.extra/'selection.json').read_text())==selection
        meta['configurations']+=extra['configurations']
        rows+=list(map(json.loads,(args.extra/'runs.jsonl').read_text().splitlines()))
    weights=collections.Counter(r['sha256'] for r in selection)
    by={c['id']:{} for c in meta['configurations']}
    for r in rows:
        assert r['sha256'] not in by[r['configuration']],'duplicate measurement'
        by[r['configuration']][r['sha256']]=r
    assert all(len(r)==meta['distinct'] for r in by.values()),'incomplete comparison'
    for c in meta['configurations']:
        if c['kind']!='solve':
            by[c['id']+'-generation']={h:dict(r,status='produced' if r.get('produced') else r['status'],seconds=r.get('generation_seconds',r['seconds'])) for h,r in by[c['id']].items()}
    success=lambda r:r['status'] in ['unsat','checked','produced']
    summary={}
    for c,rs in by.items():
        ok=[r for r in rs.values() if success(r)]
        summary[c]=dict(counts=dict(collections.Counter(r['status'] for r in rs.values())),successful=len(ok),member_weighted_successful=sum(weights[r['sha256']] for r in ok),median_seconds=statistics.median(r['seconds'] for r in ok) if ok else None,categories={k:dict(successful=sum(success(r) for r in rs.values() if category(r['member'])==k),total=sum(category(r['member'])==k for r in rs.values())) for k in sorted({category(r['member']) for r in rs.values()})})
    proof_names=['paper-candidate-proof','z3-ff-proof'];proof_sets=[{h for h,r in by[c].items() if success(r)} for c in proof_names]
    common=set.intersection(*proof_sets);zonly=proof_sets[1]-proof_sets[0];conly=proof_sets[0]-proof_sets[1]
    comparison=dict(common=len(common),candidate_only=[dict(sha256=h,member=by[proof_names[0]][h]['member'],z3_reason=by[proof_names[1]][h].get('reason',by[proof_names[1]][h]['status'])) for h in sorted(conly)],z3_only=[dict(sha256=h,member=by[proof_names[1]][h]['member'],candidate_reason=by[proof_names[0]][h].get('reason',by[proof_names[0]][h]['status'])) for h in sorted(zonly)],common_cumulative_seconds={c:sum(by[c][h]['seconds'] for h in common) for c in proof_names},common_median_seconds={c:statistics.median(by[c][h]['seconds'] for h in common) if common else None for c in proof_names})
    # Profile accepted candidate-only proof text to guide the next implementation
    # work. These are rule-use counts, not a replacement for the checker.
    for item in comparison['candidate_only']:
        text=(out/'paper-candidate-proof'/item['sha256']/'proof.alethe').read_text()
        item['alethe_rules']=dict(collections.Counter(re.findall(r':rule\s+([\w_]+)',text)))
        item['pac_rules']=dict(collections.Counter(re.findall(r'^\s*([alrbe])\s+',text,re.M)))
    paper_modes=['artifact-clean-wip-gb','artifact-clean-wip-nosimp','paper-candidate-proof-generation','paper-candidate-proof']
    common_groups={}
    common_md=[]
    for label,modes in [('Artifact modes',paper_modes),('Artifact modes plus Z3',paper_modes+['z3-ff-solve','z3-ff-proof-generation','z3-ff-proof'])]:
        hashes=set.intersection(*[{h for h,r in by[c].items() if success(r)} for c in modes])
        times={c:sum(by[c][h]['seconds'] for h in hashes) for c in modes}
        base=times['artifact-clean-wip-nosimp']
        common_groups[label]=dict(distinct=len(hashes),sha256=sorted(hashes),cumulative_seconds=times,relative_to_no_simplification={c:t/base if base else None for c,t in times.items()})
        common_md += [f'### {label}: {len(hashes)} common successes', '', '| Configuration | Cumulative time | Relative to artifact no-simplification |', '|---|---:|---:|']
        common_md += [f'| {c} | {t:.3f} s | {t/base:.2f}x |' for c,t in times.items()] if base else []
        common_md.append('')
    (out/'common-times.md').write_text('\n'.join(common_md))
    comparison['common_time_groups']=common_groups
    (out/'summary.json').write_text(json.dumps(dict(configurations=summary,proof_comparison=comparison),indent=2)+'\n')
    with (out/'per-input.csv').open('w') as f:
        w=csv.writer(f);w.writerow(['configuration','sha256','member','category','status','seconds','reason'])
        for c,rs in by.items():
            for h,r in sorted(rs.items()):w.writerow([c,h,r['member'],category(r['member']),r['status'],r['seconds'],r.get('reason','')])
    md=['| Configuration | Success / '+str(meta['distinct'])+' | Weighted / '+str(len(selection))+' | Median successful time |','|---|---:|---:|---:|']
    for c,r in summary.items():md.append(f"| {c} | {r['successful']} | {r['member_weighted_successful']} | {r['median_seconds']:.3f} s |" if r['median_seconds'] is not None else f'| {c} | 0 | 0 | — |')
    (out/'table.md').write_text('\n'.join(md)+'\n')
    explorer=[dict(sha256=h,member=by[proof_names[0]][h]['member'],category=category(by[proof_names[0]][h]['member']),results={c:{k:r[h].get(k) for k in ['status','seconds','reason']} for c,r in by.items()}) for h in sorted(by[proof_names[0]])]
    (out/'explorer.html').write_text(EXPLORER.replace('PAYLOAD',json.dumps(explorer).replace('</','<\\/')))
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import numpy as np
    plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
    names={'artifact-clean-wip-gb':'Artifact baseline (clean-wip)','artifact-clean-wip-nosimp':'Artifact baseline, no simplification','cvc5-1.3.3-gb':'CVC5 1.3.3','cvc5-1.3.3-nosimp':'CVC5 1.3.3, no simplification','paper-candidate-gb':'Paper candidate, default','paper-candidate-nosimp':'Paper candidate, no simplification','paper-candidate-proof-generation':'Paper candidate + proof','paper-candidate-proof':'Paper candidate + proof + check','z3-ff-solve':'Z3+FF solver','z3-ff-proof-generation':'Z3+FF certificate production','z3-ff-proof':'Z3+FF + proof + check'}
    fig,ax=plt.subplots(figsize=(10,6))
    for c in ['artifact-clean-wip-gb','artifact-clean-wip-nosimp','paper-candidate-proof-generation','paper-candidate-proof','z3-ff-solve','z3-ff-proof']:
        times=sorted(r['seconds'] for r in by[c].values() if success(r))
        ax.step(times,range(1,len(times)+1),where='post',label=f'{names[c]} ({len(times)})')
    ax.set(xscale='log',xlim=(.01,meta['timeout']),ylim=(0,meta['distinct']+10),xlabel='Whole-pipeline wall time (s)',ylabel='Completed distinct inputs',title='FMCAD finite-field artifact — fresh native comparison')
    ax.grid(alpha=.2);ax.legend(loc='upper left',fontsize=9)
    fig.text(.5,.015,f"{meta['distinct']} distinct inputs / {len(selection)} member paths · {meta['timeout']:g} s per pipeline · {meta['jobs']} workers · no Lean-SMT",ha='center',fontsize=9)
    fig.tight_layout(rect=(0,.04,1,1));fig.savefig(out/'cactus.png',dpi=180);plt.close(fig)
    cols=['artifact-clean-wip-gb','artifact-clean-wip-nosimp','cvc5-1.3.3-gb','cvc5-1.3.3-nosimp','cvc5-1.3.3-split','cvc5-1.4.0-gb','cvc5-1.4.0-nosimp','cvc5-1.4.0-split','cvc5-main-72f647e-gb','cvc5-main-72f647e-split','paper-candidate-gb','paper-candidate-nosimp','paper-candidate-proof','z3-ff-solve','z3-ff-proof']
    labels=['Artifact\nGB','Artifact\nno simp.','1.3.3\nGB','1.3.3\nno simp.','1.3.3\nsplit','1.4.0\nGB','1.4.0\nno simp.','1.4.0\nsplit','main\nGB','main\nsplit','Candidate\nGB','Candidate\nno simp.','Candidate\nchecked','Z3+FF\nsolver','Z3+FF\nchecked']
    cats=sorted(summary[cols[0]]['categories']);ratios=np.array([[summary[c]['categories'][k]['successful']/summary[c]['categories'][k]['total'] for c in cols] for k in cats])
    fig,ax=plt.subplots(figsize=(18,5.5));im=ax.imshow(ratios,vmin=0,vmax=1,cmap='RdYlGn',aspect='auto')
    ax.set_xticks(range(len(cols)),labels);ax.set_yticks(range(len(cats)),cats)
    for i,k in enumerate(cats):
        for j,c in enumerate(cols):
            r=summary[c]['categories'][k];ax.text(j,i,f"{r['successful']}/{r['total']}",ha='center',va='center',fontsize=10,color='black')
    ax.set_title('Coverage by compiler and property — answers and checked proofs labelled separately',pad=16)
    fig.colorbar(im,ax=ax,label='Completion fraction',shrink=.85);fig.tight_layout();fig.savefig(out/'categories.png',dpi=180);plt.close(fig)
    fig,ax=plt.subplots(figsize=(6,6))
    for h in common:ax.scatter(by[proof_names[0]][h]['seconds'],by[proof_names[1]][h]['seconds'],s=14,alpha=.55,color='#167f8c')
    ax.plot([.01,meta['timeout']],[.01,meta['timeout']],ls='--',color='gray');ax.set(xscale='log',yscale='log',xlim=(.01,meta['timeout']),ylim=(.01,meta['timeout']),xlabel='Paper candidate + proof + check (s)',ylabel='Z3+FF + proof + check (s)',title=f'Common externally checked inputs: {len(common)}')
    ax.grid(alpha=.2);fig.tight_layout();fig.savefig(out/'proof-scatter.png',dpi=180);plt.close(fig)
    print('\n'.join(md));print('Common proof inputs',len(common),'candidate-only',len(conly),'Z3-only',len(zonly))


if __name__=='__main__':main()
