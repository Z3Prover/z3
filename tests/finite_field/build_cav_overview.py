#!/usr/bin/env python3
"""Rebuild the CAV figures/tables from frozen solver measurements."""
import argparse,collections,csv,hashlib,html,json,math,statistics,sys
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
from artifact_analysis import load,family,SOLVED
from cav_data import current_rows
ROOT=Path(__file__).resolve().parents[2]
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--comparison',type=Path,help='Complete fresh three-solver campaign; omit for corrected historical comparison')
ap.add_argument('--out',type=Path,default=ROOT/'output/pdf/z3-qfff-cav')
args=ap.parse_args();DATA=args.comparison or ROOT/'tests/finite_field/results/cav-overview';OUT=args.out;OUT.mkdir(parents=True,exist_ok=True)
manifest,members,refs=load(args.comparison or ROOT/'tests/finite_field/results/paper-artifacts')
current={h:rr['z3'] for h,rr in refs.items()} if args.comparison else current_rows()
if args.comparison:
 meta=json.loads((DATA/'metadata.json').read_text());provenance=json.loads((DATA/'build-provenance.json').read_text());version='cvc5 main '+provenance['revision'][:12];reference_note=meta['binaries']['cvc5']['version']+' (fresh interleaved GB/split, adjudicated)'
else:
 version='cvc5 1.3.4 (historical)';reference_note='1.3.4 historical GB/split, adjudicated'
assert set(current)==set(members),(len(current),len(members))
LABELS=['cvc5','cvc5_split','z3'];TITLES=['cvc5 GB','cvc5 split','Z3+FF'];COLORS=['#7661a6','#e28d26','#087f8c']
rows={h:{'z3':current[h],'cvc5':refs[h]['cvc5'],'cvc5_split':refs[h]['cvc5_split']} for h in members}
conflicts=[]
for h,rr in rows.items():
 if len({tuple(r['answers']) for r in rr.values() if r['result'] in SOLVED})>1:conflicts.append(h)
assert not conflicts,conflicts
sol=lambda x:x['result'] in SOLVED

def stats(hashes):
 d={'n':len(hashes)}
 for label in LABELS:
  rr=[rows[h][label] for h in hashes];d[label]={'solved':sum(map(sol,rr)),'counts':dict(collections.Counter(r['result'] for r in rr)),'par2':statistics.mean(r['seconds'] if sol(r) else 20 for r in rr)}
 d['reference_only']=sum(not sol(rows[h]['z3']) and any(sol(rows[h][k]) for k in LABELS[:2]) for h in hashes)
 d['z3_only']=sum(sol(rows[h]['z3']) and not any(sol(rows[h][k]) for k in LABELS[:2]) for h in hashes)
 d['neither']=sum(not any(sol(r) for r in rows[h].values()) for h in hashes)
 return d
families=collections.defaultdict(list)
for h in members:families[family(members[h])].append(h)
order=['TV','TV-pureFF','CirC-D','CirC-S','QED2','Seq','Small','ASHR','Examples']
summary={'n':len(rows),'families':{f:stats(families[f]) for f in order},'total':stats(list(rows)),'conflicts':conflicts,'versions':{'z3':'round7 retained: 14772994298957b7b5c9d402b7e830b6b542e48077fcf20d46845aeeb83f249e','cvc5':reference_note},'papers':{p:stats([h for h,es in members.items() if any(e['paper']==p for e in es)]) for p in manifest['sources']}}
summary['field_sizes']={name:stats([h for h,es in members.items() if lo<=max(es[0]['field_bits'])<=hi]) for name,lo,hi in [('small (<=16 bits)',0,16),('medium (17-127 bits)',17,127),('large (>=128 bits)',128,1000000)]}
(DATA/'summary.json').write_text(json.dumps(summary,indent=2))
# Keep complete per-input identity and failure status; a timeout is never a solve.
flat=[]
for h in sorted(rows):
 for k in LABELS:
  x=rows[h][k];flat.append(dict(case=h,family=family(members[h]),name=members[h][0]['member'],solver=k,result=x['result'],seconds=x['seconds'],peak_rss_mib=x['peak_rss_mib'],source=x.get('measurement_source','fresh-interleaved' if args.comparison else 'historical-paper-artifacts')))
# Real-project queries are a separate row/panel, never folded into paper totals.
real={};real_hashes={}
for name in ['circom-10s','pure-10s']:
 for m in json.loads((ROOT/'tests/finite_field/results/real-circuits'/name/'manifest.json').read_text()):real_hashes[m['case']]=m['input_sha256']
 for line in (ROOT/'tests/finite_field/results/real-circuits'/name/'runs.jsonl').read_text().splitlines():
  x=json.loads(line)
  if x['solver'] in LABELS[:2]:real.setdefault(x['case'],{})[x['solver']]=x
for line in (ROOT/'tests/finite_field/results/performance-round7/prior-final/runs.jsonl').read_text().splitlines():
 x=json.loads(line)
 if x['family']=='Real' and x['variant']=='candidate':
  assert x['source_sha256']==real_hashes[x['case']];real[x['case']]['z3']=x
assert len(real)==8 and all(len(v)==3 for v in real.values())
if args.comparison:
 real={}
 for group in ['circom','pure']:
  for item in json.loads((DATA/('real-'+group)/'manifest.json').read_text()):assert item['input_sha256']==real_hashes[item['case']]
  for line in (DATA/('real-'+group)/'runs.jsonl').read_text().splitlines():
   x=json.loads(line);assert x['solver'] not in real.get(x['case'],{});real.setdefault(x['case'],{})[x['solver']]=x
 assert len(real)==8 and all(len(v)==3 for v in real.values())
for h,rr in real.items():
 for k,x in rr.items():flat.append(dict(case=h,family='Real (separate)',name=h,solver=k,result=x['result'],seconds=x['seconds'],peak_rss_mib=x['peak_rss_mib'],source='fresh-real-circuits' if args.comparison else 'round7' if k=='z3' else 'historical-real-circuits'))
with (OUT/'benchmark-results.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(flat[0]));w.writeheader();w.writerows(flat)
with (OUT/'category-results.csv').open('w') as f:
 w=csv.writer(f);w.writerow(['category','inputs',*TITLES,'cvc5_union_only','Z3_only','none_solve',*[t+' PAR2 seconds' for t in TITLES]])
 for name,d in summary['families'].items():w.writerow([name,d['n'],*[d[k]['solved'] for k in LABELS],d['reference_only'],d['z3_only'],d['neither'],*[d[k]['par2'] for k in LABELS]])
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42,'ps.fonttype':42})
# Category view: coverage and missed cases remain separate; unions are not a solver.
def category_figure(include_real=False):
 names=order+(['Real projects*'] if include_real else []);dd=[summary['families'][f] for f in order]
 if include_real:
  d={'n':8,**{k:{'solved':sum(sol(rr[k]) for rr in real.values())} for k in LABELS},'reference_only':0,'neither':sum(not any(sol(r) for r in rr.values()) for rr in real.values())};dd.append(d)
 fig,(a,b)=plt.subplots(1,2,figsize=(8.5,5.7) if include_real else (6.6,4.2),gridspec_kw={'width_ratios':[3,2.35]},layout='constrained')
 ar=np.array([[d[k]['solved']/d['n'] for k in LABELS] for d in dd]);a.imshow(ar,vmin=0,vmax=1,cmap='YlGnBu',aspect='auto')
 for i,d in enumerate(dd):
  for j,k in enumerate(LABELS):a.text(j,i,f"{d[k]['solved']}/{d['n']}\n{100*ar[i,j]:.0f}%",ha='center',va='center',fontsize=9.3 if not include_real else 9,linespacing=1.0,color='white' if ar[i,j]>.60 else '#16232e')
 a.set_xticks(range(3),TITLES);a.xaxis.tick_top();a.tick_params(length=0);a.set_yticks(range(len(dd)),names);a.set_title('Coverage at 10 seconds',pad=31,fontweight='bold',fontsize=12)
 for s in a.spines.values():s.set_visible(False)
 a.set_xticks(np.arange(-.5,3,1),minor=True);a.set_yticks(np.arange(-.5,len(dd),1),minor=True);a.grid(which='minor',color='white',linewidth=2);a.tick_params(which='minor',length=0)
 yy=np.arange(len(dd));miss=[d['reference_only'] for d in dd];neither=[d['neither'] for d in dd]
 b.barh(yy,miss,color='#c74732',label='cvc5 GB or split solves');b.barh(yy,neither,left=miss,color='#d5dadd',label='No solver solves')
 for i,(m,n) in enumerate(zip(miss,neither)):
  b.text(m+n+max(1,max(x+y for x,y in zip(miss,neither))*.018),i,f'{m} / {m+n}',va='center',fontsize=10)
 b.set_ylim(len(dd)-.5,-.5);b.set_yticks(yy,[]);b.tick_params(axis='y',length=0);b.set_xlim(0,max(10,max(x+y for x,y in zip(miss,neither)))*1.38);b.set_xlabel('Number of inputs');b.set_title('Where Z3+FF misses',fontweight='bold',fontsize=12,pad=31);b.grid(axis='x',alpha=.17);b.set_axisbelow(True)
 if include_real:b.legend(loc='lower center',bbox_to_anchor=(.43,-.24),frameon=False,fontsize=8)
 else:fig.legend(*b.get_legend_handles_labels(),loc='outside lower center',ncol=2,frameon=False,fontsize=9)
 for s in ['left','right','top']:b.spines[s].set_visible(False)
 if include_real:fig.suptitle('Finite-field benchmark overview · 4,212 paper inputs + 8 real-project queries',fontsize=12,fontweight='bold');fig.supxlabel(version+' vs current Z3+FF · labels at right: cvc5-only / all Z3 misses\n*Real projects form a separate diagnostic set; not included in paper-corpus totals.',fontsize=8)
 return fig
f=category_figure();f.savefig(OUT/'category-coverage.pdf');plt.close(f)
f=category_figure(True)
for ext in ['pdf','svg','png']:f.savefig(OUT/('benchmark-overview.'+ext),dpi=200)
plt.close(f)
# Classic aggregate timing view, complete common corpus, failed runs excluded from cactus.
f,(a,b)=plt.subplots(1,2,figsize=(6.6,2.8),layout='constrained')
for k,title,c in zip(LABELS,TITLES,COLORS):
 ts=sorted(r[k]['seconds'] for r in rows.values() if sol(r[k]));a.plot(range(1,len(ts)+1),ts,label=f'{title} ({len(ts)})',color=c,lw=1.5)
 ratios=sorted(r[k]['seconds']/min(v['seconds'] for v in r.values() if sol(v)) for r in rows.values() if sol(r[k]));b.step(ratios,np.arange(1,len(ratios)+1)/len(rows),where='post',label=title,color=c,lw=1.5)
a.set_yscale('log');a.set_ylim(.003,12);a.set_xlabel('Inputs solved');a.set_ylabel('Seconds');a.legend(fontsize=8,frameon=False);a.grid(alpha=.2);a.set_title('Cactus')
b.set_xscale('log');b.set_xlim(1,1000);b.set_ylim(0,1);b.set_xlabel('Factor of fastest success');b.set_ylabel('Fraction of all 4,212 inputs');b.grid(alpha=.2);b.set_title('Performance profile')
f.savefig(OUT/'runtime-overview.pdf');plt.close(f)
# Every primary benchmark as a status tile, grouped by family and sorted by outcome pattern.
status=['sat','unsat','multi','timeout','memout','unknown','error','wrong'];palette=['#46a5a0','#155f72','#4c78a8','#edbd5e','#c74732','#ad8fbb','#949ba1','#151515']
from matplotlib.colors import ListedColormap
from matplotlib.patches import Patch
f,aa=plt.subplots(3,3,figsize=(12,7.5),layout='constrained')
for ax,name in zip(aa.flat,order):
 hs=sorted(families[name],key=lambda h:(tuple(rows[h][k]['result'] for k in LABELS),h));ar=np.array([[status.index(rows[h][k]['result']) for h in hs] for k in LABELS]);ax.imshow(ar,cmap=ListedColormap(palette),vmin=-.5,vmax=7.5,aspect='auto',interpolation='nearest');ax.set_title(f'{name} (n={len(hs)})',fontsize=11);ax.set_yticks(range(3),TITLES,fontsize=8);ax.set_xticks([])
f.legend(handles=[Patch(color=c,label=s) for c,s in zip(palette,status)],loc='outside lower center',ncol=8,frameon=False,fontsize=9);f.suptitle('Every paper benchmark · grouped by category, ordered by outcome pattern',fontsize=14)
f.savefig(OUT/'all-input-statuses.pdf');f.savefig(OUT/'all-input-statuses.png',dpi=200);plt.close(f)
# A vertical status map remains legible at LNCS text width.
f,aa=plt.subplots(9,1,figsize=(5.6,7.4),layout='constrained')
for ax,name in zip(aa,order):
 hs=sorted(families[name],key=lambda h:(tuple(rows[h][k]['result'] for k in LABELS),h));ar=np.array([[status.index(rows[h][k]['result']) for h in hs] for k in LABELS]);ax.imshow(ar,cmap=ListedColormap(palette),vmin=-.5,vmax=7.5,aspect='auto',interpolation='nearest');ax.set_title(f'{name} (n={len(hs)})',fontsize=9,pad=2);ax.set_yticks(range(3),TITLES,fontsize=8);ax.set_xticks([])
f.legend(handles=[Patch(color=c,label=s) for c,s in zip(palette,status)],loc='outside lower center',ncol=4,frameon=False,fontsize=8)
f.savefig(OUT/'all-input-statuses-paper.pdf');plt.close(f)
# Numeric LaTeX output: no hand-copied aggregate values.
tex=[]
def cmd(n,v):tex.append('\\newcommand{\\'+n+'}{'+str(v)+'}')
total=summary['total'];cmd('CorpusN',len(rows));cmd('ZthreeSolved',total['z3']['solved']);cmd('CvcSolved',total['cvc5']['solved']);cmd('SplitSolved',total['cvc5_split']['solved']);cmd('ReferenceOnly',total['reference_only']);cmd('ZthreeOnly',total['z3_only']);cmd('NeitherSolved',total['neither'])
for name,label in [('RealZthreeSolved','z3'),('RealCvcSolved','cvc5'),('RealSplitSolved','cvc5_split')]:cmd(name,sum(sol(rr[label]) for rr in real.values()))
cmd('FamilyRows','\n'.join(f"{name} & {d['n']} & {d['cvc5']['solved']} & {d['cvc5_split']['solved']} & {d['z3']['solved']} & {d['reference_only']} \\\\" for name,d in summary['families'].items()))
cmd('FailureRows','\n'.join(f"{title} & {total[k]['solved']} & {total[k]['counts'].get('timeout',0)} & {total[k]['counts'].get('memout',0)} & {sum(v for s,v in total[k]['counts'].items() if s not in SOLVED and s not in ['timeout','memout','wrong'])} & {total[k]['counts'].get('wrong',0)} & {total[k]['par2']:.2f} \\\\" for k,title in zip(LABELS,TITLES)))
cmd('PaperRows','\n'.join(f"{name} & {d['n']} & {d['cvc5']['solved']} & {d['cvc5_split']['solved']} & {d['z3']['solved']} \\\\" for name,d in summary['papers'].items()))
def size_label(name):return name.replace('<=',r'$\leq$').replace('>=',r'$\geq$')
cmd('SizeRows','\n'.join(f"{size_label(name)} & {d['n']} & {d['cvc5']['solved']} & {d['cvc5_split']['solved']} & {d['z3']['solved']} \\\\" for name,d in summary['field_sizes'].items()))
cmd('RealRows','\n'.join(html.escape(h).replace('_',r'\_')+' & '+' & '.join(f"{rr[k]['seconds']:.2f}" if sol(rr[k]) else 'M' if rr[k]['result']=='memout' else 'T' if rr[k]['result']=='timeout' else rr[k]['result'] for k in LABELS)+r' \\' for h,rr in sorted(real.items())))
(OUT/'numbers.tex').write_text('\n'.join(tex)+'\n')
# Self-contained, filterable per-input viewer. Text is escaped on insertion.
cases=[]
for h,rr in rows.items():cases.append(dict(id=h,family=family(members[h]),name=members[h][0]['member'],gap=not sol(rr['z3']) and any(sol(rr[k]) for k in LABELS[:2]),results={k:{'result':x['result'],'seconds':x['seconds']} for k,x in rr.items()}))
for h,rr in real.items():cases.append(dict(id=h,family='Real (separate)',name=h,gap=False,results={k:{'result':x['result'],'seconds':x['seconds']} for k,x in rr.items()}))
payload=json.dumps(cases).replace('<','\\u003c')
page='''<!doctype html><meta charset="utf-8"><title>Finite-field benchmark explorer</title><style>body{font:15px system-ui;margin:32px;color:#17252a}h1{margin-bottom:8px}p{max-width:1000px;color:#53636a}input,select{padding:8px;margin:8px}table{border-collapse:collapse;width:100%}th,td{padding:9px;text-align:left;border-bottom:1px solid #ddd}th{position:sticky;top:0;background:#e9f0f1}td:first-child{max-width:590px;overflow-wrap:anywhere}.miss{background:#ffebe5}.ok{color:#087f8c}.bad{color:#b63b28}small{color:#6b7278}button{padding:8px}</style><h1>QF_FF benchmark explorer</h1><p>All 4,212 paper inputs plus 8 separate real-project queries. cvc5 GB/split: historical 1.3.4 results with adjudication; Z3+FF: retained round-7 binary. Limits: 10 seconds, sampled 4 GiB. Red rows are cases cvc5 solves but Z3+FF does not. Times are wall-clock measurements, not controlled pairwise speedups.</p><label>Category <select id="family"><option value="">All</option></select></label><input id="q" placeholder="Search name or hash"><label><input id="gaps" type="checkbox">Only cvc5-only gaps</label><button id="prev">Previous 100</button><button id="next">Next 100</button><p id="count"></p><table><thead><tr><th>Benchmark</th><th>Category</th><th>cvc5 GB</th><th>cvc5 split</th><th>Z3+FF</th></tr></thead><tbody id="body"></tbody></table><script>const data=PAYLOAD;let offset=0;const $=id=>document.getElementById(id);for(const f of [...new Set(data.map(x=>x.family))].sort()){$('family').add(new Option(f,f))}function cell(tr,text,cls){const td=document.createElement('td');td.textContent=text;if(cls)td.className=cls;tr.append(td)}function render(){const q=$('q').value.toLowerCase();const found=data.filter(x=>(!$('family').value||x.family===$('family').value)&&(!$('gaps').checked||x.gap)&&(!q||(x.name+' '+x.id).toLowerCase().includes(q)));offset=Math.min(offset,Math.max(0,Math.floor((found.length-1)/100)*100));$('body').replaceChildren();for(const x of found.slice(offset,offset+100)){const tr=document.createElement('tr');if(x.gap)tr.className='miss';cell(tr,x.name);tr.firstChild.title=x.id;cell(tr,x.family);for(const k of ['cvc5','cvc5_split','z3']){const r=x.results[k];cell(tr,r.result+' · '+r.seconds.toFixed(3)+' s',['sat','unsat','multi'].includes(r.result)?'ok':'bad')}$('body').append(tr)}$('count').textContent=`${found.length} matching inputs · showing ${found.length?offset+1:0}–${Math.min(offset+100,found.length)}`;$('prev').disabled=offset===0;$('next').disabled=offset+100>=found.length}for(const id of ['q','family','gaps'])$(id).addEventListener('input',()=>{offset=0;render()});$('prev').onclick=()=>{offset=Math.max(0,offset-100);render()};$('next').onclick=()=>{offset+=100;render()};render();</script>'''
if args.comparison:page=page.replace('historical 1.3.4 results with adjudication',html.escape(version)+'; fresh interleaved results with adjudication')
(OUT/'benchmark-explorer.html').write_text(page.replace('PAYLOAD',payload))
print(json.dumps(summary,indent=2))
