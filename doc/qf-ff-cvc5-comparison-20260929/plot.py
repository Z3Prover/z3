"""Reproduce the completed matched-sample figures from adjacent JSON files."""
import json,collections
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
R=Path(__file__).resolve().parent
rows=list(map(json.loads,(R/'measurements.jsonl').read_text().splitlines()));meta=json.loads((R/'metadata.json').read_text());labels=meta['labels'];cases=json.loads((R/'sample.json').read_text())['cases'];by={(r['sha256'],r['configuration']):r for r in rows}
answers=collections.defaultdict(set)
for r in rows:
 if r['status'] in ['sat','unsat']:answers[r['sha256']].add(r['status'])
disputed={h for h,a in answers.items() if len(a)>1}
def good(r):return r['status'] in ['sat','unsat','multi'] and r['sha256'] not in disputed
solved={c:{h for h in cases if good(by[h,c])} for c in labels}
plt.rcParams.update({'font.size':11})
fig,ax=plt.subplots(figsize=(10,5.8))
for c,label in labels.items():
 xs=sorted(by[h,c]['seconds'] for h in solved[c]);ax.step(xs,range(1,len(xs)+1),where='post',label=f'{label} ({len(xs)})',linewidth=2.4 if c=='z3-pr1' else 1.6)
ax.set(xscale='log',xlim=(.008,10),ylim=(0,195),xlabel='Solver wall time (s)',ylabel='Distinct inputs solved',title='Ordinary solving · completed 190-input balanced sample')
ax.grid(alpha=.22);ax.legend(loc='upper left',fontsize=9.5);fig.text(.5,.015,'10 s/run · 4 workers · SAT/UNSAT answers, not certificates · known wrong/disputed answers excluded',ha='center',fontsize=9);fig.tight_layout(rect=(0,.035,1,1))
for ext in ['png','pdf']:fig.savefig(R/f'solving-cactus.{ext}',dpi=180)
plt.close(fig)
families=sorted({e['family'] for e in cases.values()});fig,(ax,bx)=plt.subplots(2,1,figsize=(12,11.2),gridspec_kw={'height_ratios':[1.6,1]})
short=['Z3+FF\nPR1','1.3.3\nno simp.','1.4.0\nGB','1.4.0\nsplit','main 72f647e\nGB','main 72f647e\nsplit','1.3.4.dev\nFMCAD']
m=[]
for f in families:
 hs={h for h,e in cases.items() if e['family']==f};m.append([len(hs&solved[c])/len(hs) for c in labels])
im=ax.imshow(m,vmin=0,vmax=1,cmap='YlGnBu',aspect='auto');ax.set_xticks(range(len(labels)),short);ax.set_yticks(range(len(families)),families);ax.set_title('Coverage by family · the same 190 inputs in every column',pad=15)
for i,f in enumerate(families):
 hs={h for h,e in cases.items() if e['family']==f}
 for j,c in enumerate(labels):ax.text(j,i,f'{len(hs&solved[c])}/{len(hs)}',ha='center',va='center',color='white' if m[i][j]>.65 else 'black',fontsize=10)
fig.colorbar(im,ax=ax,fraction=.026,pad=.02,label='Fraction solved')
competitors=list(labels)[1:];z=solved['z3-pr1'];coverage={c:[len(z&solved[c]),len(z-solved[c]),len(solved[c]-z),len(set(cases)-(z|solved[c]))] for c in competitors};left=np.zeros(len(competitors))
for i,(label,color) in enumerate([('Both','#517da8'),('Z3+FF only','#39a778'),('cvc5 only','#eb9a4b'),('Neither','#d6dadd')]):
 vals=[coverage[c][i] for c in competitors];bx.barh(range(len(competitors)),vals,left=left,label=label,color=color)
 for j,v in enumerate(vals):
  if v:bx.text(left[j]+v/2,j,str(v),ha='center',va='center',fontsize=10)
 left+=vals
bx.set_yticks(range(len(competitors)),[labels[c].replace('cvc5 ','') for c in competitors]);bx.invert_yaxis();bx.set_xlim(0,190);bx.set_xlabel('Distinct inputs');bx.set_title('Which inputs does Z3+FF solve compared with each cvc5 configuration?',pad=12);bx.legend(ncol=4,loc='upper center',bbox_to_anchor=(.5,-.18),fontsize=10)
fig.suptitle('Z3+FF PR1 vs cvc5 versions · matched sample, 10 s/run',fontsize=15);fig.tight_layout(rect=(0,.03,1,.97),h_pad=3)
for ext in ['png','pdf']:fig.savefig(R/f'coverage.{ext}',dpi=180)
summary=dict(inputs=len(cases),solved={c:len(hs) for c,hs in solved.items()},disputed=sorted(disputed),pairwise={c:dict(zip(['both','z3_only','cvc5_only','neither'],v)) for c,v in coverage.items()});(R/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
