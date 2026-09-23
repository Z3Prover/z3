#!/usr/bin/env python3
"""Populate paper analysis paragraphs from the checked complete comparison."""
import argparse,collections,json
from cav_data import current_rows
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--comparison',type=Path)
ap.add_argument('--out',type=Path,default=ROOT/'output/pdf/z3-qfff-cav')
args=ap.parse_args();DATA=args.comparison or ROOT/'tests/finite_field/results/cav-overview';OUT=args.out
s=json.loads((DATA/'summary.json').read_text());f=s['families'];t=s['total']
worst=sorted(f.items(),key=lambda x:x[1]['reference_only'],reverse=True)[:3]
text='The largest numbers of cvc5-only successes occur in '+', '.join(name+' ('+str(d['reference_only'])+')' for name,d in worst)+'. These are direct candidates for further investigation; an aggregate family win cannot eliminate complementary failures. '
text+='Across the full corpus, '+str(t['neither'])+' inputs remain unresolved by every configuration. Their distribution separates common hard cases from weaknesses specific to this implementation.\n\n'
text+='The bit-sum and arithmetic-shift families illustrate the effect of the integration and subsequent preprocessing work: Z3+FF solves '+str(f['Seq']['z3']['solved'])+'/100 Seq inputs and '+str(f['ASHR']['z3']['solved'])+'/32 ASHR inputs, versus '+str(f['Seq']['cvc5_split']['solved'])+'/100 and '+str(f['ASHR']['cvc5_split']['solved'])+'/32 for split. The Small and mixed CirC-S categories retain distinct algebraic and search challenges; Figure~\\ref{fig:categories} reports them separately rather than attributing all failures to large moduli.\n\n'
text+='Failures also need an interface/resource distinction. The '+('fresh' if args.comparison else 'corrected')+' Z3 pass records '+str(t['z3']['counts'].get('timeout',0))+' timeouts, '+str(t['z3']['counts'].get('memout',0))+' memory-limit failures, and '+str(t['z3']['counts'].get('error',0))+' errors. '
text+=('The adapter removes the unsupported incremental-enabling option from seven Examples inputs, preserving every assertion and incremental command. ' if args.comparison else 'Seven Examples inputs were rerun after removing the unsupported incremental-enabling option; six interface errors become successes, while the cyclic five-variable system still times out. Original logs are preserved. ')
text+='A short sampled memory limit does not establish low memory use or eliminate basis-growth bottlenecks.\n'
(OUT/'findings.tex').write_text(text)
models=[json.loads(l) for l in (DATA/'models.jsonl').read_text().splitlines()];counts=collections.Counter(x['validation'] for x in models)
assert counts.get('failed',0)==0
rows=[json.loads(l) for l in (DATA/'runs.jsonl').read_text().splitlines()] if args.comparison else list(current_rows().values())
assert len(models)==sum(x['result']=='sat' for x in rows)
if args.comparison:
 by_solver=collections.Counter(x['solver'] for x in models)
 text=f"All {len(models):,} single-query SAT results in the fresh comparison pass independent original-assertion evaluation: {by_solver['z3']:,} Z3, {by_solver['cvc5']:,} cvc5 GB, and {by_solver['cvc5_split']:,} split results. Validation is untimed; matching Z3 witnesses are reused only for the identical binary and input. These are validation runs, not extra benchmark inputs. Earlier paired studies and Poseidon regression populations overlap and are reported separately. No independent UNSAT certificate is produced.\n"
else:
 text=f"All {len(models):,} current single-query SAT results in the complete paper corpus pass independent evaluation of every original assertion. This total includes exact prior validation records and new untimed model replays; it is not an extra set of benchmark inputs. The preceding paired study validated 473 SAT model runs across both binaries, and the 12 current Poseidon sentinels contributed 16 valid SAT model runs. These populations overlap and are reported separately. No independent UNSAT certificate is produced.\n"
(OUT/'validation.tex').write_text(text)
print('Generated findings and validation:',len(models),'models')
