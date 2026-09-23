#!/usr/bin/env python3
"""Resolve SAT/UNSAT disagreements only with independently checked SAT witnesses.

A checked model proves satisfiability and refutes any UNSAT answer. Majority
vote is never used. Unresolved disagreements remain visible and block the report.
"""
import argparse
import collections
import json
from pathlib import Path
from benchmark_public_ff import sexprs
from benchmark_artifacts import prepare, run
from validate_artifact_models import validate


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results',type=Path,required=True)
    ap.add_argument('--corpus',type=Path,required=True)
    args=ap.parse_args()
    results=collections.defaultdict(dict)
    for line in (args.results/'runs.jsonl').read_text().splitlines():
        r=json.loads(line);results[r['sha256']][r['solver']]=r
    file=args.results/'adjudications.json'
    adjudications=json.loads(file.read_text()) if file.exists() else {}
    for h, answers in results.items():
        if h in adjudications:continue
        if {r['result'] for r in answers.values()} & {'sat','unsat'} != {'sat','unsat'}:continue
        original=(args.corpus/'inputs'/(h+'.smt2')).read_text()
        cmds=sexprs(original)
        assert sum(c[0]=='check-sat' for c in cmds)==1
        names=[c[1] for c in cmds if c[0]=='declare-const' or (c[0]=='declare-fun' and c[2]==[])]
        query='(set-option :produce-models true)\n'+prepare(original)+'\n(get-value ('+' '.join(names)+'))\n'
        evidence=[];directory=args.results/'disagreements'/h;directory.mkdir(parents=True,exist_ok=True)
        (directory/'original.smt2').write_text(original)
        for label, r in answers.items():
            if r['result']!='sat':continue
            if label=='z3':command=[str((args.results/'binaries/z3').resolve()),'-in']
            else:
                command=[str((args.results/'binaries/cvc5').resolve()),'--lang=smt2']
                if label=='cvc5_split':command.append('--ff-solver=split')
            model=run(dict(command=command,smt=query,checks=1,timeout=30,output_limit=None))
            if model['result']!='sat':continue
            count=validate(original,model['stdout'])
            (directory/(label+'-model.json')).write_text(json.dumps(model,indent=2)+'\n')
            evidence.append(dict(solver=label,assertions_checked=count,model_file=str((directory/(label+'-model.json')).relative_to(args.results))))
        if not evidence:
            print('UNRESOLVED',h,flush=True);continue
        adjudications[h]=dict(expected='sat',basis='independent evaluation of every original assertion under complete SAT assignments',
                             wrong_solvers=[label for label,r in answers.items() if r['result']=='unsat'],evidence=evidence)
        file.write_text(json.dumps(adjudications,indent=2)+'\n')
        print('Confirmed',h,adjudications[h]['wrong_solvers'],'wrong UNSAT; models checked',len(evidence),flush=True)
    if not file.exists():file.write_text('{}\n')


if __name__=='__main__':main()
