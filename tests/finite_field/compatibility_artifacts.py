#!/usr/bin/env python3
"""Untimed diagnostic of cvc5-specific :incremental options in seven examples.

Primary results retain these parser errors. This separate run removes only the
option, explicitly enables incremental mode on cvc5's CLI, and checks the full
answer sequence without changing any assertions.
"""
import argparse
import json
import re
from pathlib import Path
from artifact_analysis import LABELS, load
from benchmark_artifacts import prepare, run


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results',type=Path,required=True)
    ap.add_argument('--corpus',type=Path,required=True)
    args=ap.parse_args()
    _, members, _=load(args.results)
    rows=[]
    for h, es in sorted(members.items()):
        original=(args.corpus/'inputs'/(h+'.smt2')).read_text()
        if '(set-option :incremental true)' not in original:continue
        smt=re.sub(r'\(set-option\s+:incremental\s+true\s*\)','',prepare(original))
        for label in LABELS:
            if label=='z3':cmd=[str((args.results/'binaries/z3').resolve()),'-in']
            else:
                cmd=[str((args.results/'binaries/cvc5').resolve()),'--lang=smt2','--incremental']
                if label=='cvc5_split':cmd.append('--ff-solver=split')
            r=run(dict(command=cmd,smt=smt,checks=es[0]['checks'],timeout=10,memory_mib=4096))
            r.update(sha256=h,solver=label,adaptation='remove :incremental true; enable --incremental on cvc5 CLI')
            rows.append(r)
    (args.results/'compatibility.json').write_text(json.dumps(rows,indent=2)+'\n')
    print('diagnostic runs',len(rows),'results',[(r['solver'],r['answers'],r['result']) for r in rows])


if __name__=='__main__':main()
