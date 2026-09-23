#!/usr/bin/env python3
"""Separate field parsing/validation from solving within one Z3 process.

Use the Python bindings and library from the build under test. First and second
parses share a context so the latter reuses its validated field modulus. This is
not a claim of incremental algebra reuse. The independent CLI harness measures
fresh-process wall time and peak RSS.
"""
import argparse
import json
import time
from pathlib import Path
from z3 import Context, SolverFor, Tactic, Then, OrElse, sat
from zk_circuits import cases


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,default=Path('tests/finite_field/results/zk-phases.json'))
    ap.add_argument('--timeout',type=int,default=3000)
    args=ap.parse_args();rows=[]
    chosen=['bn254_poseidon_16_fixed_sat','bn254_poseidon_1_free','bn254_range_253_value',
            'bls12_381_scalar_poseidon_16_fixed_sat','bls12_381_scalar_edwards_64_fixed_sat']
    for name,circuit,expected in cases(large=True):
        if name not in chosen:continue
        text=circuit.smt()
        for preprocess in [False,True]:
            ctx=Context()
            for cached in [False,True]:
                if preprocess:
                    algebra=OrElse(Tactic('ff-solve',ctx),Tactic('ff-sat',ctx),Then(Tactic('ff2bv',ctx),Tactic('qfbv',ctx)))
                    solver=Then(Tactic('ff-simplify',ctx),algebra).solver()
                else:solver=SolverFor('QF_FF',ctx)
                solver.set(timeout=args.timeout)
                start=time.perf_counter();solver.from_string(text);parse=time.perf_counter()-start
                start=time.perf_counter();result=solver.check();solve=time.perf_counter()-start
                stats=solver.statistics()
                row=dict(case=name,preprocess=preprocess,modulus_cached=cached,result=str(result),
                         parse_seconds=parse,check_seconds=solve,
                         statistics={key:stats.get_key_value(key) for key in stats.keys() if key.startswith('ff ')})
                if result==sat:
                    model=solver.model()
                    # Evaluate all original assertions, including pins.
                    assert all(str(model.eval(assertion,model_completion=True))=='True' for assertion in solver.assertions())
                rows.append(row);print(json.dumps(row),flush=True)
    args.out.write_text(json.dumps(rows,indent=2)+'\n')


if __name__=='__main__':main()
