"""Reproduce local Dafny model checks; never execute the inspected C++ source.

Each check retains its exact input, command, output, exit code and model hash.
This is a manual NFV-methodology audit runner, not the upstream NFV driver.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time


def signature(model, entry):
    match = re.search(r'^method ' + re.escape(entry) + r'\(', model, re.M)
    assert match, entry
    end = model.index('\n{', match.start())
    return match.start(), end


def change_goals(model, entry, goals, pins=()):
    first, last = signature(model, entry)
    rows = model[first:last].splitlines()
    kept = []
    for row in rows:
        if re.match(r'^\s*ensures ', row):
            assert kept[-1].startswith('// synth:'), row
            kept.pop()
        else:
            kept.append(row)
    assert kept[-1].startswith('// synth:')
    brace_tag = kept.pop()
    for pin in pins:
        kept.extend(['// synth: concrete witness pin added independently of original applicability', '  requires ' + pin])
    for goal in goals:
        kept.extend(['// synth: mechanically selected complete property goal', '  ensures ' + goal])
    kept.append(brace_tag)
    return model[:first] + '\n'.join(kept) + model[last:]


def literal(value):
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, int):
        return '(' + str(value) + ')' if value < 0 else str(value)
    assert isinstance(value, list), value
    return '[' + ', '.join(literal(v) for v in value) + ']'


def domain_drivers(model, prop, examples):
    first, last = signature(model, prop['entry_point'])
    match = re.search(r'^method \w+\(([^()]*)\) returns \(([^()]*)\)', model[first:last])
    assert match, prop['id']
    inputs = [p.split(':',1)[0].strip() for p in match[1].split(',') if p.strip()]
    outputs = [p.split(':',1)[0].strip() for p in match[2].split(',') if p.strip()]
    drivers = []
    for index, witness in enumerate(examples):
        assert set(witness) == set(inputs), (prop['id'], witness)
        call = prop['entry_point'] + '(' + ', '.join(literal(witness[p]) for p in inputs) + ')'
        names = ', '.join('out'+str(i) for i in range(len(outputs)))
        drivers.append(f'method NfvDomain{index}()\n{{\n  var {names} := {call};\n}}\n')
    return '\n'.join(drivers)


parser = argparse.ArgumentParser()
parser.add_argument('--models',type=Path,default=Path(__file__).parent / 'nfv-models')
parser.add_argument('--dafny',type=Path,required=True)
parser.add_argument('--solver',type=Path,required=True)
parser.add_argument('--phase',choices=['validity','domain','proof','refute'],required=True)
parser.add_argument('--select',nargs='*')
parser.add_argument('--mbqi',action='store_true',help='Sound supplemental Z3 model-based quantifier instantiation; does not suppress obligations.')
parser.add_argument('--variant',type=Path,help='Candidate entry-body variant; retains the original property and metadata.')
parser.add_argument('--label',default='',help='Prefix retained evidence phases, e.g. fix.')
args = parser.parse_args()
props = json.loads((args.models / 'properties.json').read_text(encoding='utf-8'))
directory = args.models / 'checks'
directory.mkdir(exist_ok=True)
history_path = args.models / 'checks.json'
history = json.loads(history_path.read_text(encoding='utf-8')) if history_path.exists() else []
failed = False
for prop in props:
    if args.select and prop['id'] not in args.select:
        continue
    model = (args.models / (prop['id'] + '.dfy')).read_text(encoding='utf-8')
    canonical_hash = hashlib.sha256(model.encode()).hexdigest()
    assert canonical_hash == prop['sha256'], (prop['id'],'metadata hash differs')
    if args.variant:
        assert args.select == [prop['id']], 'A candidate variant requires exactly one selected property'
        variant = args.variant.read_text(encoding='utf-8')
        first,last = signature(model,prop['entry_point'])
        vfirst,vlast = signature(variant,prop['entry_point'])
        assert model[:last] == variant[:vlast], 'Candidate changed a helper or an original entry contract'
        model = variant
    if args.phase in ('validity','domain'):
        checked = change_goals(model,prop['entry_point'],[])
        if args.phase == 'domain':
            checked += '\n' + domain_drivers(checked,prop,prop['witnesses'])
    elif args.phase == 'refute':
        witness = prop['witnesses'][0]
        pins = [name + ' == ' + literal(value) for name,value in witness.items()]
        negated = '!(' + ' && '.join('('+goal+')' for goal in prop['original_ensures']) + ')'
        checked = change_goals(model,prop['entry_point'],[negated],pins)
        checked += '\n' + domain_drivers(checked,prop,[witness])
    else:
        checked = model
    number = len(history) + 1
    phase = args.label + '-' + args.phase if args.label else args.phase
    name = f'{number:03}-{prop["id"]}-{phase}'
    path = directory / (name + '.dfy')
    path.write_text(checked,encoding='utf-8',newline='\n')
    command = [str(args.dafny),'verify',str(path),'--solver-path',str(args.solver),'--verification-time-limit','30','--cores','2','--allow-warnings','--show-snippets','false']
    if args.mbqi:
        command.extend(['--solver-option','O:smt.mbqi=true'])
    started = datetime.now(timezone.utc).isoformat()
    start = time.monotonic()
    completed = subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
    elapsed = round(time.monotonic()-start,3)
    (directory / (name + '.log')).write_text(completed.stdout,encoding='utf-8',newline='\n')
    record = dict(id=prop['id'],phase=phase,started_utc=started,seconds=elapsed,exit_code=completed.returncode,canonical_sha256=canonical_hash,input_sha256=hashlib.sha256(checked.encode()).hexdigest(),input=str(path.relative_to(args.models)),log=str((directory/(name+'.log')).relative_to(args.models)),command=command)
    history.append(record)
    history_path.write_text(json.dumps(history,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:record[k] for k in ('id','phase','seconds','exit_code','input')}),flush=True)
    if completed.returncode:
        failed = True
        print(completed.stdout,flush=True)
raise SystemExit(1 if failed else 0)
