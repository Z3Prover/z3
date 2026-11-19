"""Read-only validation of full raw evidence, unchanged goals and gate-aware outcomes."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))


def at(base, name):
    path = (base/name).resolve()
    assert path.is_relative_to(base.resolve()) and path.is_file(), name
    return path


def literal(value):
    if type(value) is bool:
        return str(value).lower()
    if type(value) is int:
        return str(value) if value >= 0 else '('+str(value)+')'
    return '['+','.join(literal(v) for v in value)+']'


def validate(root):
    manifest = load(root/'manifest.json')
    listed = set()
    for f in manifest['files']:
        path = at(root, f['path'])
        assert not path.is_symlink() and path.stat().st_size == f['bytes'] and sha(path) == f['sha256'], f['path']
        assert path not in listed
        listed.add(path)
    assert listed == {p for p in root.rglob('*') if p.is_file() and p != root/'manifest.json'}
    exceptions = sorted(p.relative_to(root).as_posix() for p in listed if b'\r\n' in p.read_bytes())
    assert load(root/'export-notes.json')['raw_crlf_exceptions'] == exceptions
    assert (root/'.gitattributes').read_text() == '* text eol=lf\n'+''.join(p+' -text\n' for p in exceptions)
    seal = load(root/'nfv5-model-freeze.json')
    for f in seal['files']+seal['baseline_files']:
        assert sha(at(root, f['path'])) == f['sha256']
    assert sha(root/'nfv5-retranslation-plan.json') == seal['plan_sha256'] == load(root/'nfv5-retranslation-plan-freeze.json')['plan_sha256']
    assert sha(root/'nfv5-original-selection.json') == seal['selection_sha256']
    assert sha(root/'nfv5-baseline-model-freeze.json') == seal['baseline_seal_sha256']
    models = root/'nfv5-models'
    assert sha(models/'draft-checks.json') == seal['draft_history_sha256']
    drafts, checks, props = [load(models/name) for name in ['draft-checks.json','checks.json','properties.json']]
    assert len(drafts) == 7 and all(h['exit_code']==0 for h in drafts)
    for h in drafts:
        assert sha(at(models,h['log'])) == h['log_sha256']
        for f in h['inputs']:
            assert sha(at(models,f['path'])) == f['sha256']
    assert [h['sequence'] for h in checks] == list(range(1,17))
    assert sum(h['exit_code']==0 for h in checks) == 4
    assert [p['id'] for p in props] == ['P20','P21','P22']
    edits = {'Widths':('{ seq(|rows|, i => |rows[i]|) }','{ seq(|rows|, i => |R(rows,i)|) }'),
        'Deactivate':('{ seq(|active|, i => active[i] && i!=idx) }','{ seq(|active|, i => B(active,i) && i!=idx) }'),
        'Rebase':('{ seq(|rows|, i => if B(active,i) && tok in rows[i] then Substitute(rows[i],tok,repl) else rows[i]) }',
                  '{ seq(|rows|, i => if B(active,i) && tok in R(rows,i) then Substitute(R(rows,i),tok,repl) else R(rows,i)) }')}
    baseline_props = load(models/'baseline'/'properties.json')
    for p in props:
        old = next(b for b in baseline_props if b['id']==p['id'])
        for key in ['inputs','outputs','assumptions','original_ensures','environment','examples','frozen_intent']:
            assert p[key] == old[key], (p['id'],key)
        baseline = (models/(p['id']+'.dfy')).read_text()
        assert sha(models/(p['id']+'.dfy')) == p['sha256']
        assert baseline == (models/'frozen'/(p['id']+'.dfy')).read_text()
        previous = (models/'baseline'/(p['id']+'.dfy')).read_text()
        for key in ['Widths','Deactivate','Rebase'] if p['id']=='P20' else ['Widths']:
            before, after = edits[key]
            assert previous.count(before)==1
            previous = previous.replace(before,after)
        assert previous == baseline
        start = baseline.index('method '+p['entry_point']+'(')
        opening = baseline.index('\n{',start)
        header = baseline[start:opening]
        assert re.findall(r'^\s*requires ([^\n]*)',header,re.M)==[a['clause'] for a in p['assumptions']]
        assert re.findall(r'^\s*ensures ([^\n]*)',header,re.M)==p['original_ensures']
        removed, count = re.subn(r'^// synth:[^\n]*\n[ \t]*ensures [^\n]*\n','',header,flags=re.M)
        assert count==3
        validity = baseline[:start]+removed+baseline[opening:]
        attempts = [h for h in checks if h['id']==p['id']]
        for h in attempts:
            checked = at(models,h['input']).read_text()
            assert sha(at(models,h['input']))==h['input_sha256'] and sha(at(models,h['log']))==h['log_sha256']
            if h['kind']=='validity':
                assert checked==validity
            else:
                assert any(prior['kind']=='validity' and prior['exit_code']==0 and prior['sequence']<h['sequence'] for prior in attempts)
                if h['kind']=='domain':
                    blocks = checked.split('\n// Independent concrete domain/caller, not a native execution.')
                    assert blocks[0]==validity and len(blocks)==len(p['examples'])+1
                    for i,(example,block) in enumerate(zip(p['examples'],blocks[1:]),1):
                        assert block.startswith('\nmethod ConcreteDomain'+str(i)+'()\n{\n')
                        for name,value in example['inputs'].items():
                            assert block.count('var '+name+': '+p['inputs'][name]+' := '+literal(value)+';')==1
                        assert re.findall(r'\b'+re.escape(p['entry_point'])+r'\(([^()]*)\);',block)==[','.join(p['inputs'])]
                        assert not re.search(r'\b(assume|axiom)\b',re.sub(r'//[^\n]*','',block))
                else:
                    assert h['kind']=='proof' and checked==baseline
                    assert any(prior['kind']=='domain' and prior['exit_code']==0 and prior['sequence']<h['sequence'] for prior in attempts)
            command = h['command']
            assert command[command.index('--solver-path')+1].endswith('z3-4.12.1.exe')
            assert command[command.index('--cores')+1]=='2' and command[command.index('--verification-time-limit')+1]=='30'
            assert ('--isolate-assertions' in command)==h.get('isolate_assertions',False)
            assert not any(c.startswith('--filter') or c=='--dont-verify-dependencies' for c in command)
    assert {h['id'] for h in checks if h['kind']=='domain' and h['exit_code']==0}=={'P22'}
    assert not any(h['kind']=='proof' and h['exit_code']==0 for h in checks)
    intervention = load(root/'nfv5-attempt13-resource-intervention.json')
    assert checks[12]['exit_code']==intervention['recorded_exit_code']==4294967295
    assert checks[12]['seconds']==intervention['recorded_seconds']==1887.87
    assert checks[14]['wall_timed_out'] and checks[14]['exit_code']==124
    assert '[audit harness] Wall-clock resource limit reached' in at(models,checks[14]['log']).read_text()
    results = load(root/'nfv5-results.json')
    assert sha(models/'checks.json')==results['checks_sha256']
    assert sha(root/'nfv5-model-freeze.json')==results['freeze_sha256']
    assert sha(root/'nfv5-attempt13-resource-intervention.json')==results['resource_intervention_sha256']
    summary = results['summary']
    assert summary['verified']==summary['refuted']==summary['native_executions']==summary['new_source_entries']==0
    assert summary['resources_exhausted']==3 and summary['admitted_examples']==4 and summary['verifier_attempts']==16
    for f in load(root/'nfv5-verification-handoff.json')['files']:
        assert sha(at(root,f['path']))==f['sha256']
    for path in root.rglob('*.py'):
        ast.parse(path.read_text(encoding='utf-8-sig'), filename=str(path))
    for name in ['README.md','nfv5-verification.md','nfv5-modeling.md']:
        prose = re.sub(r'```.*?```','',(root/name).read_text(),flags=re.S)
        for link in re.findall(r'\]\(([^)]+)\)',prose):
            if not link.startswith(('https://','http://')):
                at(root,link)
    provenance = subprocess.run([sys.executable,'-B',str(root/'check_nfv5_models.py'),'--provenance-only',str(models)],capture_output=True,text=True)
    assert provenance.returncode==0, provenance.stdout+provenance.stderr
    tools = load(root/'tool-validation'/'results.json')
    assert tools['status']=='pass' and tools['live_verifier_invocations']==4
    replayed = load(root/'tool-validation'/'replay'/'results.json')
    assert [h['sequence'] for h in replayed]==[1,2,3,6]
    assert all(h['matched'] and h['actual_exit']==0 for h in replayed)
    for h in replayed:
        assert sha(at(root/'tool-validation'/'replay',h['log']))==h['log_sha256']
    assert 'Ran 4 tests' in (root/'tool-validation'/'replay-tests.log').read_text()
    assert 'Ran 3 tests' in (root/'tool-validation'/'watchdog-tests.log').read_text()
    print(json.dumps(dict(status='pass',files=len(listed)+1,audit_attempts=16,live_tool_replays=4,
        whole_properties_verified=0,whole_properties_refuted=0,resources_exhausted=3,
        checks='Raw manifest, seals, exact five-line translation revision, all input/log hashes, full contracts/domains/positives, gate order, resource receipts, provenance, syntax, links, tools and replay.'),indent=2))


if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle',type=Path,default=Path(__file__).resolve().parent)
    validate(parser.parse_args().bundle.resolve())
