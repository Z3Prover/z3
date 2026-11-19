"""Exercise published replay and failure aggregation, separate from audit runs."""
import ast
import json
from pathlib import Path
import shutil
import subprocess
import sys

root=Path(__file__).parent
report=Path(r'C:\z3seq\doc\nfv-audits\c3mv-71ec455a1-batch3')
work=root/'nfv3-tool-validation'
assert not work.exists()
work.mkdir()
for n in ('replay_checks.py','validate_publication.py'):ast.parse((report/n).read_text())
tools=['--dafny',str(root/'nfv-tools'/'dafny'/'Dafny.exe'),'--solver',str(root/'nfv-tools'/'dafny'/'z3'/'bin'/'z3-4.12.1.exe')]
command=[sys.executable,str(report/'replay_checks.py'),*tools,'--select','009','013','018','--output',str(work/'replay')]
normal=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
(work/'replay-command.log').write_text(normal.stdout,encoding='utf-8',newline='\n')
assert normal.returncode==0,normal.stdout
fixture=work/'runner-fixture'
(fixture/'nfv3-models'/'checks').mkdir(parents=True)
shutil.copyfile(report/'replay_checks.py',fixture/'replay_checks.py')
history=json.loads((report/'nfv3-models'/'checks.json').read_text())
chosen=[dict(c) for c in history if Path(c['input'].replace('\\','/')).name.split('-')[0] in ('009','013')]
assert len(chosen)==2 and chosen[0]['exit_code']!=0 and chosen[1]['exit_code']==0
chosen[0]['exit_code']=0
for c in chosen:
    relative=Path(c['input'].replace('\\','/'))
    shutil.copyfile(report/'nfv3-models'/relative,fixture/'nfv3-models'/relative)
(fixture/'nfv3-models'/'checks.json').write_text(json.dumps(chosen,indent=2)+'\n',encoding='utf-8',newline='\n')
command=[sys.executable,str(fixture/'replay_checks.py'),*tools,'--output',str(work/'mismatch')]
mixed=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
(work/'mismatch-command.log').write_text(mixed.stdout,encoding='utf-8',newline='\n')
assert mixed.returncode==1,mixed.stdout
records=json.loads((work/'mismatch'/'results.json').read_text())
assert len(records)==2 and not records[0]['matched'] and records[1]['matched']
summary=dict(status='pass',live_verifier_invocations=5,audit_verifier_attempts_unchanged=18,replay_exit=normal.returncode,mismatch_exit=mixed.returncode,replay_checks=['009 expected failed full property','013 accepted complete refutation','018 complete candidate property'],mismatch_test='A separate fixture changes only the first expected exit to zero; its real failed proof must make replay fail despite a later real successful proof. This is orchestration test data, not audit evidence.',no_production_source_execution=True)
(work/'results.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8',newline='\n')
for p in work.rglob('*'):
    if p.is_file():
        dest=report/'tool-validation'/p.relative_to(work)
        dest.parent.mkdir(parents=True,exist_ok=True)
        assert not dest.exists()
        shutil.copyfile(p,dest)
print(json.dumps(summary,indent=2))
