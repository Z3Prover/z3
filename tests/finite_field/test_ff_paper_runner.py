"""Resource/status regressions for the paper-comparison supervisor (psutil)."""
import json
from pathlib import Path
import sys
import tempfile
import time
import psutil
import benchmark_ff_paper as bench


def main():
    with tempfile.TemporaryDirectory(prefix='ff-paper-supervision-') as temp:
        root=Path(temp);source=root/'problem.smt2';source.write_text('(check-sat)\n')
        tests=[('success','print("unsat")',3,16384,'unsat'),
               ('wrong_answer','print("sat")',3,16384,'sat'),
               ('nonzero','import sys\nprint("unsat")\nsys.exit(1)',3,16384,'error'),
               ('timeout','import subprocess,sys,time\np=subprocess.Popen([sys.executable,"-c","import time; time.sleep(30)"],start_new_session=True)\nopen(sys.argv[0]+".pid","w").write(str(p.pid))\ntime.sleep(30)',1,16384,'timeout'),
               ('memory','import time\ntime.sleep(30)',3,1,'memout')]
        for name,body,timeout,memory,expected in tests:
            script=root/(name+'.py');script.write_text(body)
            directory=root/name;directory.mkdir()
            # An interrupted/retried worker must never reuse a stale success.
            (directory/'result.json').write_text(json.dumps(dict(status='checked',produced=True)))
            job=dict(directory=str(directory),input=str(source),configuration=dict(id=name,kind='solve',command=[sys.executable,str(script)]),timeout=timeout,memory_mib=memory,sha256='synthetic',member=name,carcara='',ffpacheck='')
            result=bench.supervise(job)
            assert result['status']==expected,result
            assert not result.get('produced'),result
            if name=='timeout':
                pid=int(Path(str(script)+'.pid').read_text());time.sleep(.1)
                assert not psutil.pid_exists(pid) or psutil.Process(pid).status()==psutil.STATUS_ZOMBIE
    print('5 supervisor regressions passed, including separate-session descendant cleanup')


if __name__=='__main__':main()
