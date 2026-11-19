"""Capture bounded, immutable source evidence for P12 applicability."""
import hashlib
import json
from pathlib import Path
import subprocess

repo=Path(r'C:\z3seq')
head='71ec455a18702fe695d0c924a535ff9f385bd58d'
selections={
    r'src\api\api_seq.cpp':[(48,91),(300,309)],
    r'src\api\z3_api.h':[(3928,3945)],
    r'src\api\api_context.cpp':[(406,424)],
    r'src\ast\ast.h':[(125,147)],
    r'src\ast\seq_decl_plugin.cpp':[(502,508),(714,720),(920,932)],
    r'src\ast\rewriter\seq_rewriter.cpp':[(2295,2341),(2573,2588)],
    r'src\ast\seq\seq_replace_all_facet.h':[(30,70),(94,120)],
    r'src\ast\seq\seq_replace_all_facet.cpp':[(24,41),(132,210),(213,289)],
    r'src\smt\theory_nseq.cpp':[(205,232),(592,613)],
    r'src\util\zstring.h':[(30,82)],
    r'src\util\zstring.cpp':[(74,108)],
    r'src\util\buffer.h':[(26,77),(137,166),(193,211)],
    r'src\util\memory_manager.cpp':[(70,81),(120,130),(268,290),(312,333),(389,414)],
    r'src\util\debug.h':[(83,111)],
    r'src\util\debug.cpp':[(74,88),(117,146)],
    r'src\util\error_codes.h':[(23,36)],
    r'src\parsers\smt2\smt2scanner.h':[(40,56)],
    r'src\parsers\smt2\smt2scanner.cpp':[(194,216)],
    r'src\parsers\smt2\smt2parser.cpp':[(1268,1275)],
}
wanted={p.replace('\\','/'):ranges for p,ranges in selections.items()}
tree=subprocess.check_output(['git','ls-tree',head,'--',*wanted],cwd=repo,text=True,encoding='utf-8')
blobs={row.split('\t',1)[1]:row.split()[2] for row in tree.splitlines()}
assert set(blobs)==set(wanted)
paths=sorted(wanted)
batch=subprocess.check_output(['git','cat-file','--batch'],input=('\n'.join(blobs[p] for p in paths)+'\n').encode(),cwd=repo)
offset=0
records=[]
for path in paths:
    end=batch.index(b'\n',offset)
    oid,kind,size=batch[offset:end].decode().split()
    assert oid==blobs[path] and kind=='blob'
    raw=batch[end+1:end+1+int(size)]
    offset=end+2+int(size)
    text=raw.decode('utf-8')
    assert repo.joinpath(*path.split('/')).read_text(encoding='utf-8')==text,path
    lines=text.splitlines()
    indices=sorted({i for start,last in wanted[path] for i in range(start,last+1)})
    assert indices[-1]<=len(lines)
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==oid
    records.append(dict(path=path,blob=oid,sha256=hashlib.sha256(raw).hexdigest(),line_count=len(lines),worktree_matches=True,excerpts=[dict(line=i,text=lines[i-1]) for i in indices]))
assert offset==len(batch)
output=Path(__file__).parent/'nfv3-p12-source-inventory.json'
output.write_text(json.dumps(dict(head=head,scope='Bounded immutable API/parser/literal/buffer/caller/VERIFY source tracing; not native reachability or execution evidence',files=records),indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='pass',files=len(records),source_lines=sum(len(f['excerpts']) for f in records),sha256=hashlib.sha256(output.read_bytes()).hexdigest()),indent=2))
