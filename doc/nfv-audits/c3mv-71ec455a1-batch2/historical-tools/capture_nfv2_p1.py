"""Capture immutable text evidence for the batch-2 P1 applicability follow-up."""
import hashlib
import json
from pathlib import Path
import subprocess

repo = Path(r'C:\z3seq')
head = '71ec455a18702fe695d0c924a535ff9f385bd58d'
selections = {
    r'src\ast\ast.cpp': [(1612,1622)],
    r'src\ast\char_decl_plugin.cpp': [(133,150)],
    r'src\ast\seq_decl_plugin.cpp': [(765,797),(1040,1055)],
    r'src\ast\rewriter\seq_rewriter.cpp': [(1490,1634),(5598,5638)],
    r'src\ast\seq\seq_ambient_context.h': [(139,169)],
    r'src\ast\seq\seq_eq_facet.cpp': [(104,150),(290,307),(329,391),(1411,1465),(1673,1718)],
    r'src\ast\seq\seq_mem_facet.cpp': [(579,592),(1160,1258)],
    r'src\ast\seq\seq_ncontains_facet.cpp': [(28,67),(128,141),(201,434)],
    r'src\ast\seq\seq_ncontains_facet.h': [(104,149)],
    r'src\smt\seq_solver_facet.cpp': [(247,264)],
    r'src\smt\theory_nseq.cpp': [(196,206),(342,345),(474,523),(1068,1141),(1179,1251)],
    r'src\util\stx_search_tree.h': [(972,991),(1072,1118)],
    r'src\test\seq_ncontains_facet.cpp': [(77,104),(388,435)],
}
records = []
for path,ranges in selections.items():
    git_path = path.replace('\\','/')
    raw = subprocess.check_output(['git','show',head+':'+git_path],cwd=repo)
    content = raw.decode('utf-8')
    assert (repo/path).read_text(encoding='utf-8') == content, path
    lines = content.splitlines()
    indices = sorted({i for start,end in ranges for i in range(start,end+1)})
    assert indices[-1] <= len(lines), path
    blob = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    records.append(dict(path=git_path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),
                        line_count=len(lines),worktree_matches=True,
                        excerpts=[dict(line=i,text=lines[i-1]) for i in indices]))
out = Path(__file__).parent/'nfv2-p1-source-inventory.json'
out.write_text(json.dumps(dict(head=head,scope='Read-only immutable source excerpts; not an execution trace or correspondence proof',files=records),indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='pass',files=len(records),source_lines=sum(len(r['excerpts']) for r in records),artifact=str(out)),indent=2))
