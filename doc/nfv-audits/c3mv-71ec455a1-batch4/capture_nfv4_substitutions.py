"""Capture producer scopes as immutable text; no production code execution."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

repo=Path(r'C:\z3seq'); root=Path(__file__).parent
head='71ec455a18702fe695d0c924a535ff9f385bd58d'
ledger=json.loads((root/'nfv3-coverage-ledger.json').read_text())
calls=ledger['broadcast_production_call_sites']
assert len(calls)==24
paths=sorted({c['path'] for c in calls})
tree=subprocess.check_output(['git','ls-tree',head,'--',*paths],cwd=repo,text=True)
oids={r.split('\t',1)[1]:r.split()[2] for r in tree.splitlines()}
assert set(oids)==set(paths)
raw=subprocess.check_output(['git','cat-file','--batch'],input=('\n'.join(oids[p] for p in paths)+'\n').encode(),cwd=repo)
offset=0; files=[]; producers=[]
for path in paths:
    end=raw.index(b'\n',offset); oid,kind,size=raw[offset:end].decode().split()
    blob=raw[end+1:end+1+int(size)]; offset=end+2+int(size)
    assert oid==oids[path] and kind=='blob'
    assert hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest()==oid
    text=blob.decode(); lines=text.splitlines()
    assert repo.joinpath(*path.split('/')).read_text(encoding='utf-8')==text
    masked=re.sub(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'',lambda m:''.join('\n' if c=='\n' else ' ' for c in m.group()),text,flags=re.S)
    scopes=[]
    for m in re.finditer(r'^    (?=\S)[^\n;]*?\b(\w+(?:::\w+)*)\([^;{}]*\)[^;{}]*\{',masked,re.M):
        start=masked.rfind('{',m.start(),m.end()); level=1; pos=start+1
        while level and pos<len(masked):
            level+=(masked[pos]=='{')-(masked[pos]=='}'); pos+=1
        assert level==0
        scopes.append(dict(function=m[1],first=masked.count('\n',0,m.start())+1,last=masked.count('\n',0,pos)+1))
    indices=set()
    for c in calls:
        if c['path']!=path:continue
        assert lines[c['line']-1].strip()==c['text']
        containing=[s for s in scopes if s['first']<=c['line']<=s['last']]
        assert len(containing)==1,(c,containing)
        scope=containing[0]
        producers.append(dict(**c,**scope))
        indices.update(range(scope['first'],scope['last']+1))
    extra=[(35,68),(109,151),(373,391)] if path.endswith('seq_eq_facet.cpp') else [(27,70)] if path.endswith('seq_power_facet.cpp') else [(323,363)]
    for first,last in extra:indices.update(range(first,last+1))
    files.append(dict(path=path,blob=oid,sha256=hashlib.sha256(blob).hexdigest(),line_count=len(lines),worktree_matches=True,excerpts=[dict(line=i,text=lines[i-1]) for i in sorted(indices)]))
assert offset==len(raw) and len(producers)==24
result=dict(head=head,master='c2460a558fc6fee3cf15cfebd2d3f642ebf77770',previous_publication='13cfdf0d3f046886dd16ae6aef2c9853679b4877',scope='Producer function lexical scopes and sink/lookup contexts, not a global invariant proof',files=files,producers=producers,validation_history=[dict(result='Initial lexical-scope assertion failed, before output; not a verifier check',cause='Multiline model_completion_split::split declaration was omitted by a single-line signature pattern',correction='Allow newline-separated arguments while excluding braces/semicolons; still check every known site has exactly one containing scope and exact pinned call text'),dict(result='Second lexical-scope assertion failed, before output; not a verifier check',cause='The namespace-local free helper unfold_empty was excluded by requiring a qualified method name',correction='Admit namespace-indented free functions too, retaining exactly-one-scope assertions for every site')])
target=root/'nfv4-subst-source-inventory.json'
result['validation_history'].append(dict(result='Third lexical-scope assertion failed, before output; not a verifier check',cause='A nested if with size() was admitted after broadening names to free functions',correction='Require exactly four-space namespace indentation before a nonspace header character; preserve exactly-one-scope checks and disclose this local lexical heuristic, not official upstream extraction'))
assert not target.exists()
target.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
groups={}
for p in producers:groups.setdefault((p['path'],p['function'],p['first'],p['last']),[]).append(p['line'])
print(json.dumps(dict(status='pass',files=len(files),excerpt_lines=sum(len(f['excerpts']) for f in files),producer_calls=24,scopes=[dict(path=k[0],function=k[1],span=[k[2],k[3]],call_lines=v) for k,v in groups.items()],sha256=hashlib.sha256(target.read_bytes()).hexdigest()),indent=2))
