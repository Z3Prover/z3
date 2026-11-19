"""Refine three remaining areas; capture immutable evidence and new master pin."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

repo=Path(r'C:\z3seq')
root=Path(__file__).parent
head='71ec455a18702fe695d0c924a535ff9f385bd58d'
master='c2460a558fc6fee3cf15cfebd2d3f642ebf77770'
old_master='d738f81eab9af1468394664a812fe4310ae8e1fa'
def git(*args):return subprocess.check_output(['git',*args],cwd=repo,text=True,encoding='utf-8').strip()
base=git('merge-base',head,master)
assert base=='437536cd64a544a1c329fc57d83e56e294fdf47c'
selections={
    'src/ast/seq/seq_power_facet.cpp':[(94,108),(110,142),(271,305),(385,581)],
    'src/ast/seq/seq_eq_facet.cpp':[(35,68),(109,151),(288,307),(373,398)],
    'src/ast/seq/seq_eq_facet.h':[(145,156),(190,225)],
    'src/ast/seq/seq_mem_facet.cpp':[(1008,1060)],
    'src/ast/seq_decl_plugin.h':[(60,67),(315,320)],
    'src/util/stx_search_tree.h':[(119,137),(570,850),(1070,1106)],
    'src/util/vector.h':[(579,589)],
    'src/util/obj_hashtable.h':[(25,58)],
    'src/util/hashtable.h':[(514,516),(541,573)],
}
tree=git('ls-tree',head,'--',*selections)
oids={r.split('\t',1)[1]:r.split()[2] for r in tree.splitlines()}
assert set(oids)==set(selections)
paths=sorted(oids)
batch=subprocess.check_output(['git','cat-file','--batch'],input=('\n'.join(oids[p] for p in paths)+'\n').encode(),cwd=repo)
offset=0
records=[]
calls=[]
for path in paths:
    end=batch.index(b'\n',offset)
    oid,kind,size=batch[offset:end].decode().split()
    raw=batch[end+1:end+1+int(size)]
    offset=end+2+int(size)
    assert oid==oids[path] and kind=='blob'
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==oid
    text=raw.decode('utf-8')
    assert repo.joinpath(*path.split('/')).read_text(encoding='utf-8')==text
    lines=text.splitlines()
    indices={i for first,last in selections[path] for i in range(first,last+1)}
    if path.endswith(('seq_eq_facet.cpp','seq_mem_facet.cpp','seq_power_facet.cpp')):
        for i,line in enumerate(lines,1):
            if re.search(r'\bbroadcast_subst\(',line) and not re.search(r'void\s+broadcast_subst\(',line):
                calls.append(dict(path=path,line=i,text=line.strip()))
                indices.update(range(max(1,i-8),min(len(lines),i+8)+1))
    assert max(indices)<=len(lines)
    records.append(dict(path=path,blob=oid,sha256=hashlib.sha256(raw).hexdigest(),line_count=len(lines),worktree_matches=True,excerpts=[dict(line=i,text=lines[i-1]) for i in sorted(indices)]))
assert offset==len(batch) and len(calls)==24
inventory=dict(head=head,scope='Incremental C10/C11/C12 evidence and all 24 enumerated production broadcast call sites; not a complete caller-invariant proof or source execution',files=records)
inventory_path=root/'nfv3-coverage-source-inventory.json'
inventory_path.write_text(json.dumps(inventory,indent=2)+'\n',encoding='utf-8',newline='\n')
changes=lambda a,b: [dict(status=r.split('\t')[0],paths=r.split('\t')[1:]) for r in git('diff','--name-status',a,b).splitlines() if r]
master_changes=changes(old_master,master)
direct=changes(master,head)
branch_changes=changes(base,head)
overlap=sorted({p for r in master_changes for p in r['paths']} & {p for r in branch_changes for p in r['paths']})
assert not ({p for r in master_changes for p in r['paths']} & set(selections))
candidates=[
 dict(id='C10-apply-word-identity',path='src/ast/seq/seq_power_facet.cpp',entry='power_trichotomy::apply',span=[455,579],status='ready for intent selection, not selected or proved',whole_property='For a selected nonempty branch f1/f2/f3/f4 under its actual equations and direction/length guards, interpreted Y^N equals X^M concatenated with the emitted residual z.',requirements=['Use body-defined word power with nonpositive exponents yielding epsilon, concatenation and slices, not unconstrained length/count proxies.','Preserve f1 N>=1; f2 M>=1 and conditional nonnegative residual inference only when the root is nonempty; an unconstrained fresh root may be empty and N is not explicitly bounded there.','Preserve f3 M,N>=2, symbolic k unbounded below, and distinguish period-param construction from fresh p1/p2 with its asserted X equation.','Preserve f4 M=1, q>=0, q+1<=N, and prefix/suffix orientation.','No claim of branch exhaustiveness, dependency/broadcast lifetime safety, or arithmetic-engine correspondence.']),
 dict(id='C10-period-decomposition',path='src/ast/seq/seq_power_facet.cpp',entry='power_trichotomy::enumerate / constant-period f3 preparation',span=[439,449],status='possible supporting helper/whole obligation; avoid double counting',whole_property='A valid period r and the actual suffix/slice construction yield X=(p1.p2)^floor(|X|/r).p1; period need not divide length.',requirements=['Read and preserve has_period body, r>0 and r<|X| from enumeration, and l1=|X| mod r.','Do not silently replace suffix p1 by a prefix without proving equality.','No full-trichotomy completeness claim; admit unsigned length-sum limits explicitly.']),
 dict(id='C11-elimination-termination',path='src/ast/seq/seq_eq_facet.cpp',entry='eq_facet::eliminate',span=[128,151],status='deferred pending caller-justified global substitution invariant',observation='on_stack.remove(t) precedes on_stack.contains(t); obj_hashtable uses pointer-set removal, so that test does not provide an ancestor-cycle guard.',requirements=['All 24 production broadcast call sites are enumerated, but representative occurs checks do not prove a global acyclic latest-binding graph.','The central broadcaster dispatches to every sink without a uniform occurs check; eq_facet::apply_subst appends newest bindings and does not normalize earlier substitution RHS vectors.','Do not invent fuel or assume acyclicity/rank as a proved caller fact; do not claim a reachable cycle, hang or crash.']),
 dict(id='C12-rewatch-representation',path='src/util/stx_search_tree.h',entry='try_rewatch',span=[692,708],status='confirmed representation mismatch observation; primarily missed-hit/performance scope, not solver-unsoundness evidence',observation='constraint_store interns via pointee hash/equals and owns clones; vector<constraint_i const*>::contains compares pointer identity. Equation clone() allocates a different live object.',requirements=['Current watched id can be semantically active through find(), while another canonical clone is absent by pointer comparison despite an equal live fact.','A small explicit identity-versus-value model could assess the documented rewatch iff contract, but must label a converse failure as missed-hit behavior, not unsound SAT/UNSAT.','No compiled execution, native cache-hit measurement or general cache correctness proof.']),
 dict(id='C12-core-entailment',path='src/util/stx_search_tree.h',entry='filter_by_conflict_dep / cache_insert',span=[775,846],status='deferred semantic sufficiency/provenance proof',observation='Leaf-subset filtering alone is not a proof that retained live facts semantically entail a contradiction.',requirements=['Need all conflict-dependency producers, excluded-facet meaning, substitution and derived-fact provenance, not an assumed unsat-core oracle.','A mechanical subset-filter proof must not replace the original semantic soundness goal or count it as closed.']),
 dict(id='C12-eligibility-gate',path='src/util/stx_search_tree.h',entry='cache_eligible',span=[637,646],status='optional distinct whole-function control gate, not a replacement for cache soundness',whole_property='Eligibility holds exactly when no present signature-excluded facet reports live unsatisfied state.',requirements=['Facet presence/signature/satisfaction are disclosed observations; preserve the complete actual loop and early return.','This proves only the admission gate, not that any cached core is unsatisfiable; select only if useful, not to fill quota.']),
]
for candidate in candidates:
    captured={e['line'] for f in records if f['path']==candidate['path'] for e in f['excerpts']}
    assert set(range(candidate['span'][0],candidate['span'][1]+1))<=captured
assert git('rev-parse','HEAD:src')==git('rev-parse',head+':src')
ledger=dict(head=head,comparison_master=master,previous_comparison_master=old_master,merge_base=base,previous_publication='146f70d7ddf5507fdf731af2511edf4c5f669fc5',baseline_note='Master advanced by two commits; prior published reports remain pinned to their old comparison. Audited production source and merge base unchanged.',master_only_new_changes=master_changes,direct_master_to_head_file_count=len(direct),direct_master_to_head_src_count=sum(any(p.startswith('src/') for p in r['paths']) for r in direct),branch_introduced_file_count=len(branch_changes),branch_introduced_src_count=sum(any(p.startswith('src/') for p in r['paths']) for r in branch_changes),scope='Incremental refinement only, not a repeated full file classification or intent selection',inventory_sha256=hashlib.sha256(inventory_path.read_bytes()).hexdigest(),broadcast_production_call_sites=calls,candidates=candidates,p13='Complete queue property remains unresolved; not replaced by a weaker goal.',new_models=0,new_verifier_attempts=0)
(root/'nfv3-coverage-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n',encoding='utf-8',newline='\n')
ledger['new_master_paths_overlapping_branch_delta']=overlap
ledger['validation_history']=[dict(check='New master paths disjoint from entire branch delta',result='failed source-coverage assertion, not a verifier check',exception='AssertionError',overlap=['src/test/smt_context.cpp'],resolution='Corrected the overbroad claim; require disjointness only from the nine currently captured candidate/source-trace files, and preserve the broader overlap explicitly.'),dict(check='Pinned Git blob hashes, worktree text, candidate spans, producer count, unchanged source tree and disjoint current-candidate paths',result='passed')]
(root/'nfv3-coverage-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='pass',source_files=len(records),excerpt_lines=sum(len(f['excerpts']) for f in records),broadcast_call_sites=len(calls),comparison_master=master,master_new_changes=master_changes,direct_master_to_head_files=len(direct),direct_master_to_head_src_files=ledger['direct_master_to_head_src_count'],branch_introduced_files=ledger['branch_introduced_file_count']),indent=2))
