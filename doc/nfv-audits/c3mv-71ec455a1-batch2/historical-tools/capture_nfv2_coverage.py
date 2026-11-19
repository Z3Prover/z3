"""Generate a source-grounded gap ledger, not proof or native execution results."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

repo = Path(r'C:\z3seq')
session = Path(__file__).parent
head = '71ec455a18702fe695d0c924a535ff9f385bd58d'
base = '437536cd64a544a1c329fc57d83e56e294fdf47c'
master = 'd738f81eab9af1468394664a812fe4310ae8e1fa'

def git(*args):
    return subprocess.check_output(['git',*args],cwd=repo)

def candidate(ident,priority,path,entry,start,end,gap,obligation,limit,next_step):
    return dict(id=ident,priority=priority,path=path,entry=entry,span=[start,end],
                previous_gap=gap,proposed_obligation=obligation,limits=limit,next_step=next_step,
                status='candidate; not selected, modeled, verified, or refuted')

candidates = [
    candidate('C01','high','src/ast/seq/seq_ncontains_facet.cpp','ncontains_propagation::propagate',232,301,
              'P1 covered prefix pruning only, not the all-determined-mismatches discharge.',
              'A discharged negative containment must be valid at character offsets, including variable-width and empty-valued symbolic tokens.',
              'Start with symbolic token shapes [X,a,Y] and [X,b,Z]; a!=b. Candidate valuation X=aa,Y=b,Z=epsilon is only a hypothesis here.',
              'Select the complete discharge-soundness property before constructing a new model; do not extend the prior candidate-fix proof.'),
    candidate('C02','high','src/ast/seq/seq_replace_all_facet.cpp','replace_all_split::apply_case',215,268,
              'P4 checked match_at with one-character-width token valuations, not replacement splitting.',
              'Every generated empty/end/match/copy branch preserves first-occurrence replacement semantics and the cases cover all inputs under the actual pattern guard.',
              'Must retain nonempty constant pattern, nonoverlapping replacement-all scanning, fresh-tail equations and the first-character copy behavior. Model case-count arithmetic including unsigned overflow separately or explicitly bound it.',
              'Inspect pattern admission and iterator initialization; use actual case numbering, not an idealized partition.'),
    candidate('C03','high','src/ast/seq/seq_req_facet.cpp','req_propagation::propagate',26,120,
              'No earlier property modeled erasing a request vector while advancing qhead.',
              'Resolved requests are removed, unknown requests retained in order, conflicting verdicts stop, qhead remains in range and pop restores prior queue state.',
              'Regex bisimulation verdicts may be explicit inputs for this bookkeeping property; this cannot prove the regex oracle.',
              'Read vector_erase_trail semantics before translation; preserve same-index reexamination and remove-below-qhead adjustment.'),
    candidate('C04','high','src/ast/rewriter/seq_derive.cpp','derive::exclude_interval',1427,1471,
              'No earlier model covered derivative path-interval mutation or boundary arithmetic.',
              'The active interval suffix denotes exactly the original set minus the excluded interval; retained history and push/pop boundaries stay valid, with guarded endpoint +/-1.',
              'Proper character-domain intervals and a valid initial suffix are actual preconditions, not assumptions that the result is correct.',
              'Read callers and path-stack restore; include the intersect_intervals helper and endpoint cases 0/max_char.'),
    candidate('C05','high','src/ast/seq/seq_stoi_facet.h','stoi_facet::check_stoi_coherence',92,175,
              'P8 treated coherence as an external observation; it did not inspect its callback/state safety.',
              'Axiom callbacks may append/reallocate tracking terms without invalidating the saved term/depth; depth updates remain monotone and guarded bounds equal 10^k-1.',
              'Requires a justified append-only callback contract, finite registration behavior and mathematical numeric bounds; does not establish a decimal parser or AST memory safety by itself.',
              'Trace m_instantiate/add_term callbacks and validate actual registration dedup before choosing a faithful finite-state model.'),
    candidate('C06','high','src/ast/simplifiers/seq_regular_simplifier.cpp','regular_compiler::preimage',762,895,
              'P9 covered only negative decimal thresholds, not preimages of indexing/extraction.',
              'The selected str.at fixed-index and last-index preimages agree with extraction membership for all words, including short/empty words and nullable target languages.',
              'Focus on the exact selected branches and k<=64 guard. Character membership and epsilon membership suffice only because str.at returns length at most one.',
              'Read length/nullable/regex concatenation helpers; retain both successful-character and epsilon branches.'),
    candidate('C07','high','src/solver/assertions/asserted_formulas.cpp','asserted_formulas::simplify_replace_contains',317,416,
              'No earlier model checked the new replacement/contains preprocessing rule.',
              'A single-character containment observation is unchanged by first-occurrence str.replace when neither constant needle nor replacement contains that character.',
              'Must include empty needles and no-match behavior. This is the local rewrite, not a proof of shared-mark traversal, proof production or all parent-blocking gates.',
              'Translate actual replace semantics with body-defined first-match search; separately document global applicability guards and ancestor blocking.'),
    candidate('C08','high','src/ast/seq/seq_ncontains_facet.cpp','ncontains_facet::apply_subst',28,67,
              'P1 excluded dependencies, qhead rewind, append/deactivate operations and trailing.',
              'Substitution updates exactly active matching haystack/needle occurrences, joins justification when touched, rewinds the scan appropriately, and undo restores previous fields and dependencies.',
              'Value-state/trail modeling alone does not establish C++ alias or allocator correctness; inspect trail helpers and distinguish a null substitution dependency from an empty dependency set.',
              'Model a bounded operation sequence with source-faithful update order and genuine trail reversal, not a direct assignment of the expected old state.'),
    candidate('C09','medium','src/ast/rewriter/seq_regex_witness.cpp','regex_witness::accepts',131,249,
              'No previous property covered witness acceptance or its work/depth bounds.',
              'For selected Boolean regex constructors, three-valued acceptance returns a definite verdict only when supported by all needed branches, and budget exhaustion stays unknown.',
              'This wrapper property would not establish derivative correctness, ground slicing or full regex acceptance. Preserve shared mutable work and short-circuit order.',
              'Define a source-grounded constructor slice and exact work/depth arithmetic before selection; do not use successful child results as proof of entire acceptance.'),
    candidate('C10','medium','src/ast/seq/seq_power_facet.cpp','power_trichotomy::apply',455,581,
              'P5 proved primitive-root minimality, not trichotomy branches or their completeness.',
              'A selected f3 periodic-word branch emits a residual z satisfying Y^N = X^M.z under the branch equations and M,N>=2.',
              'One-branch soundness is not trichotomy exhaustiveness; preserve prefix/suffix orientation, exponent truncation semantics and constant-base period conditions.',
              'Read all helper definitions and caller guards; choose a tractable complete word identity rather than replacing word semantics with unconstrained counts.'),
    candidate('C11','high-followup','src/ast/seq/seq_eq_facet.cpp','eq_facet::eliminate',104,150,
              'No previous model checked recursive substitution expansion termination or cycle invariants.',
              'Expansion terminates and preserves represented words under the weakest caller-justified substitution-graph invariant.',
              'Observed on_stack.remove(t) occurs before on_stack.contains(t); this alone is not a reachable cycle/crash proof. Acyclicity may be maintained by callers.',
              'Trace every substitution producer before modeling; separate malformed-state behavior from reachable release behavior. Do not mask an unbounded loop with an invented fuel counter.'),
    candidate('C12','high-followup','src/util/stx_search_tree.h','search_tree::filter_by_conflict_dep / try_rewatch',631,849,
              'P7 proved only child-verdict aggregation, not cache/core entailment or watch representation.',
              'A cache hit is justified by a valid stored unsat core actually contained in the current semantically active facts, and excluded live facets block unsafe caching.',
              'Must trace provenance of conflict dependencies; do not assume leaf-subset filtering implies semantic unsatisfiability. Canonical clone pointers and live pointers are distinct representations.',
              'Inspect vector contains semantics, clone/equality rules, dependency construction and watch-list mutation. Potential missed cache hits are performance observations, not logical failures.'),
    candidate('C13','high-followup','src/smt/theory_nseq.cpp','seq_model_value_proc::mk_value',79,151,
              'P8 excluded complete model reconstruction and nested power-token processing.',
              'Generated power delimiters are balanced, starts/exponents stacks never underflow, and rebuilt values preserve dependencies and sequence denotation.',
              'Cannot prove safety by assuming arbitrary external token streams are balanced without tracing the actual producers. AST reference/GC lifetime is a separate obligation.',
              'Trace slot producers and retain nested scopes, empty bases and exponent semantics before a dedicated later batch.'),
    candidate('C14','medium','src/ast/simplifiers/seq_regular_simplifier.cpp','regular_compiler::bounded_length / decimal_greater',138,169,
              'P9 excluded nonnegative decimal languages and numerical bound propagation.',
              'Saturating length sums and conditional upper bounds never underestimate actual words; separately, positive-threshold decimal languages must handle leading zeros and magnitude boundaries.',
              'These are TWO distinct future properties, not one selected whole property. Need actual add_truncate and decimal constructor semantics; do not reuse P9 conversion assumptions as a parser proof.',
              'Split into separate entries if selected later; retain UINT_MAX sentinel behavior, numeral-size budget and loop indexing.'),
]

previous_models = {
    'P1': ('src/ast/seq/seq_ncontains_facet.cpp','selected symbolic prefix-pruning shape only'),
    'P2': ('src/ast/seq/seq_eq_facet.cpp','resolved-character disequality cancellation only'),
    'P3': ('src/ast/seq/seq_lex_facet.cpp','resolved-character lexicographic obligation only'),
    'P4': ('src/ast/seq/seq_replace_all_facet.cpp','constant pattern helper with unit-width valuations only'),
    'P5': ('src/ast/seq/seq_power_facet.cpp','primitive-root minimal divisor-period only'),
    'P6': ('src/ast/rewriter/guard_set.cpp','fresh string length scan after sorting only'),
    'P7': ('src/util/stx_search_tree.h','DFS child-result/purity aggregation only'),
    'P8': ('src/smt/theory_nseq.cpp','pending-hypothesis early acceptance/reset boundary only'),
    'P9': ('src/ast/simplifiers/seq_regular_simplifier.cpp','negative integral decimal thresholds only'),
    'P10': ('src/ast/rewriter/seq_rewriter.cpp','plus-repetition factor-count algebra only'),
}
changed=[]
for line in git('diff','--name-status',base,head,'--','src').decode().splitlines():
    status,path=line.split('\t',1)
    kind='test' if path.startswith('src/test/') else 'build' if path.endswith('CMakeLists.txt') else 'production'
    primary = [ident for ident,(source,scope) in previous_models.items() if source==path]
    changed.append(dict(path=path,change=status,kind=kind,previous_primary_model_ids=primary,
        prior_scope='Focused primary model(s), not file-wide verification' if primary else 'No first-batch primary model; prior context/range inspection may exist',
        candidate_ids=[c['id'] for c in candidates if c['path']==path]))
source_cache={}
for c in candidates:
    path=c['path']
    if path not in source_cache:
        raw=git('show',head+':'+path)
        text=raw.decode('utf-8')
        assert (repo/Path(path.replace('/','\\'))).read_text(encoding='utf-8')==text,path
        diff=git('diff','--unified=0',base,head,'--',path).decode()
        hunks=[]
        for start,count in re.findall(r'^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@',diff,re.M):
            count=int(count) if count else 1
            if count:
                hunks.append((int(start),int(start)+count-1))
        source_cache[path]=dict(raw=raw,lines=text.splitlines(),hunks=hunks)
    item=source_cache[path]
    start,end=c['span']
    assert 1<=start<=end<=len(item['lines']),(c['id'],start,end)
    c['changed_span_intersects']=any(not (end<a or start>b) for a,b in item['hunks'])
    c['eligibility']='changed-code candidate' if c['changed_span_intersects'] else 'unchanged helper context only'
    if not c['changed_span_intersects']:
        assert c['id']=='C04',(c['id'],'unexpected unchanged entry')
        c['priority']='context-only'
        c['status']='Unchanged implementation at pinned merge base: not eligible as a new-code property entry.'
        c['next_step']='Retain as dependency context only; select a genuinely changed caller before attributing an obligation to the c3mv delta.'

counts={k:sum(f['kind']==k for f in changed) for k in ('production','test','build')}
assert len(changed)==89 and counts==dict(production=64,test=20,build=5),counts
ledger=dict(head=head,master=master,merge_base=base,
    scope='Coverage mapping only. Candidates are not frozen selection, models or verdicts. Native source not executed.',
    counts=counts,files=changed,candidates=candidates,
    previous_models={ident:dict(path=path,scope=scope) for ident,(path,scope) in previous_models.items()},
    previous_batch='doc/nfv-audits/c3mv-71ec455a1',
    user_scope='Logical correctness and possible user-space crashes',
    limitations=['No exhaustive line-by-line inspection of all changed files',
                 'No native execution, build, sanitizer or regression run',
                 'Metadata and source provenance do not prove C++/Dafny correspondence'])
(session/'nfv2-coverage-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n',encoding='utf-8',newline='\n')
excerpts=[]
for path,item in source_cache.items():
    indices=sorted({i for c in candidates if c['path']==path for i in range(c['span'][0],c['span'][1]+1)})
    raw=item['raw']
    excerpts.append(dict(path=path,blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
        sha256=hashlib.sha256(raw).hexdigest(),line_count=len(item['lines']),worktree_matches=True,
        excerpts=[dict(line=i,text=item['lines'][i-1]) for i in indices]))
(session/'nfv2-coverage-source-inventory.json').write_text(json.dumps(dict(head=head,files=excerpts),indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='pass',changed_src_files=len(changed),counts=counts,
    unselected_changed_candidates=sum(c['changed_span_intersects'] for c in candidates),
    unchanged_context_entries=sum(not c['changed_span_intersects'] for c in candidates),candidate_source_files=len(excerpts),
    source_lines=sum(len(f['excerpts']) for f in excerpts)),indent=2))
