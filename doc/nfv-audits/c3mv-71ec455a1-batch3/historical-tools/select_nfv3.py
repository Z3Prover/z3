"""Freeze two new whole-property intents before any batch-3 model exists."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

root=Path(__file__).parent
repo=Path(r'C:\z3seq')
head='71ec455a18702fe695d0c924a535ff9f385bd58d'
master='c2460a558fc6fee3cf15cfebd2d3f642ebf77770'
base='437536cd64a544a1c329fc57d83e56e294fdf47c'
inventory_path=root/'nfv3-coverage-source-inventory.json'
assert hashlib.sha256(inventory_path.read_bytes()).hexdigest()=='d33911bd8dde877a572a5ad435e56574b46965c98e3a4836abc2e77392964824'
inventory=json.loads(inventory_path.read_text())
files={f['path']:f for f in inventory['files']}
def git(*args):return subprocess.check_output(['git',*args],cwd=repo,text=True,encoding='utf-8').strip()
def line(path,n):return next(e['text'] for e in files[path]['excerpts'] if e['line']==n)
def literal(word):return dict(bounds=list(range(len(word)+1)),literal=[True]*len(word))
def opaque(word):return dict(bounds=[0,len(word)],literal=[False])
def example(label,b,A,B,M,N,**fresh):
    a=opaque(A) if fresh.pop('opaqueA',False) else literal(A)
    c=opaque(B) if fresh.pop('opaqueB',False) else literal(B)
    inputs=dict(b=b,param=0,A=A,B=B,aBounds=a['bounds'],bBounds=c['bounds'],aLiteral=a['literal'],bLiteral=c['literal'],expA=M,expB=N,y1=[],y2=[],wFresh=[],iFresh=0,jFresh=0,p1Fresh=[],p2Fresh=[],kFresh=0,qFresh=0)
    inputs.update(fresh)
    return dict(label=label,inputs=inputs,status='unverified independent domain candidate; no model outcome')

power='src/ast/seq/seq_power_facet.cpp'
watch='src/util/stx_search_tree.h'
P18=dict(
 id='P18',coverage_candidate='C10-apply-word-identity',path=power,entry='power_trichotomy::apply',span=[455,579],
 intent_origin='source-inferred hypothesis from the changed function and its enumerator, not PR intent or source-confirmed correctness',
 quote_line=502,grounding_quote=line(power,502),
 inputs=dict(b='int: branch selector 0..9, including source direction',param='int: enumerated constant period, otherwise 0',A='seq<int>: original first base valuation',B='seq<int>: original second base valuation',aBounds='seq<int>: flattened token boundaries for A',bBounds='seq<int>: flattened token boundaries for B',aLiteral='seq<bool>: observed per-token is-unit-and-constant-character classification for A',bLiteral='seq<bool>: corresponding classification for B',expA='int: valuation of original first exponent',expB='int: valuation of original second exponent',y1='seq<int>: fresh f1/f4 word valuation',y2='seq<int>: fresh f4 word valuation',wFresh='seq<int>: fresh f2 root valuation',iFresh='int: fresh f2 exponent valuation',jFresh='int: fresh f2 exponent valuation',p1Fresh='seq<int>: fresh f3 first word valuation',p2Fresh='seq<int>: fresh f3 second word valuation',kFresh='int: fresh f3 exponent valuation',qFresh='int: fresh f4 exponent valuation'),
 outputs=dict(constraints_ok='bool: conjunction of interpreted side conditions actually added by this branch',fromWord='seq<int>: interpreted substituted term',toWord='seq<int>: interpreted replacement'),
 semantics=[
  'Words are seq<int> over an uninterpreted equality alphabet. Power(word,k) is empty for k<=0 and repeated concatenation otherwise. Integer exponents are unbounded mathematical integers, not unsigned.',
  'Input token boundaries begin at 0, end at word length, are nondecreasing, and have one more element than classification flags. A true literal flag requires a one-character segment. False allows any segment length, including zero; it does not assert inequality of word values.',
  'Body-defined ConstantWord follows the source reset/loop/early-return/append/nonempty-return behavior using the observed literal flags and corresponding one-character segments. Its flags are abstract syntactic observations, not guessed from word valuations.',
  'Compute direction exactly from b<5; select X,M,Y,N and the associated token views by swapping original inputs in the mirrored direction. Apply the source <= or strict < guard to the lengths of truncated word powers, not to M*|X| for negative M.',
  'Fresh values are universally free input valuations; constraints_ok accumulates the actual arithmetic constraints and word equations instead of assuming they are always true. It does not assert native solver reachability.',
  'f0 adds M<=0 OR X empty and emits X^M -> epsilon. f1 adds N>=1 and Y=X^M.y1, with residual y1.Y^(N-1).',
  'f2 adds M>=1; use primitive_root(gx?X:Y) when either ConstantWord succeeds, derive existing i/j by the actual length division, otherwise use fresh root. For each missing i/j add >=1 and the respective base=root^exponent equation. Residual is root^(j*N-i*M). Never assume j*N-i*M>=0 when root is empty.',
  'f3 adds M,N>=2. param>0 uses l1=|X| mod param, p1=suffix(X,l1), p2=X[l1..param). Otherwise use fresh p1,p2 and add X=(p1.p2)^kFresh with a trailing p1. Do not restrict kFresh>=0. Add Y=X^(M-1).p1.p2 and preserve the complete residual p2.p1.X^(M-2).p1.p2.Y^(N-2).',
  'f4 adds M=1,qFresh>=0,qFresh+1<=N, Y=y1.y2 and X=Y^qFresh.y1. Preserve residual y2.Y^(N-qFresh-1).',
  'All nonzero cases emit Y^N -> X^M.residual. Preserve every branch computation, including both constant and fresh-root variants; do not select separate properties per case.'
 ],
 domain=[
  dict(predicate='0<=b<10; 0<=param<4294967296; valid token boundary/classification views; each token-vector length <4294967296',origin='inferred',optional=False,justification='enumerate:414-451; unsigned selector/period/vector lengths and flattened token value projection'),
  dict(predicate='Non-f3 branches have param=0. In f3, ConstantWord(X) iff param>0; when param>0, 0<param<|X| and body-defined HasPeriod(X,param).',origin='inferred',optional=False,justification='enumerate:443-448: constant X produces period-param branches; nonconstant X produces param=0'),
  dict(predicate='For f2 with both bases constant, X.Y==Y.X.',origin='inferred',optional=False,justification='enumerate:441-442 rejects noncommuting constant bases; omitting this caller guard would invent invalid common-root behavior'),
  dict(predicate='For constant f3 with constant Y: |Y|>=U32(|X|+param) and U32(|Y|-param) mod |X|==0, where U32(v)=v mod 4294967296.',origin='inferred',optional=False,justification='enumerate:447 unsigned additions/subtractions retained, not silently lifted to nonwrapping mathematics'),
  dict(predicate='Every successful ConstantWord output has length <4294967296.',origin='inferred',optional=False,justification='unsigned zstring length and one-character-per-successful-token representation; not a bound on arbitrary opaque-word valuations')
 ],
 whole_positive_property='!constraints_ok || fromWord == toWord',
 required_helpers=[
  dict(name='Power',contract='Truncated signed word exponentiation by recursive concatenation with a body; algebraic lemmas must be verified, not assumed.',source='src/ast/seq/seq_power_facet.cpp:110-142; src/ast/seq_decl_plugin.h:60-67,315-320'),
  dict(name='ConstantWord',contract='Exact partial accumulation/early-return semantics on the projected flattened token view; successful output equals the complete base and is nonempty.',source=power+':271-281'),
  dict(name='HasPeriod',contract='Actual pairwise-offset scan, with checked index/unsigned domains.',source=power+':283-289'),
  dict(name='PrimitiveRoot',contract='Actual least-divisor/has_period loop and fallback. Prove any repetition/common-root facts required by the original whole goal; no bodyless common-root oracle.',source=power+':291-297'),
  dict(name='Word/slice/power construction',contract='Actual branch concatenation order and constant suffix/subslice, with all index domains established. Arithmetic normalization is interpreted mathematically, not asserted as a native rewriter theorem.',source=power+':94-108,476-497,510-579')
 ],
 omitted_effects=[
  'No proof of full arithmetic-rewriter/AST equivalence, tokenization equivalence or C++/Dafny correspondence; flattened token values and syntactic literal flags are explicit input observations.',
  'Freshness, AST identities/sorts, add_power registration, dependency propagation, callback lifetime/reallocation effects, allocations and later solver search are outside this word-semantic projection.',
  'The enumerator prefix/alphabet feasibility filters and trigger eligibility are not reconstructed; only necessary constant-root/period caller guards are retained. The model admits additional branches, not fewer. At least one source exponent expression may be syntactically symbolic even when its independent valuation is a numeral.',
  'No branch exhaustiveness/completeness claim, no native reachability claim, and no source-confirmed crash/result. An unresolved complete proof stays unresolved rather than becoming scalar-count success.'
 ],
 domain_examples=[
  example('f0 negative exponent',0,[97],[98],-1,1),
  example('f1 residual',1,[97],[97,98],1,2,y1=[98]),
  example('f2 empty fresh root and negative N',2,[],[],2,-1,opaqueA=True,opaqueB=True,iFresh=1,jFresh=1),
  example('f2 two commuting constants with different powers',2,[97,97],[97,97,97],1,1),
  example('f3 symbolic decomposition with negative k',3,[97],[97,97,98],2,2,opaqueA=True,opaqueB=True,p1Fresh=[97],p2Fresh=[98],kFresh=-1),
  example('f3 constant period not dividing length',3,[97,98,97,98,97],[97,98,97,98,97,97,98],2,2,param=2),
  example('f4 split residual',4,[97,98,97],[97,98],1,2,y1=[97],y2=[98],qFresh=1),
  example('mirrored f1 strict length guard',6,[97,98],[97],2,1,y1=[98])
 ],
 outcome='not modeled or checked')

P19=dict(
 id='P19',coverage_candidate='C12-rewatch-representation',path=watch,entry='try_rewatch',span=[681,708],
 intent_origin='source-inferred documented local return/state contract, NOT unsat-core semantic soundness',
 quote_line=688,grounding_quote=line(watch,688),
 inputs=dict(lits='seq<int>: current core store IDs',canonicalPointers='seq<int>: store-ID-to-canonical-pointer identity table',pointeeValue='seq<int>: pointer-identity-to-semantic-equivalence-class table',activePointers='seq<int>: currently active live pointer identities',oldWatch='int: original index into lits',coreIdx='int: this core ID',bucketWidths='seq<int>: watch-list bucket lengths',bucketItems='seq<int>: concatenated bucket core IDs'),
 outputs=dict(moved='bool: source return value',newWatch='int: updated core watch index',widthsOut='seq<int>: resulting bucket lengths',itemsOut='seq<int>: resulting flattened bucket core IDs'),
 domain=[
  dict(predicate='0<|lits|<4294967296; 0<=oldWatch<|lits|; every lits[i] indexes canonicalPointers; every canonical pointer and active pointer indexes pointeeValue; all vector lengths and represented IDs are unsigned-32 values.',origin='inferred',optional=False,justification='core/store/vector indexing and unsigned source representations'),
  dict(predicate='SemanticActive(canonicalPointers[lits[oldWatch]],activePointers,pointeeValue).',origin='inferred',optional=False,justification='source precondition comment:681-683; cache_lookup uses semantic find:716-735'),
  dict(predicate='Canonical pointer identities are pairwise distinct, and their pointeeValue classes are pairwise distinct.',origin='inferred',optional=False,justification='constraint_store::intern clones only after semantic find fails:600-610; one canonical owner per class'),
  dict(predicate='Each bucket width is nonnegative; widths sum to |bucketItems|; bucket lengths, each item and coreIdx fit unsigned-32. No requirement that canonical pointers equal their live semantic aliases; old watch bucket may be absent as handled by unwatch.',origin='inferred',optional=False,justification='value-state projection of the vector-of-vectors and source guarded unwatch/resize operations:664-678')
 ],
 semantics=[
  'Pointer equality is identity equality. SemanticActive is existence of an active pointer with equal pointeeValue, not membership of canonical identity.',
  'Read old_id=lits[oldWatch]; scan i from 0, skipping oldWatch. Test actual identity membership canonicalPointers[lits[i]] in activePointers, without substituting semantic equality.',
  'On first identity-absent other entry: unwatch(old_id,coreIdx), assign newWatch=i, watch(lits[i],coreIdx), return true. Otherwise preserve old state and return false.',
  'Unwatch removes the first matching coreIdx in the specified bucket if present, or is a no-op if bucket out of range or core absent. Watch grows buckets with empty rows then appends one coreIdx. Preserve order and all unaffected rows.',
  'The flattened representation uses bucketWidths plus concatenated bucketItems, with body-defined prefix offsets/slice/delete/append helpers, not an unconstrained state-update oracle.'
 ],
 whole_positive_property='(moved == (exists i :: 0<=i<|lits| && !SemanticActive(canonicalPointers[lits[i]],activePointers,pointeeValue))) AND (0<=newWatch<|lits|) AND (if moved then newWatch!=oldWatch AND !SemanticActive(canonicalPointers[lits[newWatch]],activePointers,pointeeValue) AND (widthsOut,itemsOut)==Watch(Unwatch(bucketWidths,bucketItems,lits[oldWatch],coreIdx),lits[newWatch],coreIdx) else newWatch==oldWatch AND widthsOut==bucketWidths AND itemsOut==bucketItems)',
 required_helpers=[
  dict(name='IdentityContains',contract='Body-defined equality scan over actual pointer identities.',source='src/util/vector.h:579-589'),
  dict(name='SemanticActive',contract='Body-defined existence/scan of equal pointeeValue classes; explicit equivalence-class abstraction, not a proof of arbitrary constraint_i::equals semantics.',source=watch+':575-610,716-735'),
  dict(name='Watch and Unwatch',contract='Body-defined exact bucket resize/append and first-match removal; no assumed helper effects.',source=watch+':664-678'),
  dict(name='Bucket offsets and slice updates',contract='Bodies preserve the explicit flattened value representation and unaffected row order; bounds require independent verification.',source=watch+':667-668,676-678')
 ],
 omitted_effects=[
  'This is a documented semantic-presence return contract plus complete local watch updates, not a proof that any cached core is unsatisfiable or that filtering conflict dependencies is sound.',
  'Container updates describe successful normal-return mathematical value-state resize/erase/append. Native allocation failure, capacity growth/counter overflow and memory safety are not modeled or proved.',
  'The source interface calls arbitrary constraint equals/hash; pointeeValue abstracts their semantic equivalence classes for consistent equation-like objects, with no native alias/lifetime, hash-table implementation, global cache-lookup or caller scheduling proof.',
  'A verified violation of the semantic-presence converse is a missed-hit/control-contract result only. Do not label it false SAT/UNSAT, a native crash, an exploitable vulnerability or an executed C++ counterexample.',
  'The input-example alias pattern is a candidate diagnostic, not a claimed counterexample until the complete conjunction is mechanically negated and independently verified with all inputs pinned.'
 ],
 domain_examples=[
  dict(label='two semantically active live aliases with distinct canonical identities',inputs=dict(lits=[0,1],canonicalPointers=[0,1],pointeeValue=[10,20,10,20],activePointers=[2,3],oldWatch=0,coreIdx=0,bucketWidths=[1,0],bucketItems=[0]),status='unverified candidate domain; not yet a counterexample'),
  dict(label='genuinely absent other literal and missing destination bucket',inputs=dict(lits=[0,1],canonicalPointers=[0,1],pointeeValue=[10,20,10],activePointers=[2],oldWatch=0,coreIdx=0,bucketWidths=[1],bucketItems=[0]),status='unverified candidate domain'),
  dict(label='singleton semantically active via alias',inputs=dict(lits=[0],canonicalPointers=[0],pointeeValue=[10,10],activePointers=[1],oldWatch=0,coreIdx=7,bucketWidths=[],bucketItems=[]),status='unverified candidate domain')
 ],
 outcome='not modeled or checked')

assert 'Each case asserts exactly' in P18['grounding_quote']
assert 'no absent literal' in P19['grounding_quote']
for p in (P18,P19):
    p['source_blob']=files[p['path']]['blob']
    p['original_positive_property_frozen']=True
    assert all(set(w['inputs'])==set(p['inputs']) for w in p['domain_examples'])
    delta=git('diff','--unified=0',master,head,'--',p['path'])
    ranges=[]
    for start,count in re.findall(r'@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@',delta):
        ranges.append((int(start),int(count or 1)))
    p['changed_anchors']=[i for i in range(p['span'][0],p['span'][1]+1) if any(s<=i<s+n for s,n in ranges)]
    assert p['changed_anchors'] and p['quote_line'] in p['changed_anchors']
selection=dict(batch=3,head=head,master=master,previous_master='d738f81eab9af1468394664a812fe4310ae8e1fa',merge_base=base,nfv_upstream='599726579274cfeb1c0915414b911371527a9870',scope='Manual source-only selection of two new whole-function model obligations, not outcomes or hosted-driver output',properties=[P18,P19],selection_policy='Two meaningful distinct changed entries, no quota, no branch/conjunct splitting. P18 spans all apply cases and both constant/fresh forms. P19 preserves the documented return contract AND local watch-state effects.',deferred=['P13 complete request-queue proof remains unresolved','C11 caller-justified global substitution-DAG/termination proof','C12 semantic sufficiency of cached dependency-filtered cores','Power branch completeness/exhaustiveness','Native reachability/allocation of the P12 giant-pattern witness'],not_selected=['Duplicate primitive_root property already covered by first-batch P5','Separate f1/f2/f3/f4 identity properties for the same selected apply entry','Eligibility-only predicate as a substitute for complete cache soundness','Fuel-bounded elimination success as a substitute for termination','Extra small properties to fill a ten-property quota'],evidence=dict(coverage_inventory_sha256=hashlib.sha256(inventory_path.read_bytes()).hexdigest(),coverage_ledger_sha256=hashlib.sha256((root/'nfv3-coverage-ledger.json').read_bytes()).hexdigest(),p12_trace_sha256=hashlib.sha256((root/'nfv3-p12-source-trace.md').read_bytes()).hexdigest()),pre_freeze_validation_history=[dict(result='failed selection-span assertion, not a verifier check',exception='AssertionError',cause='try_rewatch intent quote is an attached precondition/return-contract comment outside its initial body-only span',correction='Extend the faithful source slice to lines 681-708, covering the attached contract and whole body; both entry body and quote are independently changed. No property/domain was weakened; no model existed.')],new_models=0,new_verifier_attempts=0)
out=root/'nfv3-selection.json'
frozen=root/'nfv3-selection-freeze.json'
assert not out.exists() and not frozen.exists(), 'Do not overwrite a frozen selection'
out.write_text(json.dumps(selection,indent=2)+'\n',encoding='utf-8',newline='\n')
digest=hashlib.sha256(out.read_bytes()).hexdigest()
frozen.write_text(json.dumps(dict(selection_file=out.name,sha256=digest,stage='nfv3-select',state='intent frozen before any batch-3 model implementation',selected_ids=['P18','P19'],selected_entries=[p['entry'] for p in selection['properties']],policy='Do not weaken goals/domains after modeling; draft translation repairs are disclosed, then seal computation and helper contracts before original checks.'),indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='pass',selected=2,ids=['P18','P19'],witness_examples=[len(p['domain_examples']) for p in selection['properties']],selection_sha256=digest,freeze_sha256=hashlib.sha256(frozen.read_bytes()).hexdigest(),new_models=0,new_checks=0),indent=2))
