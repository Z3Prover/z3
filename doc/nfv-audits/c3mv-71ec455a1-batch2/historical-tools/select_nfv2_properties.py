"""Freeze batch-2 intent before writing any translated Dafny implementation."""
import hashlib
import json
from pathlib import Path
import subprocess

repo = Path(r'C:\z3seq')
session = Path(__file__).parent
head = '71ec455a18702fe695d0c924a535ff9f385bd58d'
master = 'd738f81eab9af1468394664a812fe4310ae8e1fa'
base = '437536cd64a544a1c329fc57d83e56e294fdf47c'
upstream = '599726579274cfeb1c0915414b911371527a9870'

def item(ident, candidate, path, entry, span, quote, inputs, domain, property_text, helpers, limits, witness):
    return dict(id=ident,coverage_candidate=candidate,path=path,entry=entry,span=span,
        grounding_quote=quote,inputs=inputs,domain=domain,whole_positive_property=property_text,
        required_helpers=helpers,correspondence_limits=limits,domain_example=witness,
        outcome='not modeled or checked',intent_origin='source-inferred hypothesis, not a quotation of PR intent')

properties = [
    item('P11','C01','src/ast/seq/seq_ncontains_facet.cpp','ncontains_propagation::propagate',[264,291],
        '// every position is a determined mismatch: the needle',
        'X,Y,Z: seq<int>; a,b: int; three distinct non-unit AST identities separate from word valuations',
        ['a != b', '|X| + 1 + |Y| < 2147483648', '|X| + 1 + |Z| < 2147483648',
         'one active obligation [X,unit(a),Y] not-contains [X,unit(b),Z]; no earlier conflict or substitution'],
        '!discharged || !WordContains(X + [a] + Y, X + [b] + Z)',
        ['Faithful pointer/kind-aware compare_alignment, not comparison of word valuations',
         'Complete token-window scan and actual all-mismatch discharge decision',
         'Body-defined word containment and valuation/flattening helpers'],
        ['Specific token shape, not all containment propagation',
         'No preceding facet/caller reachability, native result, source fix or crash claim',
         'This is a different branch from the published prefix-pruning model'],
        dict(X=[97,97],Y=[98],Z=[],a=97,b=98)),
    item('P12','C02','src/ast/seq/seq_replace_all_facet.cpp','replace_all_split::apply_case',[215,229],
        'if (c >= 2 * p.length() + 2)',
        'pattern_length, case_number: int representing 32-bit unsigned values; output admitted: bool',
        ['1 <= pattern_length <= 4294967295', '1 <= case_number <= 4294967295',
         'the selected source prelude has a valid active replacement obligation and nonempty literal pattern'],
        'admitted == (case_number < 2 * pattern_length + 2), with the specification arithmetic mathematical and the source computation modulo 4294967296',
        ['Body-defined unsigned-32 arithmetic for the actual expression 2*p.length()+2',
         'Source guard observation only: admitted iff the guard does not return false'],
        ['Checks branch-number admission only, not replacement semantics, iterator exhaustion or all index bounds',
         '32-bit unsigned target model; no assumption that 2*pattern_length+2 does not wrap',
         'No huge literal allocation is performed or proved possible. Any model refutation remains conditional on length/source applicability',
         'Caller checks only nonempty literal pattern; inspected zstring representation exposes unsigned length, not an asserted small-pattern bound'],
        dict(pattern_length=2147483647,case_number=1)),
    item('P13','C03','src/ast/seq/seq_req_facet.cpp','req_propagation::propagate',[61,118],
        'continue; // re-examine same index (now the next request)',
        'queue: seq<int> request IDs; is_eq: seq<bool>; verdict: seq<int>; start: int; outputs queue_out, qhead_out, conflict',
        ['0 <= start <= |queue| < 4294967296', '|is_eq| == |verdict| < 4294967296',
         'every queue ID indexes is_eq/verdict', 'every verdict is -1(false), 0(unknown), or 1(true)'],
        'Let stop=FirstConflict(queue,is_eq,verdict,start), or |queue| if absent. conflict == (stop < |queue|) AND queue_out == queue[..start] + FilterUnknown(queue[start..stop],verdict) + queue[stop..] AND qhead_out == (if conflict then start else |queue_out|) AND 0 <= qhead_out <= |queue_out|',
        ['Body-defined first-conflict and stable-unknown-filter specification helpers',
         'Actual mutable queue scan, erase, same-index continuation and qhead adjustment'],
        ['Bisimulation results are explicit environment observations for bookkeeping, not assumed proofs of regex equivalence',
         'Prior prefix below start is deliberately not rescanned, as in source',
         'No native allocator/AST lifetime or full trail-stack proof; scalar/vector value state only'],
        dict(queue=[0,1,2,3],is_eq=[True,False,True,True],verdict=[1,0,-1,1],start=0)),
    item('P14','C06','src/ast/simplifiers/seq_regular_simplifier.cpp','regular_compiler::preimage',[774,791],
        'result = join(yes, nullable(r) ? length(0, k) : empty);',
        'word, allowed_characters: seq<int>; accepts_empty,last_index: bool; k: int; output rewritten_accepts: bool',
        ['0 <= k <= 64', '|word| < 4294967296',
         'selected str.at fixed-nonnegative-index branch or exactly str.len(word)-1 branch; nullable helper succeeds'],
        'rewritten_accepts == TargetAccepts(StrAt(word, if last_index then |word|-1 else k), allowed_characters, accepts_empty)',
        ['Body-defined str.at with negative/out-of-range behavior and guarded indexing',
         'Body-defined target membership on epsilon and singleton words',
         'Source regex cat/meet/union/length semantics for both selected branches; no opaque assumed rewrite result'],
        ['Only epsilon/single-character membership of the arbitrary target language matters because str.at has length at most one',
         'No proof of general regex implementation, nullable decision procedure, extraction/preimage branches or caller budget behavior',
         'Integer alphabet abstracts equality of valid characters; no unsupported character-arithmetic claims'],
        dict(word=[],allowed_characters=[97],accepts_empty=True,last_index=True,k=0)),
    item('P15','C07','src/solver/assertions/asserted_formulas.cpp','asserted_formulas::simplify_replace_contains',[355,400],
        '// A single-character observation is unchanged when neither replacement operand contains it.',
        'word,needle,replacement: seq<int>; character: int; output rewritten_contains: bool',
        ['!HasCharacter(needle,character)', '!HasCharacter(replacement,character)',
         '|word|,|needle|,|replacement| < 2147483648',
         'selected admitted rewrite: nseq, no proof production/quantifiers, and no global blocked-replacement abort'],
        'rewritten_contains == HasCharacter(ReplaceFirst(word,needle,replacement),character)',
        ['Actual rewritten observation is HasCharacter(word,character)',
         'Body-defined ground ReplaceFirst from zstring::replace, including empty needle, no match, first-only replacement, matching loop and copy/skip behavior',
         'Body-defined character occurrence; preserve the real whole property, not merely a sufficient no-match case'],
        ['This is the local observation rewrite; graph traversal, ancestor blocking, sharing, proof/model conversion and marks/lifetimes remain unproved',
         'Character/string denotation only, not AST or allocator memory safety',
         'Length bounds preserve selected unsigned helper arithmetic; do not assume nonempty needle'],
        dict(word=[97,98],needle=[],replacement=[99],character=98)),
    item('P16','C03 helper','src/ast/seq/seq_eq_facet.h','vector_erase_trail<T>::undo',[78,91],
        'm_vec[m_idx] = std::move(m_value);',
        'original: seq<int>; index: int; output restored: seq<int>',
        ['0 <= index < |original| < 4294967296',
         'the trail constructor records original[index] before exactly that slot is erased, as in req_facet::remove'],
        'restored == original, with all modeled push/shift/store accesses in bounds',
        ['Body-defined actual vector erase-by-left-shift and pop',
         'Record the erased value before mutation',
         'Actual undo: push saved value, right-shift backwards, then write the saved slot; never replace the whole output with original'],
        ['Value elements abstract movable request records; move/destructor/AST references and allocation failures are outside the model',
         'Checks this new helper and its selected erase/undo path, not all apply_subst/dependency or nested trail behavior',
         'Bounds are real index/size requirements, not assumptions that undo succeeds'],
        dict(original=[10,20,30],index=1)),
    item('P17','C09','src/ast/rewriter/seq_regex_witness.cpp','regex_witness::accepts',[154,166],
        'if (value == (conjunction ? l_false : l_true))',
        'conjunction: bool; child_verdicts: seq<int>; output verdict: int; encoding -1=false,0=unknown,1=true',
        ['every child verdict is -1,0,or 1', '|child_verdicts| < 4294967296',
         'selected nonempty-ground-word Boolean regex constructor branch after earlier source guards'],
        'verdict == (if conjunction then (if -1 in child_verdicts then -1 else if 0 in child_verdicts then 0 else 1) else (if 1 in child_verdicts then 1 else if 0 in child_verdicts then 0 else -1))',
        ['Preserve source identity value, short-circuit decisive result, unknown accumulation, and loop order',
         'Body-defined membership/aggregation specification; explicit observed child verdicts rather than hidden convenient child results'],
        ['Boolean aggregation only; no work-counter/depth-budget proof, full regex acceptance, derivative or ground-slicing correctness',
         'Resource failures may appear as unknown child observations, but their occurrence/cost is not modeled',
         'This is not source-level regex soundness or native crash verification'],
        dict(conjunction=True,child_verdicts=[1,0,1])),
]

context = {
    'src/ast/seq/seq_ncontains_facet.cpp': [(38,50),(128,141),(232,301)],
    'src/ast/seq/seq_replace_all_facet.cpp': [(215,229),(271,290)],
    'src/ast/seq/seq_replace_all_facet.h': [(105,122)],
    'src/smt/theory_nseq.cpp': [(592,611)],
    'src/util/zstring.h': [(30,75)],
    'src/util/buffer.h': [(28,57),(189,208)],
    'src/ast/seq/seq_req_facet.cpp': [(26,44),(61,120)],
    'src/ast/seq/seq_req_facet.h': [(43,59),(68,101)],
    'src/ast/seq/seq_eq_facet.h': [(76,123)],
    'src/util/vector.h': [(398,425),(447,456)],
    'src/util/trail.h': [(33,53),(382,427)],
    'src/ast/simplifiers/seq_regular_simplifier.cpp': [(255,273),(577,597),(774,791)],
    'src/solver/assertions/asserted_formulas.cpp': [(317,415)],
    'src/util/zstring.cpp': [(120,143)],
    'src/ast/rewriter/seq_regex_witness.cpp': [(136,166)],
}
records={}
full_texts={}
for path,ranges in context.items():
    raw=subprocess.check_output(['git','show',head+':'+path],cwd=repo)
    full_texts[path]=raw.decode('utf-8')
    lines=raw.decode('utf-8').splitlines()
    assert (repo/Path(path.replace('/','\\'))).read_text(encoding='utf-8')==raw.decode('utf-8'),path
    indices=sorted({i for start,end in ranges for i in range(start,end+1)})
    assert 1<=indices[0]<=indices[-1]<=len(lines),path
    records[path]=dict(path=path,blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
        sha256=hashlib.sha256(raw).hexdigest(),excerpts=[dict(line=i,text=lines[i-1]) for i in indices])
for prop in properties:
    entries=records[prop['path']]['excerpts']
    hits=[e['line'] for e in entries if e['text'].strip()==prop['grounding_quote']]
    assert len(hits)==1,(prop['id'],hits)
    assert prop['span'][0]<=hits[0]<=prop['span'][1],prop['id']
    prop['quote_line']=hits[0]
    prop['source_blob']=records[prop['path']]['blob']
    if not prop['id']=='P16':
        assert prop['entry'] in full_texts[prop['path']] or prop['entry']=='regular_compiler::preimage',prop['id']
assert len(properties)==7
selection=dict(batch=2,head=head,master=master,merge_base=base,nfv_upstream=upstream,
    scope='Manual local NFV-methodology audit: seven new selected whole properties, not verdicts or official hosted-driver output',
    numbering='P11-P17 are distinct from the immutable first-batch P1-P10',properties=properties,
    deferred=['C05 callback-driven coherence: require a justified callback/object-lifetime model rather than a value-only proxy',
              'C08 full substitution/dependency/qhead undo: caller aliasing and dependency graph contracts need further tracing',
              'C10 full trichotomy word branches; C11 substitution acyclicity; C12 cache/core entailment; C13 complete model reconstruction',
              'C14 split positive-decimal/length-bound properties; C04 unchanged derivative helpers are context only'])
target=session/'nfv2-selection.json'
raw=(json.dumps(selection,indent=2)+'\n').encode('utf-8')
target.write_bytes(raw)
sources=session/'nfv2-selection-source-inventory.json'
sources.write_text(json.dumps(dict(head=head,files=list(records.values())),indent=2)+'\n',encoding='utf-8',newline='\n')
freeze=dict(scope='Intent selection freeze only; model computation/contracts are frozen later before original-property verification',
    selection_sha256=hashlib.sha256(raw).hexdigest(),source_inventory_sha256=hashlib.sha256(sources.read_bytes()).hexdigest(),
    property_ids=[p['id'] for p in properties],count=len(properties),no_dafny_implementation_created_by_this_stage=True)
(session/'nfv2-selection-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='pass',selected=freeze['property_ids'],source_files=len(records),
    selection_sha256=freeze['selection_sha256'],stage='intent frozen; no new model verdicts'),indent=2))
