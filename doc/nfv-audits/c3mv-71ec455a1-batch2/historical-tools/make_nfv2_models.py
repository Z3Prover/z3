"""Translate the frozen batch-2 slices without executing production source."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).parent
OUT = ROOT / 'nfv2-models'
HEAD = '71ec455a18702fe695d0c924a535ff9f385bd58d'
selection = json.loads((ROOT/'nfv2-selection.json').read_text(encoding='utf-8'))
freeze = json.loads((ROOT/'nfv2-selection-freeze.json').read_text(encoding='utf-8'))
assert hashlib.sha256((ROOT/'nfv2-selection.json').read_bytes()).hexdigest() == freeze['selection_sha256']
selected = {p['id']:p for p in selection['properties']}
aliases = dict(nc='src/ast/seq/seq_ncontains_facet.cpp',ra='src/ast/seq/seq_replace_all_facet.cpp',
    req='src/ast/seq/seq_req_facet.cpp',eqh='src/ast/seq/seq_eq_facet.h',vec='src/util/vector.h',
    reg='src/ast/simplifiers/seq_regular_simplifier.cpp',af='src/solver/assertions/asserted_formulas.cpp',
    zs='src/util/zstring.cpp',wit='src/ast/rewriter/seq_regex_witness.cpp')
sources = {}
properties = []

def add(pid, entry, template, witnesses, descriptions, limits):
    chosen = selected[pid]
    result=[]
    context={}
    helper_tags={}
    current=[]
    for row in template.strip().splitlines():
        refs,code=row.split('|',1)
        if refs=='s':
            result.append('// synth: specification, checked proof annotation, or structural delimiter')
            current=[]
        else:
            current=[]
            for ref in refs.split(','):
                alias,number=ref.split(':')
                path=aliases[alias]
                number=int(number)
                if path not in sources:
                    sources[path]=subprocess.check_output(['git','show',HEAD+':'+path],text=True,encoding='utf-8').splitlines()
                result.append(f'// src: {path}:{number} | {sources[path][number-1].strip()}')
                context.setdefault(path,set()).add(number)
                current.append(dict(path=path,line=number))
        match=re.match(r'(function|predicate|method|lemma) (\w+)\(',code)
        if match and match[2]!=entry:
            helper_tags[match[2]]=dict(kind=match[1],tags=current)
        result.append(code)
    model='\n'.join(result)+'\n'
    signature=model[model.index('method '+entry):].split('\n{',1)[0]
    requires=re.findall(r'^\s*requires (.+)$',signature,re.M)
    ensures=re.findall(r'^\s*ensures (.+)$',signature,re.M)
    assert set(descriptions)==set(helper_tags),(pid,set(descriptions)^set(helper_tags))
    environment=[]
    for name,data in helper_tags.items():
        first=re.search(r'^(?:function|predicate|method|lemma) '+re.escape(name)+r'\(',model,re.M).start()
        header=model[first:model.index('\n{',first)]
        environment.append(dict(name=name,kind=data['kind'],description=descriptions[name],source=data['tags'],
            requires=re.findall(r'^\s*requires (.+)$',header,re.M),
            ensures=re.findall(r'^\s*ensures (.+)$',header,re.M),
            contract_status='body-defined obligations, not trusted axioms or assumed helper results'))
    assumptions=[]
    for clause in requires:
        optional=(pid=='P11' and clause.startswith('|')) or (pid=='P14' and clause.startswith('|word|'))
        description=('Conservative additional interpreted-word length restriction, not a source guard; try removal in accepted-refutation follow-ups.' if optional
                     else 'Frozen selected-slice applicability / guarded data domain; not necessarily a native caller check: '+clause)
        assumptions.append(dict(clause=clause,origin='inferred',optional=optional,description=description))
    metadata=dict(id=pid,title=chosen['whole_positive_property'],path=chosen['path'],entry_point=entry,
        origin='source-inferred hypothesis',quote=chosen['grounding_quote'],original_ensures=ensures,
        assumptions=assumptions,
        source_lines=sorted(context[chosen['path']]),source_span=chosen['span'],required_context=sorted(context),
        source_tags={p:sorted(lines) for p,lines in context.items()},witnesses=witnesses,
        environment=environment,
        correspondence='Manual focused translation, not a C++ equivalence/native safety proof. '+limits,
        frozen_selection_sha256=freeze['selection_sha256'],frozen_intent=chosen,
        provenance='Exact source tags/metadata checked locally; full upstream extraction/span/equivalence gates not run.',
        sha256=hashlib.sha256(model.encode()).hexdigest())
    properties.append(metadata)
    (OUT/(pid+'.dfy')).write_text(model,encoding='utf-8',newline='\n')

OUT.mkdir(exist_ok=True)

add('P11','DischargeEntry',r'''
nc:154|function WordContains(h: seq<int>, n: seq<int>): bool
s|{
nc:154|  exists i :: 0 <= i <= |h| && i + |n| <= |h| && h[i..i+|n|] == n
s|}
nc:128|method AlignmentEntry() returns (verdict: int)
s|  ensures verdict == -1
s|{
nc:131|  var h := [0,3,1];
nc:132|  var n := [0,4,2];
nc:135|  var unit := [false,false,false,true,true];
nc:129|  var unknown := false;
nc:130|  var k := 0;
nc:130|  while k < |n|
s|    invariant 0 <= k <= 1
s|    invariant !unknown
s|    decreases |n| - k
s|  {
nc:131|    var ht := h[k];
nc:132|    var nt := n[k];
nc:133|    if ht == nt {
nc:134|      k := k + 1;
nc:134|      continue;
s|    }
nc:135|    if !unit[ht] || !unit[nt] {
nc:136|      verdict := 0; return;
s|    }
nc:137|    if ht != nt {
nc:138|      verdict := -1; return;
s|    }
nc:139|    unknown := true;
nc:130|    k := k + 1;
s|  }
nc:141|  verdict := if unknown then 0 else 1;
s|}
nc:201|method DischargeEntry(X: seq<int>, Y: seq<int>, Z: seq<int>, a: int, b: int) returns (discharged: bool)
s|  requires a != b
s|  requires |X| + 1 + |Y| < 2147483648
s|  requires |X| + 1 + |Z| < 2147483648
s|  ensures !discharged || !WordContains(X + [a] + Y, X + [b] + Z)
s|{
nc:264|  var h_size := 3;
nc:265|  var n_size := 3;
nc:266|  var has_window := h_size >= n_size;
nc:267|  var max_pos := if has_window then h_size - n_size else 0;
nc:268|  var found_match := false;
nc:269|  var first_undef_pos := max_pos + 1;
nc:270|  var pos := 0;
nc:270|  while has_window && pos <= max_pos
s|    invariant 0 <= pos <= 1
s|    invariant !found_match && first_undef_pos == 1
s|    decreases 1 - pos
s|  {
nc:271|    var al := AlignmentEntry();
nc:272|    if al == 1 {
nc:273|      found_match := true;
nc:274|      break;
s|    }
nc:276|    if al == 0 && first_undef_pos > max_pos {
nc:277|      first_undef_pos := pos;
s|    }
nc:270|    pos := pos + 1;
s|  }
nc:281|  if found_match {
nc:282,nc:283|    discharged := false; return;
s|  }
nc:285|  if has_window && first_undef_pos > max_pos {
nc:288|    discharged := true; return;
s|  }
nc:293|  discharged := false;
s|}
''',[dict(X=[97,97],Y=[98],Z=[],a=97,b=98)],
    dict(WordContains='Body-defined interpreted word-infix observation, not token containment.',
         AlignmentEntry='Actual compare_alignment loop specialized to the sole fixed window: AST IDs X=0,Y=1,Z=2,unit(a)=3,unit(b)=4. a!=b makes the two constant units distinct independently of their word valuations.'),
    'Only the all-mismatch discharge branch and stated token shape. Source AST identities remain distinct even when word values coincide/are empty. Earlier conflicts/substitutions, later processing, dependencies/trailing, heap allocation and native results excluded. Integer characters are equality-only alphabet abstractions. discharged observes source deactivation, not its enum return.')

add('P12','AdmissionEntry',r'''
ra:225|function Unsigned32(value: int): int
s|  requires 0 <= value
s|  ensures 0 <= Unsigned32(value) < 4294967296
s|{
ra:225|  value % 4294967296
s|}
ra:215|method AdmissionEntry(pattern_length: int, case_number: int) returns (admitted: bool)
s|  requires 1 <= pattern_length <= 4294967295
s|  requires 1 <= case_number <= 4294967295
s|  ensures admitted == (case_number < 2 * pattern_length + 2)
s|{
ra:225|  var limit := Unsigned32(Unsigned32(2 * pattern_length) + 2);
ra:225|  if case_number >= limit {
ra:226|    admitted := false; return;
s|  }
ra:227|  admitted := true;
s|}
''',[dict(pattern_length=2147483647,case_number=1),dict(pattern_length=2,case_number=5)],
    dict(Unsigned32='Body-defined modulo semantics of the source unsigned expression for an explicitly modeled 32-bit unsigned target.'),
    'The entire frozen property concerns ONLY branch-number admission. Pattern length is an observation of a hypothetical valid nonempty literal, not a constructed/allocated string. No heap realizability, native crash, replacement semantics, iterator arithmetic or C++ type-width equivalence proof is claimed. No no-overflow precondition is added.')

add('P13','RequestEntry',r'''
req:76|function ValidQueue(queue: seq<int>, is_eq: seq<bool>, verdict: seq<int>): bool
s|{
req:76|  |is_eq| == |verdict| && forall id :: id in queue ==> 0 <= id < |verdict|
s|}
req:76|function IsConflict(id: int, is_eq: seq<bool>, verdict: seq<int>): bool
s|  requires |is_eq| == |verdict| && 0 <= id < |verdict|
s|{
req:76,req:88|  verdict[id] != 0 && ((verdict[id] == 1) != is_eq[id])
s|}
req:73|function FirstConflict(queue: seq<int>, is_eq: seq<bool>, verdict: seq<int>, start: int): int
s|  requires ValidQueue(queue,is_eq,verdict)
s|  requires 0 <= start <= |queue|
s|  ensures start <= FirstConflict(queue,is_eq,verdict,start) <= |queue|
s|  decreases |queue| - start
s|{
req:73,req:76,req:88|  if start == |queue| || IsConflict(queue[start],is_eq,verdict) then start else FirstConflict(queue,is_eq,verdict,start+1)
s|}
req:99|function FilterUnknown(queue: seq<int>, verdict: seq<int>): seq<int>
s|  requires forall id :: id in queue ==> 0 <= id < |verdict|
s|  decreases |queue|
s|{
req:99,req:105|  if |queue| == 0 then [] else (if verdict[queue[0]] == 0 then [queue[0]] else []) + FilterUnknown(queue[1..],verdict)
s|}
req:73|function ExpectedQueue(queue: seq<int>, is_eq: seq<bool>, verdict: seq<int>, start: int): seq<int>
s|  requires ValidQueue(queue,is_eq,verdict)
s|  requires 0 <= start <= |queue|
s|{
req:73,req:79,req:90,req:105|  queue[..start] + FilterUnknown(queue[start..FirstConflict(queue,is_eq,verdict,start)],verdict) + queue[FirstConflict(queue,is_eq,verdict,start)..]
s|}
vec:447|function EraseAt(queue: seq<int>, index: int): seq<int>
s|  requires 0 <= index < |queue|
s|{
vec:451,vec:452,vec:454|  queue[..index] + queue[index+1..]
s|}
req:61|method RequestEntry(queue: seq<int>, is_eq: seq<bool>, verdict: seq<int>, start: int) returns (queue_out: seq<int>, qhead_out: int, conflict: bool)
s|  requires ValidQueue(queue,is_eq,verdict)
s|  requires 0 <= start <= |queue| < 4294967296
s|  requires |verdict| < 4294967296
s|  requires forall v :: v in verdict ==> -1 <= v <= 1
s|  ensures conflict == (FirstConflict(queue,is_eq,verdict,start) < |queue|)
s|  ensures queue_out == ExpectedQueue(queue,is_eq,verdict,start)
s|  ensures qhead_out == (if conflict then start else |queue_out|)
s|  ensures 0 <= qhead_out <= |queue_out|
s|{
req:63|  queue_out := queue;
req:67|  qhead_out := start;
req:67|  conflict := false;
req:67|  var head := qhead_out;
req:71|  while head < |queue_out|
s|    invariant ValidQueue(queue_out,is_eq,verdict)
s|    invariant 0 <= start <= head <= |queue_out|
s|    invariant qhead_out == start
s|    invariant ExpectedQueue(queue_out,is_eq,verdict,head) == ExpectedQueue(queue,is_eq,verdict,start)
s|    invariant (FirstConflict(queue_out,is_eq,verdict,head) < |queue_out|) == (FirstConflict(queue,is_eq,verdict,start) < |queue|)
s|    decreases |queue_out| - head
s|  {
req:72|    var id := queue_out[head];
req:74|    var value := verdict[id];
req:76|    if value == 1 {
req:77|      if is_eq[id] {
req:79|        queue_out := EraseAt(queue_out,head);
req:41,req:42|        if head < qhead_out { qhead_out := qhead_out - 1; }
req:81|        continue;
s|      }
req:85,req:86|      conflict := true; return;
s|    }
req:88|    if value == -1 {
req:89|      if !is_eq[id] {
req:91|        queue_out := EraseAt(queue_out,head);
req:41,req:42|        if head < qhead_out { qhead_out := qhead_out - 1; }
req:94|        continue;
s|      }
req:97,req:98|      conflict := true; return;
s|    }
req:105|    head := head + 1;
s|  }
req:109|  if head != qhead_out {
req:110|    qhead_out := head;
s|  }
s|}
''',[dict(queue=[0,1,2,3],is_eq=[True,False,True,True],verdict=[1,0,-1,1],start=0),
     dict(queue=[0,1,2],is_eq=[True,False,True],verdict=[0,-1,0],start=1),
     dict(queue=[],is_eq=[],verdict=[],start=0)],
    dict(ValidQueue='Body-defined validity of request-ID observations into immutable kind/verdict arrays.',
         IsConflict='Disagreement of an observed definitive bisimulation verdict and asserted equality/disequality.',
         FirstConflict='Body-defined specification scanning original request order; does not assume oracle correctness.',
         FilterUnknown='Body-defined stable retention of unknown verdicts.',
         ExpectedQueue='Whole residual queue specification from first conflict and stable retention.',
         EraseAt='Value denotation of vector erase; its actual left-shift/pop inverse is modeled independently in P16.'),
    'The complete frozen bookkeeping property, with explicit child/oracle observations, not regex truth. Queue elements are immutable IDs; duplicates allowed. Observational initialization copies preexisting source state. Status writes of l_undef, statistics and trail effects are excluded. Selected scan never removes below qhead, but the source remove adjustment is retained. No native allocator/lifetime proof.')

add('P14','PreimageEntry',r'''
reg:774|function StrAt(word: seq<int>, index: int): seq<int>
s|{
reg:774|  if 0 <= index < |word| then [word[index]] else []
s|}
reg:775|function TargetAccepts(value: seq<int>, allowed_characters: seq<int>, accepts_empty: bool): bool
s|{
reg:775,reg:780|  if |value| == 0 then accepts_empty else |value| == 1 && value[0] in allowed_characters
s|}
reg:774|method PreimageEntry(word: seq<int>, allowed_characters: seq<int>, accepts_empty: bool, last_index: bool, k: int) returns (rewritten_accepts: bool)
s|  requires 0 <= k <= 64
s|  requires |word| < 4294967296
s|  ensures rewritten_accepts == TargetAccepts(StrAt(word,if last_index then |word|-1 else k),allowed_characters,accepts_empty)
s|{
reg:777|  if !last_index {
reg:779|    var yes := k < |word| && word[k] in allowed_characters;
reg:780|    var absent := accepts_empty && |word| <= k;
reg:780|    rewritten_accepts := yes || absent;
reg:782|  } else {
reg:786|    var yes := exists cut :: 0 <= cut < |word| && cut + 1 == |word| && word[cut] in allowed_characters;
reg:787|    rewritten_accepts := yes || (accepts_empty && |word| == 0);
s|  }
s|}
''',[dict(word=[],allowed_characters=[97],accepts_empty=True,last_index=True,k=0),
     dict(word=[97,98],allowed_characters=[98],accepts_empty=False,last_index=False,k=1),
     dict(word=[97],allowed_characters=[],accepts_empty=True,last_index=False,k=64)],
    dict(StrAt='Body-defined SMT str.at denotation, including negative/out-of-range empty result.',
         TargetAccepts='Body-defined observation of arbitrary target language on epsilon and singleton words only.'),
    'Both frozen indexing branches, not general preimage or regex engine correctness. Regex length/cat/union/intersection membership is expanded denotationally into word lengths and guarded character observations; nullable succeeds with the explicit accepts_empty observation. Integer character equality only. k is irrelevant in the last-index branch but retained as the shared signature input.')

add('P15','ObservationEntry',r'''
af:360|function HasCharacter(word: seq<int>, character: int): bool
s|{
af:360|  character in word
s|}
zs:131|function MatchFrom(word: seq<int>, needle: seq<int>, index: int, offset: int): bool
s|  requires 0 <= index <= |word| && index + |needle| <= |word|
s|  requires 0 <= offset <= |needle|
s|  ensures MatchFrom(word,needle,index,offset) == (word[index+offset..index+|needle|] == needle[offset..])
s|  decreases |needle| - offset
s|{
zs:131,zs:132|  if offset == |needle| then true else word[index+offset] == needle[offset] && MatchFrom(word,needle,index,offset+1)
s|}
zs:129|function ReplaceScan(word: seq<int>, needle: seq<int>, replacement: seq<int>, index: int, found: bool): seq<int>
s|  requires 0 < |needle|
s|  requires 0 <= index <= |word|
s|  decreases |word| - index
s|{
zs:129,zs:130,zs:134,zs:135,zs:136,zs:137,zs:140|  if index == |word| then [] else if !found && index+|needle| <= |word| && MatchFrom(word,needle,index,0) then replacement + ReplaceScan(word,needle,replacement,index+|needle|,true) else [word[index]] + ReplaceScan(word,needle,replacement,index+1,found)
s|}
zs:120|function ReplaceFirst(word: seq<int>, needle: seq<int>, replacement: seq<int>): seq<int>
s|{
zs:122,zs:123,zs:125,zs:126,zs:128,zs:129|  if |word| < |needle| then word else if |needle| == 0 then replacement + word else ReplaceScan(word,needle,replacement,0,false)
s|}
zs:129|lemma ScanPreserves(word: seq<int>, needle: seq<int>, replacement: seq<int>, character: int, index: int, found: bool)
s|  requires 0 < |needle| && 0 <= index <= |word|
s|  requires !HasCharacter(needle,character) && !HasCharacter(replacement,character)
s|  ensures HasCharacter(ReplaceScan(word,needle,replacement,index,found),character) == HasCharacter(word[index..],character)
s|  decreases |word| - index
s|{
zs:129|  if index < |word| {
zs:130|    if !found && index+|needle| <= |word| && MatchFrom(word,needle,index,0) {
zs:135,zs:136,zs:137|      ScanPreserves(word,needle,replacement,character,index+|needle|,true);
s|      assert word[index..index+|needle|] == needle;
s|      assert word[index..] == word[index..index+|needle|] + word[index+|needle|..];
zs:139|    } else {
zs:140|      ScanPreserves(word,needle,replacement,character,index+1,found);
s|      assert word[index..] == [word[index]] + word[index+1..];
s|    }
s|  }
s|}
af:317|method ObservationEntry(word: seq<int>, needle: seq<int>, replacement: seq<int>, character: int) returns (rewritten_contains: bool)
s|  requires !HasCharacter(needle,character)
s|  requires !HasCharacter(replacement,character)
s|  requires |word| < 2147483648 && |needle| < 2147483648 && |replacement| < 2147483648
s|  ensures rewritten_contains == HasCharacter(ReplaceFirst(word,needle,replacement),character)
s|{
zs:122,zs:125|  if 0 < |needle| <= |word| {
zs:129|    ScanPreserves(word,needle,replacement,character,0,false);
s|  }
af:399|  rewritten_contains := HasCharacter(word,character);
s|}
''',[dict(word=[97,98],needle=[],replacement=[99],character=98),
     dict(word=[97,98,97],needle=[97],replacement=[99,99],character=98),
     dict(word=[97,98],needle=[99,99,99],replacement=[],character=98)],
    dict(HasCharacter='Body-defined one-character containment denotation used by the source local rewrite guard/result.',
         MatchFrom='Pure recursion faithfully represents the source inner matching loop and guarded remaining offset.',
         ReplaceScan='Pure recursion represents the actual source outer loop state (index,found), first-only match, append and skip behavior. It is not an opaque replace oracle.',
         ReplaceFirst='Actual ground replacement branch order from zstring::replace, including empty needle and too-short source.',
         ScanPreserves='Erased proof helper by induction on the source scan; all contracts must be proved, not assumed.'),
    'Local character-observation rewrite only; no blocked-ancestor traversal/AST sharing/lifetime proof. Denotational helper loops are represented by structurally decreasing recursion with the same matching, found flag and index progression, permitting a pure specification in the entry postcondition. Length bounds keep selected native helper sums in unsigned range. This is not a native memory-safety proof.')

add('P16','RestorationEntry',r'''
vec:447|method EraseLeft(original: seq<int>, index: int) returns (erased: seq<int>)
s|  requires 0 <= index < |original|
s|  ensures erased == original[..index] + original[index+1..]
s|{
vec:449|  erased := original;
vec:449|  var pos := index;
vec:451|  while pos + 1 < |erased|
s|    invariant |erased| == |original|
s|    invariant index <= pos < |erased|
s|    invariant erased[..index] == original[..index]
s|    invariant erased[index..pos] == original[index+1..pos+1]
s|    invariant erased[pos..] == original[pos..]
s|    decreases |erased| - pos
s|  {
vec:452|    erased := erased[pos := erased[pos+1]];
vec:451|    pos := pos + 1;
s|  }
vec:454|  erased := erased[..|erased|-1];
s|}
eqh:84|method RestorationEntry(original: seq<int>, index: int) returns (restored: seq<int>)
s|  requires 0 <= index < |original| < 4294967296
s|  ensures restored == original
s|{
eqh:83|  var saved := original[index];
req:38,req:39|  restored := EraseLeft(original,index);
eqh:86|  restored := restored + [saved];
eqh:87|  var i := |restored| - 1;
eqh:87|  while i > index
s|    invariant |restored| == |original|
s|    invariant index <= i < |restored|
s|    invariant restored[..index] == original[..index]
s|    invariant restored[index..i] == original[index+1..i+1]
s|    invariant restored[i+1..] == original[i+1..]
s|    decreases i - index
s|  {
eqh:88|    restored := restored[i := restored[i-1]];
eqh:87|    i := i - 1;
s|  }
eqh:89|  restored := restored[index := saved];
s|}
''',[dict(original=[10,20,30],index=1),dict(original=[42],index=0),dict(original=[1,2,3],index=2)],
    dict(EraseLeft='Actual left-shift/pop erase computation, with a proved slice contract; not an assumed inverse.'),
    'The complete selected erase-save/undo path with genuine backward shifting. Bounds checking is performed by Dafny obligations on every modeled access. Integer value elements abstract movable request records; move/destructor/ref-count semantics, allocation failure and arbitrary interleavings/trail scopes are not modeled.')

add('P17','BooleanEntry',r'''
wit:154|method BooleanEntry(conjunction: bool, child_verdicts: seq<int>) returns (verdict: int)
s|  requires forall value :: value in child_verdicts ==> -1 <= value <= 1
s|  requires |child_verdicts| < 4294967296
s|  ensures verdict == (if conjunction then (if -1 in child_verdicts then -1 else if 0 in child_verdicts then 0 else 1) else (if 1 in child_verdicts then 1 else if 0 in child_verdicts then 0 else -1))
s|{
wit:156|  verdict := if conjunction then 1 else -1;
wit:157|  var i := 0;
wit:157|  while i < |child_verdicts|
s|    invariant 0 <= i <= |child_verdicts|
s|    invariant conjunction ==> -1 !in child_verdicts[..i]
s|    invariant !conjunction ==> 1 !in child_verdicts[..i]
s|    invariant verdict == (if 0 in child_verdicts[..i] then 0 else if conjunction then 1 else -1)
s|    decreases |child_verdicts| - i
s|  {
wit:158|    var value := child_verdicts[i];
wit:159|    if value == (if conjunction then -1 else 1) {
wit:160|      verdict := value; return;
s|    }
wit:161|    if value == 0 {
wit:162|      verdict := 0;
s|    }
wit:157|    i := i + 1;
s|  }
s|}
''',[dict(conjunction=True,child_verdicts=[1,0,1]),dict(conjunction=False,child_verdicts=[0,1,-1]),dict(conjunction=True,child_verdicts=[])],
    {},'Only the selected Boolean constructor aggregation; child verdicts are explicit observations with -1=false,0=unknown,1=true. Shared recursion/work counters, resource admission, derivatives, slicing and actual recursive truth are not modeled. Empty lists generalize the same fold identity; no counterexample may be advertised as native solely from a non-admitted AST shape.')

assert {p['id'] for p in properties} == set(freeze['property_ids'])
(OUT/'properties.json').write_text(json.dumps(properties,indent=2)+'\n',encoding='utf-8',newline='\n')
(OUT/'sources.json').write_text(json.dumps(dict(head=HEAD,files=sources),indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='generated',models=len(properties),source_files=len(sources),directory=str(OUT)),indent=2))
