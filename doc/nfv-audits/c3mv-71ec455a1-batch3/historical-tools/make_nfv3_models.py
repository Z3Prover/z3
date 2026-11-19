"""Translate frozen batch-3 intents; never execute inspected production source."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

root=Path(__file__).parent
out=root/'nfv3-models'
head='71ec455a18702fe695d0c924a535ff9f385bd58d'
selection=json.loads((root/'nfv3-selection.json').read_text())
freeze=json.loads((root/'nfv3-selection-freeze.json').read_text())
assert hashlib.sha256((root/'nfv3-selection.json').read_bytes()).hexdigest()==freeze['sha256']
assert not (out/'frozen').exists(), 'Do not regenerate sealed computation/contracts'
selected={p['id']:p for p in selection['properties']}
aliases={'p':'src/ast/seq/seq_power_facet.cpp','w':'src/util/stx_search_tree.h','v':'src/util/vector.h'}
sources={}
records=[]
out.mkdir(exist_ok=True)

def add(pid,entry,template,notes):
    rows=[]; context={}; declarations={}
    for row in template.strip().splitlines():
        ref,code=row.split('|',1)
        tags=[]
        if ref=='s':
            rows.append('// synth: specification, checked annotation, or structural delimiter')
        else:
            for item in ref.split(','):
                alias,n=item.split(':'); n=int(n); path=aliases[alias]
                if path not in sources:
                    sources[path]=subprocess.check_output(['git','show',head+':'+path],cwd=r'C:\z3seq',text=True,encoding='utf-8').splitlines()
                rows.append(f'// src: {path}:{n} | {sources[path][n-1].strip()}')
                tags.append(dict(path=path,line=n))
                context.setdefault(path,set()).add(n)
        match=re.match(r'(function|predicate|method|lemma) (\w+)\(',code)
        if match and match[2]!=entry:
            declarations[match[2]]=dict(kind=match[1],source=tags)
        rows.append(code)
    model='\n'.join(rows)+'\n'
    code=re.sub(r'//[^\n]*','',model)
    signature=code[code.index('method '+entry):].split('\n{',1)[0]
    requires=re.findall(r'^\s*requires (.+)$',signature,re.M)
    ensures=re.findall(r'^\s*ensures (.+)$',signature,re.M)
    environment=[]
    for name,data in declarations.items():
        first=re.search(r'^(?:function|predicate|method|lemma) '+re.escape(name)+r'\(',code,re.M).start()
        header=code[first:code.index('\n{',first)]
        environment.append(dict(name=name,**data,description='Body-defined source-tagged projected behavior/specification; '+notes,requires=re.findall(r'^\s*requires (.+)$',header,re.M),ensures=re.findall(r'^\s*ensures (.+)$',header,re.M),contract_status='Must verify body; not a trusted axiom or assumed helper effect'))
    chosen=selected[pid]
    record=dict(id=pid,title=chosen['whole_positive_property'],path=chosen['path'],entry_point=entry,origin='source-inferred hypothesis',quote=chosen['grounding_quote'].strip(),original_ensures=ensures,assumptions=[dict(clause=c,origin='inferred',optional=False,description='Frozen source applicability or projected representation invariant, not a proved global/native caller fact; see frozen intent domains and limits.') for c in requires],source_span=chosen['span'],source_lines=sorted(context[chosen['path']]),required_context=sorted(context),source_tags={p:sorted(ns) for p,ns in context.items()},environment=environment,witnesses=chosen['domain_examples'],frozen_selection_sha256=freeze['sha256'],frozen_intent=chosen,correspondence=notes,provenance='Exact tags and local metadata only; no source equivalence or full upstream extraction/span gates.',sha256=hashlib.sha256(model.encode()).hexdigest())
    (out/(pid+'.dfy')).write_text(model,encoding='utf-8',newline='\n')
    records.append(record)

add('P18','PowerRewriteEntry',r'''
p:131,p:132,p:135|function Power(word: seq<int>, n: int): seq<int>
s|  decreases if n > 0 then n else 0
s|{
p:132,p:135|  if n <= 0 then [] else word + Power(word,n-1)
s|}
p:466,p:467|predicate TokenView(word: seq<int>, bounds: seq<int>, flags: seq<bool>)
s|{
p:466,p:467|  |bounds| == |flags| + 1 && bounds[0] == 0 && bounds[|flags|] == |word| && (forall j :: 0 <= j < |flags| ==> 0 <= bounds[j] <= bounds[j+1] <= |word| && (flags[j] ==> bounds[j+1] == bounds[j]+1))
s|}
p:271|function ConstantWord(word: seq<int>, bounds: seq<int>, flags: seq<bool>, i: int, acc: seq<int>): (bool,seq<int>)
s|  requires TokenView(word,bounds,flags) && 0 <= i <= |flags|
s|  requires acc == word[..bounds[i]]
s|  ensures ConstantWord(word,bounds,flags,i,acc).0 ==> ConstantWord(word,bounds,flags,i,acc).1 == word && 0 < |word|
s|  decreases |flags| - i
s|{
p:273,p:276,p:277,p:278,p:280|  if i == |flags| then (0 < |acc|,acc) else if !flags[i] then (false,acc) else ConstantWord(word,bounds,flags,i+1,acc+[word[bounds[i]]])
s|}
p:283|function PeriodScan(word: seq<int>, r: int, i: int): bool
s|  requires r > 0 && i >= 0
s|  decreases if i+r < |word| then |word|-i-r else 0
s|{
p:284,p:285,p:286,p:288|  if i+r >= |word| then true else word[i] == word[i+r] && PeriodScan(word,r,i+1)
s|}
p:291|function RootScan(word: seq<int>, d: int): seq<int>
s|  requires 0 < |word| && 1 <= d <= |word|
s|  ensures 0 < |RootScan(word,d)| <= |word|
s|  decreases |word| - d
s|{
p:292,p:293,p:294,p:296|  if d == |word| then word else if |word| % d == 0 && PeriodScan(word,d,0) then word[..d] else RootScan(word,d+1)
s|}
p:291|function PrimitiveRoot(word: seq<int>): seq<int>
s|  requires 0 < |word|
s|  ensures 0 < |PrimitiveRoot(word)| <= |word|
s|{
p:292,p:296|  RootScan(word,1)
s|}
p:447|function U32(value: int): int
s|{
p:447|  value % 4294967296
s|}
p:414,p:431,p:443|predicate EnumerationDomain(b: int, param: int, A: seq<int>, B: seq<int>, aBounds: seq<int>, bBounds: seq<int>, aLiteral: seq<bool>, bLiteral: seq<bool>)
s|  requires 0 <= b < 10
s|  requires TokenView(A,aBounds,aLiteral) && TokenView(B,bBounds,bLiteral)
s|{
p:431,p:455,p:460|  var X := if b < 5 then A else B;
p:431,p:455,p:460|  var Y := if b < 5 then B else A;
p:431,p:473|  var gx := ConstantWord(X,if b < 5 then aBounds else bBounds,if b < 5 then aLiteral else bLiteral,0,[]).0;
p:431,p:473|  var gy := ConstantWord(Y,if b < 5 then bBounds else aBounds,if b < 5 then bLiteral else aLiteral,0,[]).0;
p:441,p:442,p:443,p:444,p:446,p:447,p:448|  (if b % 5 == 3 then (gx <==> param > 0) && (param > 0 ==> param < |X| && PeriodScan(X,param,0)) && (gx && gy ==> |Y| >= U32(|X|+param) && U32(|Y|-param) % |X| == 0) else param == 0) && (b % 5 == 2 && gx && gy ==> X+Y == Y+X) && (gx ==> |X| < 4294967296) && (gy ==> |Y| < 4294967296)
s|}
p:455,p:456,p:457,p:458,p:459,p:464,p:468,p:469|method PowerRewriteEntry(b: int, param: int, A: seq<int>, B: seq<int>, aBounds: seq<int>, bBounds: seq<int>, aLiteral: seq<bool>, bLiteral: seq<bool>, expA: int, expB: int, y1: seq<int>, y2: seq<int>, wFresh: seq<int>, iFresh: int, jFresh: int, p1Fresh: seq<int>, p2Fresh: seq<int>, kFresh: int, qFresh: int) returns (constraints_ok: bool, fromWord: seq<int>, toWord: seq<int>)
s|  requires 0 <= b < 10 && 0 <= param < 4294967296
s|  requires TokenView(A,aBounds,aLiteral) && TokenView(B,bBounds,bLiteral)
s|  requires |aLiteral| < 4294967296 && |bLiteral| < 4294967296
s|  requires EnumerationDomain(b,param,A,B,aBounds,bBounds,aLiteral,bLiteral)
s|  ensures !constraints_ok || fromWord == toWord
s|{
p:460|  var dir_u := b < 5;
p:462,p:465|  var X := if dir_u then A else B;
p:463,p:465|  var Y := if dir_u then B else A;
p:462,p:465|  var M := if dir_u then expA else expB;
p:463,p:465|  var N := if dir_u then expB else expA;
p:466,p:467,p:470|  var cx := ConstantWord(X,if dir_u then aBounds else bBounds,if dir_u then aLiteral else bLiteral,0,[]);
p:466,p:468,p:470|  var cy := ConstantWord(Y,if dir_u then bBounds else aBounds,if dir_u then bLiteral else aLiteral,0,[]);
p:470|  var gx, sx := cx.0, cx.1;
p:470|  var gy, sy := cy.0, cy.1;
p:472,p:499,p:500|  constraints_ok := if dir_u then |Power(X,M)| <= |Power(Y,N)| else |Power(X,M)| < |Power(Y,N)|;
p:473,p:474,p:475,p:476,p:483,p:484,p:485,p:487,p:489,p:490,p:491,p:492,p:493,p:503|  var z: seq<int> := [];
p:504|  if b % 5 == 0 {
p:507|    constraints_ok := constraints_ok && (M <= 0 || |X| == 0);
p:508|    fromWord := Power(X,M);
p:508|    toWord := [];
p:509|    return;
p:510|  } else if b % 5 == 1 {
p:512,p:513|    constraints_ok := constraints_ok && N >= 1;
p:514|    constraints_ok := constraints_ok && Y == Power(X,M) + y1;
p:515|    z := y1 + Power(Y,N-1);
p:518|  } else if b % 5 == 2 {
p:520|    var w: seq<int>;
p:520|    var i, j := iFresh, jFresh;
p:521|    constraints_ok := constraints_ok && M >= 1;
p:522|    if gx || gy {
p:523|      var rt := PrimitiveRoot(if gx then sx else sy);
p:524|      w := rt;
p:525|      if gx {
p:526|        i := |sx| / |rt|;
s|      }
p:527|      if gy {
p:528|        j := |sy| / |rt|;
s|      }
p:530|    } else {
p:531|      w := wFresh;
s|    }
p:532,p:533,p:534,p:535|    if !gx { i := iFresh; constraints_ok := constraints_ok && i >= 1 && X == Power(w,i); }
p:537,p:538,p:539,p:540|    if !gy { j := jFresh; constraints_ok := constraints_ok && j >= 1 && Y == Power(w,j); }
p:542|    z := Power(w,j*N-i*M);
p:545|  } else if b % 5 == 3 {
p:547|    var p1, p2 := p1Fresh, p2Fresh;
p:548,p:549|    constraints_ok := constraints_ok && M >= 2 && N >= 2;
p:550|    if param > 0 {
p:552|      var l1 := |sx| % param;
p:553|      p1 := sx[|sx|-l1..];
p:554|      p2 := sx[l1..param];
p:556|    } else {
p:558,p:559,p:560|      constraints_ok := constraints_ok && X == Power(p1+p2,kFresh)+p1;
s|    }
p:562|    constraints_ok := constraints_ok && Y == Power(X,M-1)+p1+p2;
p:563|    z := p2+p1+Power(X,M-2)+p1+p2+Power(Y,N-2);
p:566|  } else {
p:568,p:569,p:570,p:571|    constraints_ok := constraints_ok && M == 1 && qFresh >= 0 && qFresh+1 <= N;
p:572|    constraints_ok := constraints_ok && Y == y1+y2;
p:573|    constraints_ok := constraints_ok && X == Power(Y,qFresh)+y1;
p:574|    z := y2+Power(Y,N-qFresh-1);
s|  }
p:578|  fromWord := Power(Y,N);
p:578|  toWord := Power(X,M)+z;
s|}
''','Word-semantic projection with explicit token observations and actual guard equations; no native equivalence, reachability, allocation or dependency proof. Signed powers truncate nonpositive exponents; root word algebra must be proved, not assumed.')

add('P19','RewatchEntry',r'''
w:600,w:610|predicate PointerView(lits: seq<int>, canonicalPointers: seq<int>, pointeeValue: seq<int>, activePointers: seq<int>)
s|{
w:600,w:610|  (forall j :: 0 <= j < |lits| ==> 0 <= lits[j] < |canonicalPointers|) && (forall j :: 0 <= j < |canonicalPointers| ==> 0 <= canonicalPointers[j] < |pointeeValue|) && (forall j :: 0 <= j < |activePointers| ==> 0 <= activePointers[j] < |pointeeValue|)
s|}
w:583,w:589|predicate SemanticActive(pointer: int, activePointers: seq<int>, pointeeValue: seq<int>)
s|  requires 0 <= pointer < |pointeeValue|
s|  requires forall j :: 0 <= j < |activePointers| ==> 0 <= activePointers[j] < |pointeeValue|
s|{
w:583,w:589|  exists j :: 0 <= j < |activePointers| && pointeeValue[activePointers[j]] == pointeeValue[pointer]
s|}
v:579|function IdentityContains(active: seq<int>, pointer: int, start: int): bool
s|  requires 0 <= start <= |active|
s|  decreases |active| - start
s|{
v:581,v:582,v:583,v:584,v:586|  if start == |active| then false else active[start] == pointer || IdentityContains(active,pointer,start+1)
s|}
w:665,w:675|predicate BucketShape(widths: seq<int>, items: seq<int>)
s|  decreases |widths|
s|{
w:665,w:675|  if |widths| == 0 then |items| == 0 else 0 <= widths[0] <= |items| && BucketShape(widths[1..],items[widths[0]..])
s|}
w:676,w:678|function RemoveFirst(row: seq<int>, core: int): seq<int>
s|  decreases |row|
s|{
w:676,w:677,w:678|  if |row| == 0 then [] else if row[0] == core then row[1..] else [row[0]] + RemoveFirst(row[1..],core)
s|}
w:672|function Unwatch(widths: seq<int>, items: seq<int>, id: int, core: int): (seq<int>,seq<int>)
s|  requires BucketShape(widths,items) && id >= 0
s|  ensures BucketShape(Unwatch(widths,items,id,core).0,Unwatch(widths,items,id,core).1)
s|  decreases id
s|{
w:673,w:674|  if id >= |widths| then (widths,items) else
w:675|  var width := widths[0];
w:676,w:677,w:678|  if id == 0 then var row := RemoveFirst(items[..width],core); ([|row|]+widths[1..],row+items[width..]) else
w:675|  var tail := Unwatch(widths[1..],items[width..],id-1,core);
w:675|  ([width]+tail.0,items[..width]+tail.1)
s|}
w:664|function Watch(widths: seq<int>, items: seq<int>, id: int, core: int): (seq<int>,seq<int>)
s|  requires BucketShape(widths,items) && id >= 0
s|  ensures BucketShape(Watch(widths,items,id,core).0,Watch(widths,items,id,core).1)
s|  decreases id
s|{
w:665,w:666|  if |widths| == 0 then
w:667,w:668|    if id == 0 then ([1],[core]) else var tail := Watch([],[],id-1,core); ([0]+tail.0,tail.1)
w:665|  else var width := widths[0];
w:668|    if id == 0 then ([width+1]+widths[1..],items[..width]+[core]+items[width..]) else
w:667|    var tail := Watch(widths[1..],items[width..],id-1,core);
w:668|    ([width]+tail.0,items[..width]+tail.1)
s|}
w:685,w:688,w:689|predicate HasAbsent(lits: seq<int>, canonicalPointers: seq<int>, pointeeValue: seq<int>, activePointers: seq<int>)
s|  requires PointerView(lits,canonicalPointers,pointeeValue,activePointers)
s|{
w:685,w:688,w:689|  exists j :: 0 <= j < |lits| && !SemanticActive(canonicalPointers[lits[j]],activePointers,pointeeValue)
s|}
w:685,w:688,w:689,w:700,w:701,w:702|predicate WholeRewatch(lits: seq<int>, canonicalPointers: seq<int>, pointeeValue: seq<int>, activePointers: seq<int>, oldWatch: int, coreIdx: int, bucketWidths: seq<int>, bucketItems: seq<int>, moved: bool, newWatch: int, widthsOut: seq<int>, itemsOut: seq<int>)
s|  requires PointerView(lits,canonicalPointers,pointeeValue,activePointers)
s|  requires 0 <= oldWatch < |lits| && BucketShape(bucketWidths,bucketItems)
s|{
w:685,w:688,w:689,w:700,w:701,w:702,w:707|  0 <= newWatch < |lits| && (moved == HasAbsent(lits,canonicalPointers,pointeeValue,activePointers)) && (if moved then newWatch != oldWatch && !SemanticActive(canonicalPointers[lits[newWatch]],activePointers,pointeeValue) && (var removed := Unwatch(bucketWidths,bucketItems,lits[oldWatch],coreIdx); var changed := Watch(removed.0,removed.1,lits[newWatch],coreIdx); widthsOut == changed.0 && itemsOut == changed.1) else newWatch == oldWatch && widthsOut == bucketWidths && itemsOut == bucketItems)
s|}
w:692|method RewatchEntry(lits: seq<int>, canonicalPointers: seq<int>, pointeeValue: seq<int>, activePointers: seq<int>, oldWatch: int, coreIdx: int, bucketWidths: seq<int>, bucketItems: seq<int>) returns (moved: bool, newWatch: int, widthsOut: seq<int>, itemsOut: seq<int>)
s|  requires 0 < |lits| < 4294967296 && 0 <= oldWatch < |lits|
s|  requires PointerView(lits,canonicalPointers,pointeeValue,activePointers)
s|  requires |canonicalPointers| < 4294967296 && |pointeeValue| < 4294967296 && |activePointers| < 4294967296 && |bucketWidths| < 4294967296 && |bucketItems| < 4294967296
s|  requires forall j,k :: 0 <= j < k < |canonicalPointers| ==> canonicalPointers[j] != canonicalPointers[k] && pointeeValue[canonicalPointers[j]] != pointeeValue[canonicalPointers[k]]
s|  requires SemanticActive(canonicalPointers[lits[oldWatch]],activePointers,pointeeValue)
s|  requires BucketShape(bucketWidths,bucketItems) && 0 <= coreIdx < 4294967296
s|  requires forall j :: 0 <= j < |bucketWidths| ==> bucketWidths[j] < 4294967296
s|  requires forall j :: 0 <= j < |bucketItems| ==> 0 <= bucketItems[j] < 4294967296
s|  ensures WholeRewatch(lits,canonicalPointers,pointeeValue,activePointers,oldWatch,coreIdx,bucketWidths,bucketItems,moved,newWatch,widthsOut,itemsOut)
s|{
w:693|  newWatch := oldWatch;
w:693|  widthsOut, itemsOut := bucketWidths, bucketItems;
w:694|  var old_id := lits[oldWatch];
w:695|  var i := 0;
w:695|  while i < |lits|
s|    invariant 0 <= i <= |lits|
s|    invariant newWatch == oldWatch && widthsOut == bucketWidths && itemsOut == bucketItems
s|    decreases |lits| - i
s|  {
w:696|    if i == oldWatch {
w:695,w:697|      i := i+1; continue;
s|    }
w:698|    var c := canonicalPointers[lits[i]];
w:699|    if !IdentityContains(activePointers,c,0) {
w:700|      var removed := Unwatch(widthsOut,itemsOut,old_id,coreIdx);
w:701|      newWatch := i;
w:702|      var changed := Watch(removed.0,removed.1,lits[i],coreIdx);
w:702|      widthsOut, itemsOut := changed.0, changed.1;
w:703|      moved := true; return;
s|    }
w:695|    i := i+1;
s|  }
w:707|  moved := false;
s|}
''','Documented semantic rewatch converse and complete local updates, not global UNSAT-core correctness. Semantic classes and flattened watch buckets are disclosed projections; actual scan uses identity. Normal-return container effects exclude native resource/overflow/lifetime behavior.')

(out/'properties.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8',newline='\n')
(out/'sources.json').write_text(json.dumps({p:dict(blob=subprocess.check_output(['git','rev-parse',head+':'+p],cwd=r'C:\z3seq',text=True).strip(),line_count=len(lines)) for p,lines in sources.items()},indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(generated=[dict(id=p['id'],sha256=p['sha256'],helpers=len(p['environment'])) for p in records],scope='draft models only, no verification or freeze yet'),indent=2))
