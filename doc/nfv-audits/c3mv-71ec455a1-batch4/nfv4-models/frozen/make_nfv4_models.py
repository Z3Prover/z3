"""Author body-defined models from the frozen batch-four selection."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).parent
OUT = ROOT / 'nfv4-models'
PIN = '71ec455a18702fe695d0c924a535ff9f385bd58d'
selection_raw = (ROOT / 'nfv4-selection.json').read_bytes()
assert hashlib.sha256(selection_raw).hexdigest() == '7d7e9ff5bc259460e5dfc9b6892f7ccadc1fd8378fd10e970a585b07029bb4ce'
selection = json.loads(selection_raw)
assert not (OUT / 'frozen').exists(), 'Do not regenerate sealed computation/contracts'
OUT.mkdir(exist_ok=True)
aliases = dict(p='src/ast/seq/seq_power_facet.cpp', h='src/ast/seq/seq_power_facet.h',
    e='src/ast/seq/seq_eq_facet.cpp', w='src/util/stx_search_tree.h', d='src/util/dependency.h',
    m='src/ast/seq/seq_mem_facet.cpp', mh='src/ast/seq/seq_mem_facet.h', a='src/ast/seq/seq_ambient_context.h',
    q='src/ast/seq_decl_plugin.cpp', z='src/util/zstring.h')
listing = subprocess.check_output(['git','ls-tree',PIN,'--',*aliases.values()],cwd=r'C:\z3seq',text=True)
oids = {line.split('\t',1)[1]:line.split()[2] for line in listing.splitlines()}
assert set(oids) == set(aliases.values())
paths = sorted(oids)
raw = subprocess.check_output(['git','cat-file','--batch'],input=('\n'.join(oids[p] for p in paths)+'\n').encode(),cwd=r'C:\z3seq')
sources = {}; records = []; offset = 0
for path in paths:
    end=raw.index(b'\n',offset); oid,kind,size=raw[offset:end].decode().split()
    blob=raw[end+1:end+1+int(size)]; offset=end+2+int(size)
    assert kind=='blob' and oid==oids[path]
    assert hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest()==oid
    sources[path]=blob.decode().splitlines()
    records.append(dict(path=path,blob=oid,sha256=hashlib.sha256(blob).hexdigest()))
assert offset==len(raw)

common = r'''
@w:644-657
function I(s: seq<int>, i: int): int
{ if 0 <= i < |s| then s[i] else 0 }
function B(s: seq<bool>, i: int): bool
{ 0 <= i < |s| && s[i] }
function R(s: seq<seq<int>>, i: int): seq<int>
{ if 0 <= i < |s| then s[i] else [] }
function Index(s: seq<int>, v: int, i: int): int
  decreases |s|-i
{ if 0 <= i < |s| then (if s[i]==v then i else Index(s,v,i+1)) else -1 }
function Count(s: seq<int>, v: int): int
  decreases |s|
{ if |s|==0 then 0 else (if s[0]==v then 1 else 0)+Count(s[1..],v) }
function Pick(s: seq<int>, ps: seq<int>): seq<int>
  decreases |ps|
{ if |ps|==0 then [] else [I(s,ps[0])]+Pick(s,ps[1..]) }
@q:1040-1055
function Rows(w: seq<int>, f: seq<int>): seq<seq<int>>
  decreases |w|
{
  if |w|==0 then [] else
  var n := if 0 <= w[0] <= |f| then w[0] else 0;
  [f[..n]]+Rows(w[1..],f[n..])
}
function Widths(rows: seq<seq<int>>): seq<int>
{ seq(|rows|, i => |rows[i]|) }
function Flat(rows: seq<seq<int>>): seq<int>
  decreases |rows|
{ if |rows|==0 then [] else rows[0]+Flat(rows[1..]) }
ghost predicate Partition(w: seq<int>, f: seq<int>)
{ Widths(Rows(w,f))==w && Flat(Rows(w,f))==f }
@w:600-611
ghost predicate Unique(s: seq<int>)
{ forall i,j :: 0 <= i < j < |s| ==> s[i]!=s[j] }
'''

p20 = r'''
@h:108-118
function FindActive(keys: seq<int>, active: seq<bool>, tok: int, i: int): int
  decreases |keys|-i
{ if 0 <= i < |keys| then (if B(active,i) && keys[i]==tok then i else FindActive(keys,active,tok,i+1)) else -1 }
@p:27-32
function Deactivate(active: seq<bool>, idx: int): seq<bool>
{ seq(|active|, i => active[i] && i!=idx) }
@e:37-45
function Substitute(ts: seq<int>, tok: int, repl: seq<int>): seq<int>
  decreases |ts|
{ if |ts|==0 then [] else (if ts[0]==tok then repl else [ts[0]])+Substitute(ts[1..],tok,repl) }
@h:38-61,86-102
function Register(repl: seq<int>, sp: seq<bool>, sw: seq<int>, si: seq<int>, se: seq<int>, state: (seq<int>,seq<seq<int>>,seq<bool>,seq<int>,seq<int>,seq<int>)): (seq<int>,seq<seq<int>>,seq<bool>,seq<int>,seq<int>,seq<int>)
  decreases |repl|
{
  if |repl|==0 then state else
  var t := repl[0];
  var add := B(sp,t) && FindActive(state.0,state.2,t,0)<0;
  var ns := if add then (state.0+[t],state.1+[R(Rows(sw,si),t)],state.2+[true],state.3+[I(se,t)],state.4+[0],state.5+[0]) else state;
  Register(repl[1..],sp,sw,si,se,ns)
}
@p:49-60
function Rebase(rows: seq<seq<int>>, active: seq<bool>, tok: int, repl: seq<int>): seq<seq<int>>
{ seq(|rows|, i => if B(active,i) && tok in rows[i] then Substitute(rows[i],tok,repl) else rows[i]) }
@p:43-61
function PowerExpected(sp: seq<bool>, sw: seq<int>, si: seq<int>, se: seq<int>, keys: seq<int>, rows: seq<seq<int>>, active: seq<bool>, exps: seq<int>, deps: seq<int>, flags: seq<int>, tok: int, repl: seq<int>): (seq<int>,seq<seq<int>>,seq<bool>,seq<int>,seq<int>,seq<int>)
{
  var state := Register(repl,sp,sw,si,se,(keys,rows,Deactivate(active,FindActive(keys,active,tok,0)),exps,deps,flags));
  (state.0,Rebase(state.1,state.2,tok,repl),state.2,state.3,state.4,state.5)
}
@p:49-60
ghost predicate Edge(keys: seq<int>, rows: seq<seq<int>>, active: seq<bool>, a: int, b: int)
{ exists j :: 0 <= j < |keys| && B(active,j) && keys[j]==a && b in R(rows,j) }
ghost predicate CurrentBaseAcyclic(keys: seq<int>, rows: seq<seq<int>>, active: seq<bool>)
{
  !(exists cycle: seq<int> :: |cycle|>1 && cycle[0]==cycle[|cycle|-1] && (forall j :: 0 <= j < |cycle|-1 ==> Edge(keys,rows,active,cycle[j],cycle[j+1])))
}
@h:38-61,86-118
ghost predicate PowerStateWellFormed(sp: seq<bool>, se: seq<int>, keys: seq<int>, rows: seq<seq<int>>, active: seq<bool>, exps: seq<int>, deps: seq<int>, flags: seq<int>)
{
  |se|==|sp| && |rows|==|keys|==|active|==|exps|==|deps|==|flags| &&
  (forall j :: 0 <= j < |keys| ==> 0 <= keys[j] < |sp| && B(sp,keys[j]) && exps[j]==I(se,keys[j]) && deps[j]>=0 && 0<=flags[j]<4 && (forall t :: t in rows[j] ==> 0<=t<|sp|)) &&
  (forall j,k :: 0<=j<k<|keys| && active[j] && active[k] ==> keys[j]!=keys[k])
}
@q:1040-1055
ghost predicate Catalog(sp: seq<bool>, sw: seq<int>, si: seq<int>, se: seq<int>)
{
  |sw|==|se|==|sp| && Partition(sw,si) && (forall t :: t in si ==> 0<=t<|sp|) &&
  (forall j :: 0<=j<|sp| && !sp[j] ==> sw[j]==0) && CurrentBaseAcyclic(seq(|sp|,i=>i),Rows(sw,si),sp)
}
@p:43-61
ghost predicate PowerUpdateExact(sp: seq<bool>, sw: seq<int>, si: seq<int>, se: seq<int>, keys: seq<int>, rows: seq<seq<int>>, active: seq<bool>, exps: seq<int>, deps: seq<int>, flags: seq<int>, tok: int, repl: seq<int>, ko: seq<int>, wo: seq<int>, io: seq<int>, ao: seq<bool>, eo: seq<int>, depso: seq<int>, fo: seq<int>)
{
  var expected := PowerExpected(sp,sw,si,se,keys,rows,active,exps,deps,flags,tok,repl);
  (ko,Rows(wo,io),ao,eo,depso,fo)==expected && Partition(wo,io)
}
@p:43-61
method PowerSubstitutionEntry(syntaxPower: seq<bool>, syntaxWidths: seq<int>, syntaxItems: seq<int>, syntaxExps: seq<int>, keys: seq<int>, widths: seq<int>, items: seq<int>, active: seq<bool>, exps: seq<int>, deps: seq<int>, flags: seq<int>, fromTok: int, repl: seq<int>, substDep: int) returns (keysOut: seq<int>, widthsOut: seq<int>, itemsOut: seq<int>, activeOut: seq<bool>, expsOut: seq<int>, depsOut: seq<int>, flagsOut: seq<int>)
  requires Catalog(syntaxPower,syntaxWidths,syntaxItems,syntaxExps)
  requires Partition(widths,items) && PowerStateWellFormed(syntaxPower,syntaxExps,keys,Rows(widths,items),active,exps,deps,flags)
  requires 0<=fromTok<|syntaxPower| && (forall t :: t in repl ==> 0<=t<|syntaxPower|) && substDep>=0
  requires |keys|+|repl|<4294967296 && (forall n :: n in widths+syntaxWidths ==> 0<=n<4294967296) && (forall r :: r in Rows(widths,items)+Rows(syntaxWidths,syntaxItems) ==> |Substitute(r,fromTok,repl)|<4294967296)
  ensures Partition(widthsOut,itemsOut) && PowerStateWellFormed(syntaxPower,syntaxExps,keysOut,Rows(widthsOut,itemsOut),activeOut,expsOut,depsOut,flagsOut)
  ensures PowerUpdateExact(syntaxPower,syntaxWidths,syntaxItems,syntaxExps,keys,Rows(widths,items),active,exps,deps,flags,fromTok,repl,keysOut,widthsOut,itemsOut,activeOut,expsOut,depsOut,flagsOut)
  ensures CurrentBaseAcyclic(keys,Rows(widths,items),active) ==> CurrentBaseAcyclic(keysOut,Rows(widthsOut,itemsOut),activeOut)
{
@p:44-46
  var idx := FindActive(keys,active,fromTok,0);
  var ko, bases, ao, eo, de, fl := keys, Rows(widths,items), Deactivate(active,idx), exps, deps, flags;
@p:47-48
  var j := 0;
  while j < |repl|
    invariant 0<=j<=|repl|
    decreases |repl|-j
  {
    var t := repl[j];
    if B(syntaxPower,t) && FindActive(ko,ao,t,0)<0 {
@h:86-102,38-61
      ko := ko+[t];
      bases := bases+[R(Rows(syntaxWidths,syntaxItems),t)];
      ao := ao+[true];
      eo := eo+[I(syntaxExps,t)];
      de := de+[0];
      fl := fl+[0];
    }
@p:47-48
    j := j+1;
  }
@p:49-60
  bases := Rebase(bases,ao,fromTok,repl);
  keysOut, widthsOut, itemsOut, activeOut, expsOut, depsOut, flagsOut := ko, Widths(bases), Flat(bases), ao, eo, de, fl;
}
'''

p21 = r'''
@w:637-658
function Eligible(c: seq<bool>, sat: seq<bool>, i: int): bool
  decreases |c|-i
{ if 0<=i<|c| then (c[i] || B(sat,i)) && Eligible(c,sat,i+1) else true }
function Collect(c: seq<bool>, w: seq<int>, i: int, offset: int): seq<int>
  decreases |w|-i
{
  if 0<=i<|w| then
  var n := if w[i]>=0 then w[i] else 0;
  (if B(c,i) then seq(n,j=>offset+j) else [])+Collect(c,w,i+1,offset+n)
  else []
}
@d:235-275
function Subset(a: seq<int>, b: seq<int>): bool
  decreases |a|
{ if |a|==0 then true else a[0] in b && Subset(a[1..],b) }
@w:782-805
function Filter(ps: seq<int>, has: seq<bool>, dw: seq<int>, di: seq<int>, ch: bool, cl: seq<int>): seq<int>
  decreases |ps|
{
  if |ps|==0 then [] else
  (if !ch || !B(has,ps[0]) || Subset(R(Rows(dw,di),ps[0]),cl) then [ps[0]] else [])+Filter(ps[1..],has,dw,di,ch,cl)
}
@w:601-611
function InternList(values: seq<int>, store: seq<int>): (seq<int>,seq<int>)
  decreases |values|
{
  if |values|==0 then (store,[]) else
  var found := Index(store,values[0],0);
  var id := if found<0 then |store| else found;
  var ns := if found<0 then store+[values[0]] else store;
  var rest := InternList(values[1..],ns);
  (rest.0,[id]+rest.1)
}
@w:664-668
function WatchAdd(buckets: seq<seq<int>>, id: int, core: int): seq<seq<int>>
{
  if id<0 then buckets else if id<|buckets| then buckets[id:=buckets[id]+[core]] else buckets+seq(id-|buckets|,i=>[])+[[core]]
}
@w:824-846
function CacheExpected(enabled: bool, fc: seq<bool>, fs: seq<bool>, fw: seq<int>, fv: seq<int>, dh: seq<bool>, dw: seq<int>, di: seq<int>, ch: bool, cl: seq<int>, store: seq<int>, cores: seq<seq<int>>, watches: seq<int>, buckets: seq<seq<int>>): (seq<int>,seq<seq<int>>,seq<int>,seq<seq<int>>,bool)
{
  var ps := if enabled && Eligible(fc,fs,0) then Filter(Collect(fc,fw,0,0),dh,dw,di,ch,cl) else [];
  if |ps|==0 then (store,cores,watches,buckets,false) else
  var interned := InternList(Pick(fv,ps),store);
  (interned.0,cores+[interned.1],watches+[0],WatchAdd(buckets,I(interned.1,0),|cores|),true)
}
@mh:65-94
function AcceptWord(ids: seq<int>, words: seq<seq<int>>, word: seq<int>): bool
  decreases |ids|
{ if |ids|==0 then false else R(words,ids[0])==word || AcceptWord(ids[1..],words,word) }
@m:886-913
ghost predicate BackgroundAllows(any: bool, lengths: seq<int>, n: int)
{ n>=0 && (any || n in lengths) }
ghost predicate JointSatisfiable(values: seq<int>, words: seq<seq<int>>, langs: seq<seq<int>>, any: bool, lengths: seq<int>, guessed: bool, n: int)
{
  if |values|==0 then (if guessed then BackgroundAllows(any,lengths,n) else any || (exists k :: k in lengths && k>=0))
  else exists w :: 0<=w<|words| && BackgroundAllows(any,lengths,|words[w]|) && (!guessed || |words[w]|==n) && (forall v :: v in values ==> AcceptWord(R(langs,v),words,words[w]))
}
@m:886-913
ghost predicate ClosingCertificate(fc: seq<bool>, fw: seq<int>, fv: seq<int>, dh: seq<bool>, dw: seq<int>, di: seq<int>, ch: bool, cl: seq<int>, words: seq<seq<int>>, langs: seq<seq<int>>, any: bool, lengths: seq<int>, guessed: bool, n: int, leaf: int, proof: seq<int>)
{
  var collected := Collect(fc,fw,0,0);
  (forall p :: p in proof ==> p in collected && (if ch then !B(dh,p) || Subset(R(Rows(dw,di),p),cl) else !B(dh,p))) &&
  (guessed ==> ch && leaf in cl && BackgroundAllows(any,lengths,n) && (forall p :: p in collected ==> exists w :: 0<=w<|words| && |words[w]|==n && AcceptWord(R(langs,I(fv,p)),words,words[w]))) &&
  !JointSatisfiable(Pick(fv,proof),words,langs,any,lengths,guessed,n)
}
@w:619-628,660-668
ghost predicate CacheStateWellFormed(store: seq<int>, cores: seq<seq<int>>, watches: seq<int>, buckets: seq<seq<int>>, nlangs: int)
{
  Unique(store) && (forall v :: v in store ==> 0<=v<nlangs) && |watches|==|cores| && |buckets|<=|store| &&
  (forall c :: 0<=c<|cores| ==> |cores[c]|>0 && 0<=watches[c]<|cores[c]| && (forall id :: id in cores[c] ==> 0<=id<|store|) &&
    0<=I(cores[c],watches[c])<|buckets| && (forall b :: 0<=b<|buckets| ==> Count(buckets[b],c)==(if b==I(cores[c],watches[c]) then 1 else 0))) &&
  (forall b,c :: 0<=b<|buckets| && c in buckets[b] ==> 0<=c<|cores|)
}
@w:807-846
ghost predicate AllCoresUnsat(store: seq<int>, cores: seq<seq<int>>, words: seq<seq<int>>, langs: seq<seq<int>>, any: bool, lengths: seq<int>)
{ forall c :: 0<=c<|cores| ==> !JointSatisfiable(Pick(store,cores[c]),words,langs,any,lengths,false,0) }
ghost predicate CacheInsertExact(enabled: bool, fc: seq<bool>, fs: seq<bool>, fw: seq<int>, fv: seq<int>, dh: seq<bool>, dw: seq<int>, di: seq<int>, ch: bool, cl: seq<int>, store: seq<int>, cores: seq<seq<int>>, watches: seq<int>, buckets: seq<seq<int>>, inserted: bool, so: seq<int>, cw: seq<int>, ci: seq<int>, wo: seq<int>, bw: seq<int>, bi: seq<int>)
{
  (so,Rows(cw,ci),wo,Rows(bw,bi),inserted)==CacheExpected(enabled,fc,fs,fw,fv,dh,dw,di,ch,cl,store,cores,watches,buckets) && Partition(cw,ci) && Partition(bw,bi)
}
@w:824-846
method CacheInsertEntry(enabled: bool, facetContrib: seq<bool>, facetSatisfied: seq<bool>, facetWidths: seq<int>, facetValues: seq<int>, factHasDep: seq<bool>, factDepWidths: seq<int>, factDepItems: seq<int>, conflictHasDep: bool, conflictLeaves: seq<int>, wordWidths: seq<int>, wordChars: seq<int>, langWidths: seq<int>, langWords: seq<int>, backgroundAny: bool, backgroundLengths: seq<int>, guessPresent: bool, guessLength: int, guessLeaf: int, proofPositions: seq<int>, store: seq<int>, coreWidths: seq<int>, coreIds: seq<int>, coreWatch: seq<int>, bucketWidths: seq<int>, bucketItems: seq<int>) returns (inserted: bool, storeOut: seq<int>, coreWidthsOut: seq<int>, coreIdsOut: seq<int>, coreWatchOut: seq<int>, bucketWidthsOut: seq<int>, bucketItemsOut: seq<int>)
  requires |facetContrib|==|facetSatisfied|==|facetWidths| && Partition(facetWidths,facetValues) && (forall f :: 0<=f<|facetWidths| && !facetContrib[f] ==> facetWidths[f]==0)
  requires |factHasDep|==|factDepWidths|==|facetValues| && Partition(factDepWidths,factDepItems) && (forall p :: 0<=p<|factHasDep| && !factHasDep[p] ==> factDepWidths[p]==0) && (!conflictHasDep ==> conflictLeaves==[])
  requires Partition(wordWidths,wordChars) && Partition(langWidths,langWords) && (forall w :: w in langWords ==> 0<=w<|wordWidths|) && (forall v :: v in facetValues ==> 0<=v<|langWidths|)
  requires (forall c :: c in wordChars ==> 0<=c<=196607) && (forall n :: n in backgroundLengths ==> n>=0)
  requires Partition(coreWidths,coreIds) && Partition(bucketWidths,bucketItems) && CacheStateWellFormed(store,Rows(coreWidths,coreIds),coreWatch,Rows(bucketWidths,bucketItems),|langWidths|)
  requires |facetContrib|<4294967296 && |store|+|facetValues|<4294967296 && |coreWidths|+1<4294967296 && (forall w :: w in facetWidths+factDepWidths+wordWidths+langWidths+coreWidths+bucketWidths ==> 0<=w<4294967296) && (forall x :: x in factDepItems+conflictLeaves+[guessLeaf] ==> 0<=x<4294967296)
  requires !(enabled && Eligible(facetContrib,facetSatisfied,0) && |Filter(Collect(facetContrib,facetWidths,0,0),factHasDep,factDepWidths,factDepItems,conflictHasDep,conflictLeaves)|>0) || ClosingCertificate(facetContrib,facetWidths,facetValues,factHasDep,factDepWidths,factDepItems,conflictHasDep,conflictLeaves,Rows(wordWidths,wordChars),Rows(langWidths,langWords),backgroundAny,backgroundLengths,guessPresent,guessLength,guessLeaf,proofPositions)
  ensures Partition(coreWidthsOut,coreIdsOut) && Partition(bucketWidthsOut,bucketItemsOut) && CacheStateWellFormed(storeOut,Rows(coreWidthsOut,coreIdsOut),coreWatchOut,Rows(bucketWidthsOut,bucketItemsOut),|langWidths|)
  ensures CacheInsertExact(enabled,facetContrib,facetSatisfied,facetWidths,facetValues,factHasDep,factDepWidths,factDepItems,conflictHasDep,conflictLeaves,store,Rows(coreWidths,coreIds),coreWatch,Rows(bucketWidths,bucketItems),inserted,storeOut,coreWidthsOut,coreIdsOut,coreWatchOut,bucketWidthsOut,bucketItemsOut)
  ensures AllCoresUnsat(store,Rows(coreWidths,coreIds),Rows(wordWidths,wordChars),Rows(langWidths,langWords),backgroundAny,backgroundLengths) ==> AllCoresUnsat(storeOut,Rows(coreWidthsOut,coreIdsOut),Rows(wordWidths,wordChars),Rows(langWidths,langWords),backgroundAny,backgroundLengths)
{
@w:825-829
  inserted,storeOut,coreWidthsOut,coreIdsOut,coreWatchOut,bucketWidthsOut,bucketItemsOut := false,store,coreWidths,coreIds,coreWatch,bucketWidths,bucketItems;
  if !enabled || !Eligible(facetContrib,facetSatisfied,0) { return; }
  var ps := Collect(facetContrib,facetWidths,0,0);
  if |ps|==0 { return; }
@w:836-838
  ps := Filter(ps,factHasDep,factDepWidths,factDepItems,conflictHasDep,conflictLeaves);
  if |ps|==0 { return; }
@w:839-841
  var interned := InternList(Pick(facetValues,ps),store);
  storeOut := interned.0;
@w:842-845
  var cores := Rows(coreWidths,coreIds)+[interned.1];
  coreWidthsOut,coreIdsOut := Widths(cores),Flat(cores);
  coreWatchOut := coreWatch+[0];
  var buckets := WatchAdd(Rows(bucketWidths,bucketItems),I(interned.1,0),|coreWidths|);
  bucketWidthsOut,bucketItemsOut := Widths(buckets),Flat(buckets);
  inserted := true;
}
'''

p22 = r'''
@w:579-599
function FindIntern(owned: seq<int>, values: seq<int>, hashes: seq<int>, query: int, i: int): int
  decreases |owned|-i
{
  if 0<=i<|owned| then (if I(hashes,owned[i])%4294967296==I(hashes,query)%4294967296 && I(values,owned[i])==I(values,query) then i else FindIntern(owned,values,hashes,query,i+1)) else -1
}
@w:577-611
ghost predicate CanonicalStoreWellFormed(owned: seq<int>, values: seq<int>, hashes: seq<int>, ids: seq<int>)
{
  |values|==|hashes|==|ids| && Unique(owned) &&
  (forall j :: 0<=j<|owned| ==> 0<=owned[j]<|values| && I(ids,owned[j])==j) &&
  (forall j,k :: 0<=j<k<|owned| ==> I(values,owned[j])!=I(values,owned[k]))
}
@w:601-611
ghost predicate InternTransitionExact(query: int, owned: seq<int>, values: seq<int>, hashes: seq<int>, ids: seq<int>, id: int, oo: seq<int>, vo: seq<int>, ho: seq<int>, io: seq<int>)
{
  var found := FindIntern(owned,values,hashes,query,0);
  if found>=0 then id==I(ids,I(owned,found)) && (oo,vo,ho,io)==(owned,values,hashes,ids)
  else id==|owned| && (oo,vo,ho,io)==(owned+[|values|],values+[I(values,query)],hashes+[I(hashes,query)],ids+[|owned|])
}
@w:601-611
ghost predicate CanonicalClassPreserved(query: int, owned: seq<int>, values: seq<int>, id: int, oo: seq<int>, vo: seq<int>)
{
  0<=id<|oo| && I(vo,I(oo,id))==I(values,query) &&
  (forall j :: 0<=j<|owned| ==> j<|oo| && oo[j]==owned[j] && I(vo,oo[j])==I(values,owned[j]))
}
@w:601-611
method CanonicalInternEntry(query: int, owned: seq<int>, heapValues: seq<int>, heapHashes: seq<int>, heapIds: seq<int>) returns (id: int, ownedOut: seq<int>, valuesOut: seq<int>, hashesOut: seq<int>, idsOut: seq<int>)
  requires CanonicalStoreWellFormed(owned,heapValues,heapHashes,heapIds) && 0<=query<|heapValues|
  requires (forall j :: 0<=j<|heapHashes| ==> 0<=heapHashes[j]<18446744073709551616 && 0<=heapIds[j]<4294967296)
  requires (forall j,k :: 0<=j<|heapValues| && 0<=k<|heapValues| && heapValues[j]==heapValues[k] ==> heapHashes[j]%4294967296==heapHashes[k]%4294967296) && |owned|+1<4294967296
  ensures CanonicalStoreWellFormed(ownedOut,valuesOut,hashesOut,idsOut)
  ensures InternTransitionExact(query,owned,heapValues,heapHashes,heapIds,id,ownedOut,valuesOut,hashesOut,idsOut)
  ensures CanonicalClassPreserved(query,owned,heapValues,id,ownedOut,valuesOut)
{
@w:602-604
  ownedOut,valuesOut,hashesOut,idsOut := owned,heapValues,heapHashes,heapIds;
  var found := FindIntern(owned,heapValues,heapHashes,query,0);
  if found>=0 { id := I(heapIds,I(owned,found)); return; }
@w:605,122-132
  var clone := |heapValues|;
  valuesOut := heapValues+[heapValues[query]];
  hashesOut := heapHashes+[heapHashes[query]];
  idsOut := heapIds+[4294967295];
@w:606-609
  id := |owned|;
  idsOut := idsOut[clone:=id];
  ownedOut := owned+[clone];
}
'''

templates = {'P20':common+p20, 'P21':common+p21, 'P22':common+p22}
properties=[]
for chosen in selection['properties']:
    pid=chosen['id']; rows=[]; anchors=[]; tags={}
    for line in templates[pid].strip().splitlines():
        if line.startswith('@'):
            anchors=[]
            for ref in line[1:].split(','):
                if ':' in ref:
                    alias,ns=ref.split(':')
                else:
                    ns=ref
                bounds=list(map(int,ns.split('-')))
                for n in range(bounds[0],bounds[-1]+1):
                    path=aliases[alias]; assert 1<=n<=len(sources[path])
                    anchors.append((path,n))
            continue
        if not line.strip():
            rows.append(''); continue
        if re.match(r'^\s*(requires|ensures|invariant|decreases|assert)\b',line) or line.strip() in {'{','}'}:
            rows.append('// synth: specification, checked annotation, or structural delimiter')
        else:
            assert anchors
            for path,n in anchors:
                rows.append(f'// src: {path}:{n} | {sources[path][n-1].strip()}')
                tags.setdefault(path,set()).add(n)
        rows.append(line)
    model='\n'.join(rows)+'\n'
    code=re.sub(r'//[^\n]*','',model)
    entry=chosen['entry_name']
    signature=code[code.index('method '+entry):].split('\n{',1)[0]
    reqs=re.findall(r'^\s*requires (.+)$',signature,re.M)
    goals=re.findall(r'^\s*ensures (.+)$',signature,re.M)
    assert len(goals)==3
    params=re.search(r'method '+entry+r'\((.*?)\) returns',signature,re.S)[1]
    parsed=dict(re.findall(r'(\w+): (seq<(?:int|bool)>|int|bool)',params))
    assert parsed==chosen['inputs']
    declarations=[]
    for match in re.finditer(r'^(?:ghost )?(function|predicate|method|lemma) (\w+)\(',code,re.M):
        if match[2]==entry: continue
        header=code[match.start():code.index('\n{',match.start())] if '\n{' in code[match.start():] else ''
        raw_decl=re.search(r'^(?:ghost )?(?:function|predicate|method|lemma) '+re.escape(match[2])+r'\(',model,re.M)
        before=model[:raw_decl.start()].splitlines()
        helper_anchors=[]
        for prior in reversed(before):
            if not prior.startswith('//'): break
            anchor=re.fullmatch(r'// src: (.+):(\d+) \| (.*)',prior)
            if anchor:
                helper_anchors.append(dict(path=anchor[1],line=int(anchor[2]),text=anchor[3]))
        assert helper_anchors
        declarations.append(dict(name=match[2],kind=match[1],body_required=True,
            source_anchors=list(reversed(helper_anchors)),
            interpretation='Body-defined source-tagged projection; inspect actual body, not an admitted oracle. Total helper defaults apply only outside the frozen well-formed representation domain.',
            requires=re.findall(r'^\s*requires (.+)$',header,re.M),ensures=re.findall(r'^\s*ensures (.+)$',header,re.M)))
    record=dict(id=pid,entry_point=entry,origin='source-inferred hypothesis',path=chosen['path'],source_span=chosen['span'],
        title=chosen['positive_meaning'],quote=chosen['grounding_quote'].strip(),frozen_intent=chosen,
        frozen_selection_sha256=hashlib.sha256(selection_raw).hexdigest(),inputs=chosen['inputs'],outputs=chosen['outputs'],
        original_ensures=goals,assumptions=[dict(clause=r,origin='inferred',optional=False,
            description='Frozen applicability, well-formed projected state, representable machine counters or explicitly recomputed conditional closing certificate; see selection for complete justification.') for r in reqs],
        environment=declarations,examples=chosen['examples'],source_tags={p:sorted(ns) for p,ns in tags.items()},
        correspondence_limits=chosen['limitations']+[
            'Totalized access and row decoding return zero/false/empty only for malformed representations; requires exclude those cases. This is not a native default, a claimed safety fix or a hidden assumption.',
            'P21 uses the source Unicode alphabet0..196607; alternative global character modes are outside this finite-language projection.',
            'Exact-update predicates are complete original-algorithm specifications. A repair that suppresses/changes that transition may be impossible under the frozen conjunction; never weaken it to manufacture a repair.',
            'Source anchors cover projections/contexts, not a C++/Dafny translation-equivalence theorem or official full upstream admission.'],
        sha256=hashlib.sha256(model.encode()).hexdigest())
    (OUT/(pid+'.dfy')).write_text(model,encoding='utf-8',newline='\n')
    properties.append(record)
(OUT/'properties.json').write_text(json.dumps(properties,indent=2)+'\n',encoding='utf-8',newline='\n')
for rec in records:
    used=sorted({n for prop in properties for n in prop['source_tags'].get(rec['path'],[])})
    if rec['path']==aliases['z']:
        used=sorted(set(used)|set(range(36,52)))
    rec['excerpts']=[dict(line=n,text=sources[rec['path']][n-1]) for n in used]
(OUT/'sources.json').write_text(json.dumps(dict(head=PIN,files=records,scope='Raw pinned Git identities for exact source anchors; no native source execution.'),indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(status='authored',properties=[dict(id=p['id'],helpers=len(p['environment']),requires=len(p['assumptions']),whole_conjuncts=len(p['original_ensures']),sha256=p['sha256']) for p in properties],verifier_attempts=0),indent=2))
