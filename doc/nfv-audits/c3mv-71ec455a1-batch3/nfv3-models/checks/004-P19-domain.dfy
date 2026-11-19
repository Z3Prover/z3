// src: src/util/stx_search_tree.h:600 | }
// src: src/util/stx_search_tree.h:610 | return id;
predicate PointerView(lits: seq<int>, canonicalPointers: seq<int>, pointeeValue: seq<int>, activePointers: seq<int>)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:600 | }
// src: src/util/stx_search_tree.h:610 | return id;
  (forall j :: 0 <= j < |lits| ==> 0 <= lits[j] < |canonicalPointers|) && (forall j :: 0 <= j < |canonicalPointers| ==> 0 <= canonicalPointers[j] < |pointeeValue|) && (forall j :: 0 <= j < |activePointers| ==> 0 <= activePointers[j] < |pointeeValue|)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:583 | bool operator()(constraint_i* a, constraint_i* b) const { return a == b || a->equals(*b); }
// src: src/util/stx_search_tree.h:589 | void init(vector<constraint_i const*> const& cs) {
predicate SemanticActive(pointer: int, activePointers: seq<int>, pointeeValue: seq<int>)
// synth: specification, checked annotation, or structural delimiter
  requires 0 <= pointer < |pointeeValue|
// synth: specification, checked annotation, or structural delimiter
  requires forall j :: 0 <= j < |activePointers| ==> 0 <= activePointers[j] < |pointeeValue|
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:583 | bool operator()(constraint_i* a, constraint_i* b) const { return a == b || a->equals(*b); }
// src: src/util/stx_search_tree.h:589 | void init(vector<constraint_i const*> const& cs) {
  exists j :: 0 <= j < |activePointers| && pointeeValue[activePointers[j]] == pointeeValue[pointer]
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/vector.h:579 | bool contains(T const & elem) const {
function IdentityContains(active: seq<int>, pointer: int, start: int): bool
// synth: specification, checked annotation, or structural delimiter
  requires 0 <= start <= |active|
// synth: specification, checked annotation, or structural delimiter
  decreases |active| - start
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/vector.h:581 | const_iterator e = end();
// src: src/util/vector.h:582 | for (; it != e; ++it) {
// src: src/util/vector.h:583 | if (*it == elem) {
// src: src/util/vector.h:584 | return true;
// src: src/util/vector.h:586 | }
  if start == |active| then false else active[start] == pointer || IdentityContains(active,pointer,start+1)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:665 | if (id >= m_watch_list.size())
// src: src/util/stx_search_tree.h:675 | return;
predicate BucketShape(widths: seq<int>, items: seq<int>)
// synth: specification, checked annotation, or structural delimiter
  decreases |widths|
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:665 | if (id >= m_watch_list.size())
// src: src/util/stx_search_tree.h:675 | return;
  if |widths| == 0 then |items| == 0 else 0 <= widths[0] <= |items| && BucketShape(widths[1..],items[widths[0]..])
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:676 | auto& bucket = m_watch_list[id];
// src: src/util/stx_search_tree.h:678 | if (pos != bucket.end())
function RemoveFirst(row: seq<int>, core: int): seq<int>
// synth: specification, checked annotation, or structural delimiter
  decreases |row|
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:676 | auto& bucket = m_watch_list[id];
// src: src/util/stx_search_tree.h:677 | auto pos = std::find(bucket.begin(), bucket.end(), core_idx);
// src: src/util/stx_search_tree.h:678 | if (pos != bucket.end())
  if |row| == 0 then [] else if row[0] == core then row[1..] else [row[0]] + RemoveFirst(row[1..],core)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:672 | // before this is called, so the bucket is left consistent).
function Unwatch(widths: seq<int>, items: seq<int>, id: int, core: int): (seq<int>,seq<int>)
// synth: specification, checked annotation, or structural delimiter
  requires BucketShape(widths,items) && id >= 0
// synth: specification, checked annotation, or structural delimiter
  ensures BucketShape(Unwatch(widths,items,id,core).0,Unwatch(widths,items,id,core).1)
// synth: specification, checked annotation, or structural delimiter
  decreases id
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:673 | void unwatch(unsigned id, unsigned core_idx) {
// src: src/util/stx_search_tree.h:674 | if (id >= m_watch_list.size())
  if id >= |widths| then (widths,items) else
// src: src/util/stx_search_tree.h:675 | return;
  var width := widths[0];
// src: src/util/stx_search_tree.h:676 | auto& bucket = m_watch_list[id];
// src: src/util/stx_search_tree.h:677 | auto pos = std::find(bucket.begin(), bucket.end(), core_idx);
// src: src/util/stx_search_tree.h:678 | if (pos != bucket.end())
  if id == 0 then var row := RemoveFirst(items[..width],core); ([|row|]+widths[1..],row+items[width..]) else
// src: src/util/stx_search_tree.h:675 | return;
  var tail := Unwatch(widths[1..],items[width..],id-1,core);
// src: src/util/stx_search_tree.h:675 | return;
  ([width]+tail.0,items[..width]+tail.1)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:664 | void watch(unsigned id, unsigned core_idx) {
function Watch(widths: seq<int>, items: seq<int>, id: int, core: int): (seq<int>,seq<int>)
// synth: specification, checked annotation, or structural delimiter
  requires BucketShape(widths,items) && id >= 0
// synth: specification, checked annotation, or structural delimiter
  ensures BucketShape(Watch(widths,items,id,core).0,Watch(widths,items,id,core).1)
// synth: specification, checked annotation, or structural delimiter
  decreases id
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:665 | if (id >= m_watch_list.size())
// src: src/util/stx_search_tree.h:666 | m_watch_list.resize(id + 1);
  if |widths| == 0 then
// src: src/util/stx_search_tree.h:667 | m_watch_list[id].push_back(core_idx);
// src: src/util/stx_search_tree.h:668 | }
    if id == 0 then ([1],[core]) else var tail := Watch([],[],id-1,core); ([0]+tail.0,tail.1)
// src: src/util/stx_search_tree.h:665 | if (id >= m_watch_list.size())
  else var width := widths[0];
// src: src/util/stx_search_tree.h:668 | }
    if id == 0 then ([width+1]+widths[1..],items[..width]+[core]+items[width..]) else
// src: src/util/stx_search_tree.h:667 | m_watch_list[id].push_back(core_idx);
    var tail := Watch(widths[1..],items[width..],id-1,core);
// src: src/util/stx_search_tree.h:668 | }
    ([width]+tail.0,items[..width]+tail.1)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:685 | // that is NOT active and moves the watch there.
// src: src/util/stx_search_tree.h:688 | // Returns false - no absent literal exists anywhere in the core:
// src: src/util/stx_search_tree.h:689 | //                 every one of its literals is active right now,
predicate HasAbsent(lits: seq<int>, canonicalPointers: seq<int>, pointeeValue: seq<int>, activePointers: seq<int>)
// synth: specification, checked annotation, or structural delimiter
  requires PointerView(lits,canonicalPointers,pointeeValue,activePointers)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:685 | // that is NOT active and moves the watch there.
// src: src/util/stx_search_tree.h:688 | // Returns false - no absent literal exists anywhere in the core:
// src: src/util/stx_search_tree.h:689 | //                 every one of its literals is active right now,
  exists j :: 0 <= j < |lits| && !SemanticActive(canonicalPointers[lits[j]],activePointers,pointeeValue)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:685 | // that is NOT active and moves the watch there.
// src: src/util/stx_search_tree.h:688 | // Returns false - no absent literal exists anywhere in the core:
// src: src/util/stx_search_tree.h:689 | //                 every one of its literals is active right now,
// src: src/util/stx_search_tree.h:700 | unwatch(old_id, core_idx);
// src: src/util/stx_search_tree.h:701 | e.watch = i;
// src: src/util/stx_search_tree.h:702 | watch(e.lits[i], core_idx);
predicate WholeRewatch(lits: seq<int>, canonicalPointers: seq<int>, pointeeValue: seq<int>, activePointers: seq<int>, oldWatch: int, coreIdx: int, bucketWidths: seq<int>, bucketItems: seq<int>, moved: bool, newWatch: int, widthsOut: seq<int>, itemsOut: seq<int>)
// synth: specification, checked annotation, or structural delimiter
  requires PointerView(lits,canonicalPointers,pointeeValue,activePointers)
// synth: specification, checked annotation, or structural delimiter
  requires 0 <= oldWatch < |lits| && BucketShape(bucketWidths,bucketItems)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:685 | // that is NOT active and moves the watch there.
// src: src/util/stx_search_tree.h:688 | // Returns false - no absent literal exists anywhere in the core:
// src: src/util/stx_search_tree.h:689 | //                 every one of its literals is active right now,
// src: src/util/stx_search_tree.h:700 | unwatch(old_id, core_idx);
// src: src/util/stx_search_tree.h:701 | e.watch = i;
// src: src/util/stx_search_tree.h:702 | watch(e.lits[i], core_idx);
// src: src/util/stx_search_tree.h:707 | }
  0 <= newWatch < |lits| && (moved == HasAbsent(lits,canonicalPointers,pointeeValue,activePointers)) && (if moved then newWatch != oldWatch && !SemanticActive(canonicalPointers[lits[newWatch]],activePointers,pointeeValue) && (var removed := Unwatch(bucketWidths,bucketItems,lits[oldWatch],coreIdx); var changed := Watch(removed.0,removed.1,lits[newWatch],coreIdx); widthsOut == changed.0 && itemsOut == changed.1) else newWatch == oldWatch && widthsOut == bucketWidths && itemsOut == bucketItems)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:692 | bool try_rewatch(unsigned core_idx, vector<constraint_i const*> const& active) {
method RewatchEntry(lits: seq<int>, canonicalPointers: seq<int>, pointeeValue: seq<int>, activePointers: seq<int>, oldWatch: int, coreIdx: int, bucketWidths: seq<int>, bucketItems: seq<int>) returns (moved: bool, newWatch: int, widthsOut: seq<int>, itemsOut: seq<int>)
// synth: specification, checked annotation, or structural delimiter
  requires 0 < |lits| < 4294967296 && 0 <= oldWatch < |lits|
// synth: specification, checked annotation, or structural delimiter
  requires PointerView(lits,canonicalPointers,pointeeValue,activePointers)
// synth: specification, checked annotation, or structural delimiter
  requires |canonicalPointers| < 4294967296 && |pointeeValue| < 4294967296 && |activePointers| < 4294967296 && |bucketWidths| < 4294967296 && |bucketItems| < 4294967296
// synth: specification, checked annotation, or structural delimiter
  requires forall j,k :: 0 <= j < k < |canonicalPointers| ==> canonicalPointers[j] != canonicalPointers[k] && pointeeValue[canonicalPointers[j]] != pointeeValue[canonicalPointers[k]]
// synth: specification, checked annotation, or structural delimiter
  requires SemanticActive(canonicalPointers[lits[oldWatch]],activePointers,pointeeValue)
// synth: specification, checked annotation, or structural delimiter
  requires BucketShape(bucketWidths,bucketItems) && 0 <= coreIdx < 4294967296
// synth: specification, checked annotation, or structural delimiter
  requires forall j :: 0 <= j < |bucketWidths| ==> bucketWidths[j] < 4294967296
// synth: specification, checked annotation, or structural delimiter
  requires forall j :: 0 <= j < |bucketItems| ==> 0 <= bucketItems[j] < 4294967296
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:693 | unsat_core_entry& e = m_unsat_cores[core_idx];
  newWatch := oldWatch;
// src: src/util/stx_search_tree.h:693 | unsat_core_entry& e = m_unsat_cores[core_idx];
  widthsOut, itemsOut := bucketWidths, bucketItems;
// src: src/util/stx_search_tree.h:694 | unsigned old_id = e.lits[e.watch];
  var old_id := lits[oldWatch];
// src: src/util/stx_search_tree.h:695 | for (unsigned i = 0; i < e.lits.size(); ++i) {
  var i := 0;
// src: src/util/stx_search_tree.h:695 | for (unsigned i = 0; i < e.lits.size(); ++i) {
  while i < |lits|
// synth: specification, checked annotation, or structural delimiter
    invariant 0 <= i <= |lits|
// synth: specification, checked annotation, or structural delimiter
    invariant newWatch == oldWatch && widthsOut == bucketWidths && itemsOut == bucketItems
// synth: specification, checked annotation, or structural delimiter
    decreases |lits| - i
// synth: specification, checked annotation, or structural delimiter
  {
// src: src/util/stx_search_tree.h:696 | if (i == e.watch)
    if i == oldWatch {
// src: src/util/stx_search_tree.h:695 | for (unsigned i = 0; i < e.lits.size(); ++i) {
// src: src/util/stx_search_tree.h:697 | continue;
      i := i+1; continue;
// synth: specification, checked annotation, or structural delimiter
    }
// src: src/util/stx_search_tree.h:698 | auto c = m_constraint_store[e.lits[i]];
    var c := canonicalPointers[lits[i]];
// src: src/util/stx_search_tree.h:699 | if (!active.contains(c)) {
    if !IdentityContains(activePointers,c,0) {
// src: src/util/stx_search_tree.h:700 | unwatch(old_id, core_idx);
      var removed := Unwatch(widthsOut,itemsOut,old_id,coreIdx);
// src: src/util/stx_search_tree.h:701 | e.watch = i;
      newWatch := i;
// src: src/util/stx_search_tree.h:702 | watch(e.lits[i], core_idx);
      var changed := Watch(removed.0,removed.1,lits[i],coreIdx);
// src: src/util/stx_search_tree.h:702 | watch(e.lits[i], core_idx);
      widthsOut, itemsOut := changed.0, changed.1;
// src: src/util/stx_search_tree.h:703 | return true;
      moved := true; return;
// synth: specification, checked annotation, or structural delimiter
    }
// src: src/util/stx_search_tree.h:695 | for (unsigned i = 0; i < e.lits.size(); ++i) {
    i := i+1;
// synth: specification, checked annotation, or structural delimiter
  }
// src: src/util/stx_search_tree.h:707 | }
  moved := false;
// synth: specification, checked annotation, or structural delimiter
}

// Independent concrete proof harness, not a source-translated entry.
method ConcreteDomain0()
{
  var out0, out1, out2, out3 := RewatchEntry([0, 1], [0, 1], [10, 20, 10, 20], [2, 3], 0, 0, [1, 0], [0]);
}

// Independent concrete proof harness, not a source-translated entry.
method ConcreteDomain1()
{
  var out0, out1, out2, out3 := RewatchEntry([0, 1], [0, 1], [10, 20, 10], [2], 0, 0, [1], [0]);
}

// Independent concrete proof harness, not a source-translated entry.
method ConcreteDomain2()
{
  var out0, out1, out2, out3 := RewatchEntry([0], [0], [10, 10], [1], 0, 7, [], []);
}
