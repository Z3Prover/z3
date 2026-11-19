// src: src/ast/seq/seq_req_facet.cpp:76 | case l_true:
function ValidQueue(queue: seq<int>, is_eq: seq<bool>, verdict: seq<int>): bool
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/ast/seq/seq_req_facet.cpp:76 | case l_true:
  |is_eq| == |verdict| && forall id :: id in queue ==> 0 <= id < |verdict|
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/ast/seq/seq_req_facet.cpp:76 | case l_true:
function IsConflict(id: int, is_eq: seq<bool>, verdict: seq<int>): bool
// synth: specification, checked proof annotation, or structural delimiter
  requires |is_eq| == |verdict| && 0 <= id < |verdict|
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/ast/seq/seq_req_facet.cpp:76 | case l_true:
// src: src/ast/seq/seq_req_facet.cpp:88 | case l_false:
  verdict[id] != 0 && ((verdict[id] == 1) != is_eq[id])
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/ast/seq/seq_req_facet.cpp:73 | regex_bisim bisim(m_rw);
function FirstConflict(queue: seq<int>, is_eq: seq<bool>, verdict: seq<int>, start: int): int
// synth: specification, checked proof annotation, or structural delimiter
  requires ValidQueue(queue,is_eq,verdict)
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 <= start <= |queue|
// synth: specification, checked proof annotation, or structural delimiter
  ensures start <= FirstConflict(queue,is_eq,verdict,start) <= |queue|
// synth: specification, checked proof annotation, or structural delimiter
  decreases |queue| - start
// synth: specification, checked proof annotation, or structural delimiter
{
// synth: explicit sequence membership instantiates the guarded queue-domain quantifier
  assert start < |queue| ==> queue[start] in queue;
// src: src/ast/seq/seq_req_facet.cpp:73 | regex_bisim bisim(m_rw);
// src: src/ast/seq/seq_req_facet.cpp:76 | case l_true:
// src: src/ast/seq/seq_req_facet.cpp:88 | case l_false:
  if start == |queue| || IsConflict(queue[start],is_eq,verdict) then start else FirstConflict(queue,is_eq,verdict,start+1)
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/ast/seq/seq_req_facet.cpp:99 | }
function FilterUnknown(queue: seq<int>, verdict: seq<int>): seq<int>
// synth: specification, checked proof annotation, or structural delimiter
  requires forall id :: id in queue ==> 0 <= id < |verdict|
// synth: specification, checked proof annotation, or structural delimiter
  decreases |queue|
// synth: specification, checked proof annotation, or structural delimiter
{
// synth: explicit element and suffix membership establish helper-call domains
  assert |queue| > 0 ==> queue[0] in queue;
// synth: explicit element and suffix membership establish helper-call domains
  assert |queue| > 0 ==> (forall id :: id in queue[1..] ==> id in queue);
// src: src/ast/seq/seq_req_facet.cpp:99 | }
// src: src/ast/seq/seq_req_facet.cpp:105 | f.set_status(head, l_undef);
  if |queue| == 0 then [] else (if verdict[queue[0]] == 0 then [queue[0]] else []) + FilterUnknown(queue[1..],verdict)
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/ast/seq/seq_req_facet.cpp:73 | regex_bisim bisim(m_rw);
function ExpectedQueue(queue: seq<int>, is_eq: seq<bool>, verdict: seq<int>, start: int): seq<int>
// synth: specification, checked proof annotation, or structural delimiter
  requires ValidQueue(queue,is_eq,verdict)
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 <= start <= |queue|
// synth: specification, checked proof annotation, or structural delimiter
{
// synth: slice membership establishes the filtering helper domain
  assert forall id :: id in queue[start..FirstConflict(queue,is_eq,verdict,start)] ==> id in queue;
// src: src/ast/seq/seq_req_facet.cpp:73 | regex_bisim bisim(m_rw);
// src: src/ast/seq/seq_req_facet.cpp:79 | f.remove(head);
// src: src/ast/seq/seq_req_facet.cpp:90 | // p != q confirmed: discharge.
// src: src/ast/seq/seq_req_facet.cpp:105 | f.set_status(head, l_undef);
  queue[..start] + FilterUnknown(queue[start..FirstConflict(queue,is_eq,verdict,start)],verdict) + queue[FirstConflict(queue,is_eq,verdict,start)..]
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/util/vector.h:447 | void erase(iterator pos) {
function EraseAt(queue: seq<int>, index: int): seq<int>
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 <= index < |queue|
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/util/vector.h:451 | iterator e    = end();
// src: src/util/vector.h:452 | for(; pos != e; ++pos, ++prev) {
// src: src/util/vector.h:454 | }
  queue[..index] + queue[index+1..]
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/ast/seq/seq_req_facet.cpp:61 | stx::simplify_result req_propagation::propagate(eq_tree::node& n) {
method RequestEntry(queue: seq<int>, is_eq: seq<bool>, verdict: seq<int>, start: int) returns (queue_out: seq<int>, qhead_out: int, conflict: bool)
// synth: specification, checked proof annotation, or structural delimiter
  requires ValidQueue(queue,is_eq,verdict)
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 <= start <= |queue| < 4294967296
// synth: specification, checked proof annotation, or structural delimiter
  requires |verdict| < 4294967296
// synth: specification, checked proof annotation, or structural delimiter
  requires forall v :: v in verdict ==> -1 <= v <= 1
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/ast/seq/seq_req_facet.cpp:63 | auto& f = ac.req_facet_ref();
  queue_out := queue;
// src: src/ast/seq/seq_req_facet.cpp:67 | unsigned head = f.qhead();
  qhead_out := start;
// src: src/ast/seq/seq_req_facet.cpp:67 | unsigned head = f.qhead();
  conflict := false;
// src: src/ast/seq/seq_req_facet.cpp:67 | unsigned head = f.qhead();
  var head := qhead_out;
// src: src/ast/seq/seq_req_facet.cpp:71 | while (head < f.reqs().size()) {
  while head < |queue_out|
// synth: specification, checked proof annotation, or structural delimiter
    invariant ValidQueue(queue_out,is_eq,verdict)
// synth: specification, checked proof annotation, or structural delimiter
    invariant 0 <= start <= head <= |queue_out|
// synth: specification, checked proof annotation, or structural delimiter
    invariant qhead_out == start
// synth: specification, checked proof annotation, or structural delimiter
    decreases |queue_out| - head
// synth: specification, checked proof annotation, or structural delimiter
  {
// src: src/ast/seq/seq_req_facet.cpp:72 | str_req const& r = f.reqs()[head];
    var id := queue_out[head];
// synth: instantiate the request-index domain before indexing observations
    assert id in queue_out;
// src: src/ast/seq/seq_req_facet.cpp:74 | lbool verdict = bisim.are_equivalent(r.m_p, r.m_q);
    var value := verdict[id];
// src: src/ast/seq/seq_req_facet.cpp:76 | case l_true:
    if value == 1 {
// src: src/ast/seq/seq_req_facet.cpp:77 | if (r.m_is_eq) {
      if is_eq[id] {
// synth: erasure introduces no request identities
        assert forall item :: item in EraseAt(queue_out,head) ==> item in queue_out;
// src: src/ast/seq/seq_req_facet.cpp:79 | f.remove(head);
        queue_out := EraseAt(queue_out,head);
// src: src/ast/seq/seq_req_facet.cpp:41 | if (idx < m_qhead)
// src: src/ast/seq/seq_req_facet.cpp:42 | advance_qhead(m_qhead - 1);
        if head < qhead_out { qhead_out := qhead_out - 1; }
// src: src/ast/seq/seq_req_facet.cpp:81 | continue; // re-examine same index (now the next request)
        continue;
// synth: specification, checked proof annotation, or structural delimiter
      }
// src: src/ast/seq/seq_req_facet.cpp:85 | n.set_conflict(stx::br_plugin_base, r.m_dep);
// src: src/ast/seq/seq_req_facet.cpp:86 | return stx::simplify_result::conflict;
      conflict := true; return;
// synth: specification, checked proof annotation, or structural delimiter
    }
// src: src/ast/seq/seq_req_facet.cpp:88 | case l_false:
    if value == -1 {
// src: src/ast/seq/seq_req_facet.cpp:89 | if (!r.m_is_eq) {
      if !is_eq[id] {
// synth: erasure introduces no request identities
        assert forall item :: item in EraseAt(queue_out,head) ==> item in queue_out;
// src: src/ast/seq/seq_req_facet.cpp:91 | f.remove(head);
        queue_out := EraseAt(queue_out,head);
// src: src/ast/seq/seq_req_facet.cpp:41 | if (idx < m_qhead)
// src: src/ast/seq/seq_req_facet.cpp:42 | advance_qhead(m_qhead - 1);
        if head < qhead_out { qhead_out := qhead_out - 1; }
// src: src/ast/seq/seq_req_facet.cpp:94 | }
        continue;
// synth: specification, checked proof annotation, or structural delimiter
      }
// src: src/ast/seq/seq_req_facet.cpp:97 | n.set_conflict(stx::br_plugin_base, r.m_dep);
// src: src/ast/seq/seq_req_facet.cpp:98 | return stx::simplify_result::conflict;
      conflict := true; return;
// synth: specification, checked proof annotation, or structural delimiter
    }
// src: src/ast/seq/seq_req_facet.cpp:105 | f.set_status(head, l_undef);
    head := head + 1;
// synth: specification, checked proof annotation, or structural delimiter
  }
// src: src/ast/seq/seq_req_facet.cpp:109 | }
  if head != qhead_out {
// src: src/ast/seq/seq_req_facet.cpp:110 | if (head != f.qhead()) {
    qhead_out := head;
// synth: specification, checked proof annotation, or structural delimiter
  }
// synth: specification, checked proof annotation, or structural delimiter
}

method NfvDomain0()
{
  var out0, out1, out2 := RequestEntry([0, 1, 2, 3], [true, false, true, true], [1, 0, (-1), 1], 0);
}

method NfvDomain1()
{
  var out0, out1, out2 := RequestEntry([0, 1, 2], [true, false, true], [0, (-1), 0], 1);
}

method NfvDomain2()
{
  var out0, out1, out2 := RequestEntry([], [], [], 0);
}
