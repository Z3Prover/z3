// src: src/util/vector.h:447 | void erase(iterator pos) {
method EraseLeft(original: seq<int>, index: int) returns (erased: seq<int>)
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 <= index < |original|
// synth: specification, checked proof annotation, or structural delimiter
  ensures erased == original[..index] + original[index+1..]
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/util/vector.h:449 | iterator prev = pos;
  erased := original;
// src: src/util/vector.h:449 | iterator prev = pos;
  var pos := index;
// src: src/util/vector.h:451 | iterator e    = end();
  while pos + 1 < |erased|
// synth: specification, checked proof annotation, or structural delimiter
    invariant |erased| == |original|
// synth: specification, checked proof annotation, or structural delimiter
    invariant index <= pos < |erased|
// synth: specification, checked proof annotation, or structural delimiter
    invariant erased[..index] == original[..index]
// synth: specification, checked proof annotation, or structural delimiter
    invariant erased[index..pos] == original[index+1..pos+1]
// synth: specification, checked proof annotation, or structural delimiter
    invariant erased[pos..] == original[pos..]
// synth: specification, checked proof annotation, or structural delimiter
    decreases |erased| - pos
// synth: specification, checked proof annotation, or structural delimiter
  {
// src: src/util/vector.h:452 | for(; pos != e; ++pos, ++prev) {
    erased := erased[pos := erased[pos+1]];
// src: src/util/vector.h:451 | iterator e    = end();
    pos := pos + 1;
// synth: specification, checked proof annotation, or structural delimiter
  }
// src: src/util/vector.h:454 | }
  erased := erased[..|erased|-1];
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/ast/seq/seq_eq_facet.h:84 | void undo() override {
method RestorationEntry(original: seq<int>, index: int) returns (restored: seq<int>)
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 <= index < |original| < 4294967296
// synth: specification, checked proof annotation, or structural delimiter
  ensures restored == original
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/ast/seq/seq_eq_facet.h:83 | vector_erase_trail(vector<T>& v, unsigned idx) : m_vec(v), m_idx(idx), m_value(v[idx]) {}
  var saved := original[index];
// src: src/ast/seq/seq_req_facet.cpp:38 | m_reqs.erase(m_reqs.begin() + idx);
// src: src/ast/seq/seq_req_facet.cpp:39 | // Removing a resolved request below `m_qhead` shifts later entries
  restored := EraseLeft(original,index);
// src: src/ast/seq/seq_eq_facet.h:86 | m_vec.push_back(m_value);
  restored := restored + [saved];
// src: src/ast/seq/seq_eq_facet.h:87 | for (unsigned i = m_vec.size() - 1; i > m_idx; --i)
  var i := |restored| - 1;
// src: src/ast/seq/seq_eq_facet.h:87 | for (unsigned i = m_vec.size() - 1; i > m_idx; --i)
  while i > index
// synth: specification, checked proof annotation, or structural delimiter
    invariant |restored| == |original|
// synth: specification, checked proof annotation, or structural delimiter
    invariant index <= i < |restored|
// synth: specification, checked proof annotation, or structural delimiter
    invariant restored[..index] == original[..index]
// synth: specification, checked proof annotation, or structural delimiter
    invariant restored[index..i] == original[index+1..i+1]
// synth: specification, checked proof annotation, or structural delimiter
    invariant restored[i+1..] == original[i+1..]
// synth: specification, checked proof annotation, or structural delimiter
    decreases i - index
// synth: specification, checked proof annotation, or structural delimiter
  {
// src: src/ast/seq/seq_eq_facet.h:88 | m_vec[i] = std::move(m_vec[i - 1]);
    restored := restored[i := restored[i-1]];
// src: src/ast/seq/seq_eq_facet.h:87 | for (unsigned i = m_vec.size() - 1; i > m_idx; --i)
    i := i - 1;
// synth: specification, checked proof annotation, or structural delimiter
  }
// src: src/ast/seq/seq_eq_facet.h:89 | m_vec[m_idx] = std::move(m_value);
  restored := restored[index := saved];
// synth: specification, checked proof annotation, or structural delimiter
}
