// src: src/solver/assertions/asserted_formulas.cpp:360 | if (seq.str.is_contains(e, haystack, query) && haystack == arg &&
function HasCharacter(word: seq<int>, character: int): bool
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/solver/assertions/asserted_formulas.cpp:360 | if (seq.str.is_contains(e, haystack, query) && haystack == arg &&
  character in word
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/util/zstring.cpp:131 | for (unsigned j = 0; eq && j < src.length(); ++j) {
function MatchFrom(word: seq<int>, needle: seq<int>, index: int, offset: int): bool
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 <= index <= |word| && index + |needle| <= |word|
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 <= offset <= |needle|
// synth: specification, checked proof annotation, or structural delimiter
  ensures MatchFrom(word,needle,index,offset) == (word[index+offset..index+|needle|] == needle[offset..])
// synth: specification, checked proof annotation, or structural delimiter
  decreases |needle| - offset
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/util/zstring.cpp:131 | for (unsigned j = 0; eq && j < src.length(); ++j) {
// src: src/util/zstring.cpp:132 | eq = m_buffer[i+j] == src[j];
  if offset == |needle| then true else word[index+offset] == needle[offset] && MatchFrom(word,needle,index,offset+1)
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/util/zstring.cpp:129 | for (unsigned i = 0; i < length(); ++i) {
function ReplaceScan(word: seq<int>, needle: seq<int>, replacement: seq<int>, index: int, found: bool): seq<int>
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 < |needle|
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 <= index <= |word|
// synth: specification, checked proof annotation, or structural delimiter
  decreases |word| - index
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/util/zstring.cpp:129 | for (unsigned i = 0; i < length(); ++i) {
// src: src/util/zstring.cpp:130 | bool eq = !found && i + src.length() <= length();
// src: src/util/zstring.cpp:134 | if (eq) {
// src: src/util/zstring.cpp:135 | result.m_buffer.append(dst.m_buffer);
// src: src/util/zstring.cpp:136 | found = true;
// src: src/util/zstring.cpp:137 | i += src.length() - 1;
// src: src/util/zstring.cpp:140 | result.m_buffer.push_back(m_buffer[i]);
  if index == |word| then [] else if !found && index+|needle| <= |word| && MatchFrom(word,needle,index,0) then replacement + ReplaceScan(word,needle,replacement,index+|needle|,true) else [word[index]] + ReplaceScan(word,needle,replacement,index+1,found)
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/util/zstring.cpp:120 | zstring zstring::replace(zstring const& src, zstring const& dst) const {
function ReplaceFirst(word: seq<int>, needle: seq<int>, replacement: seq<int>): seq<int>
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/util/zstring.cpp:122 | if (length() < src.length()) {
// src: src/util/zstring.cpp:123 | return zstring(*this);
// src: src/util/zstring.cpp:125 | if (src.length() == 0) {
// src: src/util/zstring.cpp:126 | return dst + zstring(*this);
// src: src/util/zstring.cpp:128 | bool found = false;
// src: src/util/zstring.cpp:129 | for (unsigned i = 0; i < length(); ++i) {
  if |word| < |needle| then word else if |needle| == 0 then replacement + word else ReplaceScan(word,needle,replacement,0,false)
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/util/zstring.cpp:129 | for (unsigned i = 0; i < length(); ++i) {
lemma ScanPreserves(word: seq<int>, needle: seq<int>, replacement: seq<int>, character: int, index: int, found: bool)
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 < |needle| && 0 <= index <= |word|
// synth: specification, checked proof annotation, or structural delimiter
  requires !HasCharacter(needle,character) && !HasCharacter(replacement,character)
// synth: specification, checked proof annotation, or structural delimiter
  ensures HasCharacter(ReplaceScan(word,needle,replacement,index,found),character) == HasCharacter(word[index..],character)
// synth: specification, checked proof annotation, or structural delimiter
  decreases |word| - index
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/util/zstring.cpp:129 | for (unsigned i = 0; i < length(); ++i) {
  if index < |word| {
// src: src/util/zstring.cpp:130 | bool eq = !found && i + src.length() <= length();
    if !found && index+|needle| <= |word| && MatchFrom(word,needle,index,0) {
// src: src/util/zstring.cpp:135 | result.m_buffer.append(dst.m_buffer);
// src: src/util/zstring.cpp:136 | found = true;
// src: src/util/zstring.cpp:137 | i += src.length() - 1;
      ScanPreserves(word,needle,replacement,character,index+|needle|,true);
// synth: specification, checked proof annotation, or structural delimiter
      assert word[index..index+|needle|] == needle;
// synth: specification, checked proof annotation, or structural delimiter
      assert word[index..] == word[index..index+|needle|] + word[index+|needle|..];
// synth: specification, checked proof annotation, or structural delimiter
    } else {
// src: src/util/zstring.cpp:140 | result.m_buffer.push_back(m_buffer[i]);
      ScanPreserves(word,needle,replacement,character,index+1,found);
// synth: specification, checked proof annotation, or structural delimiter
      assert word[index..] == [word[index]] + word[index+1..];
// synth: specification, checked proof annotation, or structural delimiter
    }
// synth: specification, checked proof annotation, or structural delimiter
  }
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/solver/assertions/asserted_formulas.cpp:317 | bool asserted_formulas::simplify_replace_contains() {
method ObservationEntry(word: seq<int>, needle: seq<int>, replacement: seq<int>, character: int) returns (rewritten_contains: bool)
// synth: specification, checked proof annotation, or structural delimiter
  requires !HasCharacter(needle,character)
// synth: specification, checked proof annotation, or structural delimiter
  requires !HasCharacter(replacement,character)
// synth: specification, checked proof annotation, or structural delimiter
  requires |word| < 2147483648 && |needle| < 2147483648 && |replacement| < 2147483648
// synth: specification, checked proof annotation, or structural delimiter
  ensures rewritten_contains == HasCharacter(ReplaceFirst(word,needle,replacement),character)
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/util/zstring.cpp:122 | if (length() < src.length()) {
// src: src/util/zstring.cpp:125 | if (src.length() == 0) {
  if 0 < |needle| <= |word| {
// src: src/util/zstring.cpp:129 | for (unsigned i = 0; i < length(); ++i) {
    ScanPreserves(word,needle,replacement,character,0,false);
// synth: specification, checked proof annotation, or structural delimiter
  }
// src: src/solver/assertions/asserted_formulas.cpp:399 | expr_ref preserved(seq.str.mk_contains(to_app(replaced)->get_arg(0), p->get_arg(1)), m);
  rewritten_contains := HasCharacter(word,character);
// synth: specification, checked proof annotation, or structural delimiter
}
