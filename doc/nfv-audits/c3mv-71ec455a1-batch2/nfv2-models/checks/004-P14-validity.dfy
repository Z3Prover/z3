// src: src/ast/simplifiers/seq_regular_simplifier.cpp:774 | if (u.str.is_at(term, s, i)) {
function StrAt(word: seq<int>, index: int): seq<int>
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:774 | if (u.str.is_at(term, s, i)) {
  if 0 <= index < |word| then [word[index]] else []
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:775 | expr* one = meet(r, character);
function TargetAccepts(value: seq<int>, allowed_characters: seq<int>, accepts_empty: bool): bool
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:775 | expr* one = meet(r, character);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:780 | result = join(yes, nullable(r) ? length(0, k) : empty);
  if |value| == 0 then accepts_empty else |value| == 1 && value[0] in allowed_characters
// synth: specification, checked proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:774 | if (u.str.is_at(term, s, i)) {
method PreimageEntry(word: seq<int>, allowed_characters: seq<int>, accepts_empty: bool, last_index: bool, k: int) returns (rewritten_accepts: bool)
// synth: specification, checked proof annotation, or structural delimiter
  requires 0 <= k <= 64
// synth: specification, checked proof annotation, or structural delimiter
  requires |word| < 4294967296
// synth: specification, checked proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:777 | if (a.is_numeral(i, v) && v.is_unsigned() && v <= rational(64)) {
  if !last_index {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:779 | expr* yes = cat({length(k, k), one, all});
    var yes := k < |word| && word[k] in allowed_characters;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:780 | result = join(yes, nullable(r) ? length(0, k) : empty);
    var absent := accepts_empty && |word| <= k;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:780 | result = join(yes, nullable(r) ? length(0, k) : empty);
    rewritten_accepts := yes || absent;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:782 | else {
  } else {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:786 | expr* yes = cat(all, one);
    var yes := exists cut :: 0 <= cut < |word| && cut + 1 == |word| && word[cut] in allowed_characters;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:787 | result = join(yes, nullable(r) ? epsilon : empty);
    rewritten_accepts := yes || (accepts_empty && |word| == 0);
// synth: specification, checked proof annotation, or structural delimiter
  }
// synth: specification, checked proof annotation, or structural delimiter
}
