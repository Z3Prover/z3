// src: src/ast/seq/seq_power_facet.cpp:283 | static bool has_period(zstring const& s, unsigned r) {
ghost predicate Period(s: seq<int>, r: int)
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:284 | for (unsigned i = 0; i + r < s.length(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:285 | if (s[i] != s[i + r])
  forall i :: 0 <= i < |s| && 0 <= i+r < |s| ==> s[i] == s[i+r]
// synth: specification, invariant, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:283 | static bool has_period(zstring const& s, unsigned r) {
method CheckPeriod(s: seq<int>, r: int) returns (ok: bool)
// synth: specification, invariant, or structural delimiter
  requires 1 <= r <= |s| < 2147483647
// synth: specification, invariant, or structural delimiter
  ensures ok == Period(s,r)
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:284 | for (unsigned i = 0; i + r < s.length(); ++i) {
  var i := 0;
// src: src/ast/seq/seq_power_facet.cpp:284 | for (unsigned i = 0; i + r < s.length(); ++i) {
  while i+r < |s|
// synth: specification, invariant, or structural delimiter
    invariant 0 <= i <= |s| - r
// synth: specification, invariant, or structural delimiter
    invariant forall j :: 0 <= j < i ==> s[j] == s[j+r]
// synth: specification, invariant, or structural delimiter
    decreases |s| - r - i
// synth: specification, invariant, or structural delimiter
  {
// src: src/ast/seq/seq_power_facet.cpp:285 | if (s[i] != s[i + r])
    if s[i] != s[i+r] {
// src: src/ast/seq/seq_power_facet.cpp:286 | return false;
      ok := false; return;
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/seq/seq_power_facet.cpp:284 | for (unsigned i = 0; i + r < s.length(); ++i) {
    i := i+1;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_power_facet.cpp:288 | return true;
  ok := true;
// synth: specification, invariant, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:291 | static zstring primitive_root(zstring const& s) {
method PrimitiveEntry(s: seq<int>) returns (root: seq<int>)
// synth: specification, invariant, or structural delimiter
  requires 0 < |s| < 2147483647
// synth: specification, invariant, or structural delimiter
  ensures 0 < |root| <= |s| && root == s[..|root|]
// synth: specification, invariant, or structural delimiter
  ensures |s| % |root| == 0 && Period(s,|root|)
// synth: specification, invariant, or structural delimiter
  ensures forall k :: 1 <= k < |root| ==> |s| % k != 0 || !Period(s,k)
// synth: specification, invariant, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:292 | for (unsigned d = 1; d < s.length(); ++d) {
  var d := 1;
// src: src/ast/seq/seq_power_facet.cpp:292 | for (unsigned d = 1; d < s.length(); ++d) {
  while d < |s|
// synth: specification, invariant, or structural delimiter
    invariant 1 <= d <= |s|
// synth: specification, invariant, or structural delimiter
    invariant forall k :: 1 <= k < d ==> |s| % k != 0 || !Period(s,k)
// synth: specification, invariant, or structural delimiter
    decreases |s| - d
// synth: specification, invariant, or structural delimiter
  {
// src: src/ast/seq/seq_power_facet.cpp:293 | if (s.length() % d == 0 && has_period(s, d))
    if |s| % d == 0 {
// src: src/ast/seq/seq_power_facet.cpp:293 | if (s.length() % d == 0 && has_period(s, d))
      var yes := CheckPeriod(s,d);
// src: src/ast/seq/seq_power_facet.cpp:293 | if (s.length() % d == 0 && has_period(s, d))
      if yes {
// src: src/ast/seq/seq_power_facet.cpp:294 | return s.extract(0, d);
        root := s[..d]; return;
// synth: specification, invariant, or structural delimiter
      }
// synth: specification, invariant, or structural delimiter
    }
// src: src/ast/seq/seq_power_facet.cpp:292 | for (unsigned d = 1; d < s.length(); ++d) {
    d := d+1;
// synth: specification, invariant, or structural delimiter
  }
// src: src/ast/seq/seq_power_facet.cpp:296 | return s;
  root := s;
// synth: specification, invariant, or structural delimiter
}
