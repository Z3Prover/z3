// src: src/ast/simplifiers/seq_regular_simplifier.cpp:288 | SASSERT(bound.is_int() && bound >= 0);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:289 | std::string text = bound.to_string();
function Digits(n: int): seq<int>
// synth: checked contract, proof annotation, or structural delimiter
  ensures n >= 0 ==> 0 < |Digits(n)|
// synth: checked contract, proof annotation, or structural delimiter
  decreases if n >= 0 then n else 0
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:288 | SASSERT(bound.is_int() && bound >= 0);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:289 | std::string text = bound.to_string();
  if n < 0 then [] else if n < 10 then [48 + n] else Digits(n / 10) + [48 + n % 10]
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:298 | unsigned digit = text[i] - '0';
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:301 | if (digit < 9) {
function CountLowDigits(ds: seq<int>): int
// synth: checked contract, proof annotation, or structural delimiter
  ensures 0 <= CountLowDigits(ds) <= |ds|
// synth: checked contract, proof annotation, or structural delimiter
  decreases |ds|
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:298 | unsigned digit = text[i] - '0';
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:301 | if (digit < 9) {
  if |ds| == 0 then 0 else CountLowDigits(ds[..|ds| - 1]) + (if ds[|ds| - 1] < 57 then 1 else 0)
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:263 | expr* cat(std::initializer_list<expr*> xs) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:264 | expr* result = epsilon;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:265 | for (expr* x : xs) result = cat(result, x);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:266 | return result;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:290 | if (text.size() > 4096) throw failure::budget;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:292 | expr* digits = decimal_range(0, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:297 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:299 | expr* exact = lit(zstring(static_cast<unsigned>(text[i])));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:300 | greater = cat(exact, greater);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:301 | if (digit < 9) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:302 | expr* higher = decimal_range(digit + 1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:303 | expr* alternative = cat(higher, suffix);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:304 | greater = join(greater, alternative);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:306 | suffix = cat(digits, suffix);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:308 | expr* nonzero = decimal_range(1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:309 | expr* arbitrary = star(digits);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:310 | expr* longer = cat({nonzero, suffix, arbitrary});
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:311 | greater = join(greater, longer);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:312 | expr* zeros = lit(zstring("0"));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:313 | zeros = star(zeros);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:314 | return cat(zeros, greater);
function TickCapacity(bound: int): int
// synth: checked contract, proof annotation, or structural delimiter
  ensures 0 <= TickCapacity(bound)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:263 | expr* cat(std::initializer_list<expr*> xs) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:264 | expr* result = epsilon;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:265 | for (expr* x : xs) result = cat(result, x);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:266 | return result;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:290 | if (text.size() > 4096) throw failure::budget;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:292 | expr* digits = decimal_range(0, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:297 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:299 | expr* exact = lit(zstring(static_cast<unsigned>(text[i])));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:300 | greater = cat(exact, greater);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:301 | if (digit < 9) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:302 | expr* higher = decimal_range(digit + 1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:303 | expr* alternative = cat(higher, suffix);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:304 | greater = join(greater, alternative);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:306 | suffix = cat(digits, suffix);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:308 | expr* nonzero = decimal_range(1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:309 | expr* arbitrary = star(digits);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:310 | expr* longer = cat({nonzero, suffix, arbitrary});
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:311 | greater = join(greater, longer);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:312 | expr* zeros = lit(zstring("0"));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:313 | zeros = star(zeros);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:314 | return cat(zeros, greater);
  if |Digits(bound)| > 4096 then 0 else 10 + 4 * |Digits(bound)| + 3 * CountLowDigits(Digits(bound))
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
function I(xs: seq<int>, k: int): int
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if 0 <= k < |xs| then xs[k] else 0
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
function B(xs: seq<bool>, k: int): bool
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
  0 <= k < |xs| && xs[k]
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
function Scan(inc: seq<bool>, left: int, steps: int, limit: int): seq<int>
// synth: checked contract, proof annotation, or structural delimiter
  ensures |Scan(inc, left, steps, limit)| == 3
// synth: checked contract, proof annotation, or structural delimiter
  decreases if left > 0 then left else 0
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if left <= 0 then [0, steps, 0]
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  else if |inc| == 0 then [3, steps, 0]
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  else if !inc[0] then [2, steps, 1]
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  else if (steps + 1) % 4294967296 > limit then [1, (steps + 1) % 4294967296, 1]
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  else var rest := Scan(inc[1..], left - 1, (steps + 1) % 4294967296, limit);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
       [I(rest, 0), I(rest, 1), 1 + I(rest, 2)]
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:290 | if (text.size() > 4096) throw failure::budget;
function ExpectedStatus(bound: int, inc: seq<bool>, steps: int, limit: int): int
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:290 | if (text.size() > 4096) throw failure::budget;
  if |Digits(bound)| > 4096 then 1 else I(Scan(inc, TickCapacity(bound), steps, limit), 0)
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:290 | if (text.size() > 4096) throw failure::budget;
function ExpectedSteps(bound: int, inc: seq<bool>, steps: int, limit: int): int
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:290 | if (text.size() > 4096) throw failure::budget;
  if |Digits(bound)| > 4096 then steps else I(Scan(inc, TickCapacity(bound), steps, limit), 1)
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:290 | if (text.size() > 4096) throw failure::budget;
function ExpectedUsed(bound: int, inc: seq<bool>, steps: int, limit: int): int
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:290 | if (text.size() > 4096) throw failure::budget;
  if |Digits(bound)| > 4096 then 0 else I(Scan(inc, TickCapacity(bound), steps, limit), 2)
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:292 | expr* digits = decimal_range(0, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:298 | unsigned digit = text[i] - '0';
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:308 | expr* nonzero = decimal_range(1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:312 | expr* zeros = lit(zstring("0"));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:314 | return cat(zeros, greater);
function Stoi(word: seq<int>): int
// synth: checked contract, proof annotation, or structural delimiter
  decreases |word|
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:292 | expr* digits = decimal_range(0, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:298 | unsigned digit = text[i] - '0';
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:308 | expr* nonzero = decimal_range(1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:312 | expr* zeros = lit(zstring("0"));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:314 | return cat(zeros, greater);
  if |word| == 0 then -1
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:292 | expr* digits = decimal_range(0, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:298 | unsigned digit = text[i] - '0';
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:308 | expr* nonzero = decimal_range(1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:312 | expr* zeros = lit(zstring("0"));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:314 | return cat(zeros, greater);
  else if |word| == 1 then (if 48 <= word[0] <= 57 then word[0] - 48 else -1)
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:292 | expr* digits = decimal_range(0, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:298 | unsigned digit = text[i] - '0';
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:308 | expr* nonzero = decimal_range(1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:312 | expr* zeros = lit(zstring("0"));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:314 | return cat(zeros, greater);
  else if 48 <= word[|word| - 1] <= 57 && Stoi(word[..|word| - 1]) >= 0
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:292 | expr* digits = decimal_range(0, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:298 | unsigned digit = text[i] - '0';
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:308 | expr* nonzero = decimal_range(1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:312 | expr* zeros = lit(zstring("0"));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:314 | return cat(zeros, greater);
       then 10 * Stoi(word[..|word| - 1]) + word[|word| - 1] - 48
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:292 | expr* digits = decimal_range(0, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:298 | unsigned digit = text[i] - '0';
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:308 | expr* nonzero = decimal_range(1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:312 | expr* zeros = lit(zstring("0"));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:314 | return cat(zeros, greater);
       else -1
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
function Width(word: seq<int>): int
// synth: checked contract, proof annotation, or structural delimiter
  ensures Width(word) > 0
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
  |word| + 1
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
function TableAt(table: seq<bool>, n: int, i: int, j: int): bool
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
  n > 0 && 0 <= i <= j < n && 0 <= i * n + j < |table| && table[i * n + j]
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:257 | expr* lit(zstring const& s) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:259 | expr_ref str(u.str.mk_string(s), m);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
function Match(word: seq<int>, text: seq<int>, i: int, j: int): bool
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:257 | expr* lit(zstring const& s) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:259 | expr_ref str(u.str.mk_string(s), m);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
  0 <= i <= j <= |word| && word[i..j] == text
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:283 | expr* decimal_range(unsigned lo, unsigned hi) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:285 | return keep(u.re.mk_range(empty->get_sort(), '0' + lo, '0' + hi));
function RangeAt(word: seq<int>, lo: int, hi: int, i: int, j: int): bool
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:283 | expr* decimal_range(unsigned lo, unsigned hi) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:285 | return keep(u.re.mk_range(empty->get_sort(), '0' + lo, '0' + hi));
  0 <= i < |word| && j == i + 1 && lo <= word[i] <= hi
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
function CutAt(a: seq<bool>, b: seq<bool>, n: int, i: int, j: int): bool
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
  n > 0 && 0 <= i <= j < n && exists k: int :: i <= k <= j && TableAt(a, n, i, k) && TableAt(b, n, k, j)
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
function Reach(a: seq<bool>, n: int, i: int, j: int): bool
// synth: checked contract, proof annotation, or structural delimiter
  decreases if 0 <= i <= j then j - i else 0
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
  if n <= 0 || i < 0 || j < i || j >= n then false
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
  else if i == j then true
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
  else exists k: int :: i <= k < j && Reach(a, n, i, k) && TableAt(a, n, k, j)
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:1497 | empty = u.re.mk_empty(re);
function MEmpty(word: seq<int>): seq<bool>
// synth: checked contract, proof annotation, or structural delimiter
  ensures |MEmpty(word)| == Width(word) * Width(word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:1497 | empty = u.re.mk_empty(re);
  seq(Width(word) * Width(word), k => false)
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:1498 | epsilon = u.re.mk_epsilon(s);
function MEpsilon(word: seq<int>): seq<bool>
// synth: checked contract, proof annotation, or structural delimiter
  ensures |MEpsilon(word)| == Width(word) * Width(word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:1498 | epsilon = u.re.mk_epsilon(s);
  seq(Width(word) * Width(word), k => k / Width(word) == k % Width(word))
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:257 | expr* lit(zstring const& s) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:259 | expr_ref str(u.str.mk_string(s), m);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
function MLiteral(text: seq<int>, word: seq<int>): seq<bool>
// synth: checked contract, proof annotation, or structural delimiter
  ensures |MLiteral(text, word)| == Width(word) * Width(word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:257 | expr* lit(zstring const& s) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:259 | expr_ref str(u.str.mk_string(s), m);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
  seq(Width(word) * Width(word), k => Match(word, text, k / Width(word), k % Width(word)))
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:283 | expr* decimal_range(unsigned lo, unsigned hi) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:285 | return keep(u.re.mk_range(empty->get_sort(), '0' + lo, '0' + hi));
function MRange(lo: int, hi: int, word: seq<int>): seq<bool>
// synth: checked contract, proof annotation, or structural delimiter
  ensures |MRange(lo, hi, word)| == Width(word) * Width(word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:283 | expr* decimal_range(unsigned lo, unsigned hi) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:285 | return keep(u.re.mk_range(empty->get_sort(), '0' + lo, '0' + hi));
  seq(Width(word) * Width(word), k => RangeAt(word, lo, hi, k / Width(word), k % Width(word)))
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
function MCat(a: seq<bool>, b: seq<bool>, word: seq<int>): seq<bool>
// synth: checked contract, proof annotation, or structural delimiter
  ensures |MCat(a, b, word)| == Width(word) * Width(word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
  seq(Width(word) * Width(word), k => CutAt(a, b, Width(word), k / Width(word), k % Width(word)))
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
function MUnion(a: seq<bool>, b: seq<bool>, word: seq<int>): seq<bool>
// synth: checked contract, proof annotation, or structural delimiter
  ensures |MUnion(a, b, word)| == Width(word) * Width(word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
  seq(Width(word) * Width(word), k => B(a, k) || B(b, k))
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
function MStar(a: seq<bool>, word: seq<int>): seq<bool>
// synth: checked contract, proof annotation, or structural delimiter
  ensures |MStar(a, word)| == Width(word) * Width(word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
  seq(Width(word) * Width(word), k => Reach(a, Width(word), k / Width(word), k % Width(word)))
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
method Tick(inc: seq<bool>, used: int, steps: int, limit: int) returns (status: int, stepsOut: int, usedOut: int)
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= used < |inc|
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= steps < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= limit < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures usedOut == used + 1
// synth: checked contract, proof annotation, or structural delimiter
  ensures 0 <= stepsOut < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures status == (if !inc[used] then 2 else if (steps + 1) % 4294967296 > limit then 1 else 0)
// synth: checked contract, proof annotation, or structural delimiter
  ensures stepsOut == (if inc[used] then (steps + 1) % 4294967296 else steps)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  usedOut := used + 1;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  stepsOut := steps;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if !inc[used] { status := 2; return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  stepsOut := (steps + 1) % 4294967296;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  status := if stepsOut > limit then 1 else 0;
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:283 | expr* decimal_range(unsigned lo, unsigned hi) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:284 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:285 | return keep(u.re.mk_range(empty->get_sort(), '0' + lo, '0' + hi));
method MakeRange(lo: int, hi: int, word: seq<int>, inc: seq<bool>, used: int, steps: int, limit: int) returns (language: seq<bool>, status: int, stepsOut: int, usedOut: int)
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= used < |inc|
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= steps < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= limit < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures usedOut == used + 1
// synth: checked contract, proof annotation, or structural delimiter
  ensures 0 <= stepsOut < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures status == (if !inc[used] then 2 else if (steps + 1) % 4294967296 > limit then 1 else 0)
// synth: checked contract, proof annotation, or structural delimiter
  ensures stepsOut == (if inc[used] then (steps + 1) % 4294967296 else steps)
// synth: checked contract, proof annotation, or structural delimiter
  ensures status != 0 ==> language == []
// synth: checked contract, proof annotation, or structural delimiter
  ensures status == 0 ==> language == MRange(lo, hi, word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:283 | expr* decimal_range(unsigned lo, unsigned hi) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:284 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:285 | return keep(u.re.mk_range(empty->get_sort(), '0' + lo, '0' + hi));
  language := [];
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:283 | expr* decimal_range(unsigned lo, unsigned hi) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:284 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:285 | return keep(u.re.mk_range(empty->get_sort(), '0' + lo, '0' + hi));
  status, stepsOut, usedOut := Tick(inc, used, steps, limit);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:283 | expr* decimal_range(unsigned lo, unsigned hi) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:284 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:285 | return keep(u.re.mk_range(empty->get_sort(), '0' + lo, '0' + hi));
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:283 | expr* decimal_range(unsigned lo, unsigned hi) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:284 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:285 | return keep(u.re.mk_range(empty->get_sort(), '0' + lo, '0' + hi));
  language := MRange(lo, hi, word);
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:257 | expr* lit(zstring const& s) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:258 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:259 | expr_ref str(u.str.mk_string(s), m);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
method MakeLiteral(text: seq<int>, word: seq<int>, inc: seq<bool>, used: int, steps: int, limit: int) returns (language: seq<bool>, status: int, stepsOut: int, usedOut: int)
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= used < |inc|
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= steps < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= limit < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures usedOut == used + 1
// synth: checked contract, proof annotation, or structural delimiter
  ensures 0 <= stepsOut < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures status == (if !inc[used] then 2 else if (steps + 1) % 4294967296 > limit then 1 else 0)
// synth: checked contract, proof annotation, or structural delimiter
  ensures stepsOut == (if inc[used] then (steps + 1) % 4294967296 else steps)
// synth: checked contract, proof annotation, or structural delimiter
  ensures status != 0 ==> language == []
// synth: checked contract, proof annotation, or structural delimiter
  ensures status == 0 ==> language == MLiteral(text, word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:257 | expr* lit(zstring const& s) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:258 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:259 | expr_ref str(u.str.mk_string(s), m);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
  language := [];
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:257 | expr* lit(zstring const& s) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:258 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:259 | expr_ref str(u.str.mk_string(s), m);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
  status, stepsOut, usedOut := Tick(inc, used, steps, limit);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:257 | expr* lit(zstring const& s) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:258 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:259 | expr_ref str(u.str.mk_string(s), m);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:257 | expr* lit(zstring const& s) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:258 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:259 | expr_ref str(u.str.mk_string(s), m);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:260 | return keep(rw.mk_to_re(str));
  language := MLiteral(text, word);
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
method MakeCat(a: seq<bool>, b: seq<bool>, word: seq<int>, inc: seq<bool>, used: int, steps: int, limit: int) returns (language: seq<bool>, status: int, stepsOut: int, usedOut: int)
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= used < |inc|
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= steps < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= limit < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures usedOut == used + 1
// synth: checked contract, proof annotation, or structural delimiter
  ensures 0 <= stepsOut < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures status == (if !inc[used] then 2 else if (steps + 1) % 4294967296 > limit then 1 else 0)
// synth: checked contract, proof annotation, or structural delimiter
  ensures stepsOut == (if inc[used] then (steps + 1) % 4294967296 else steps)
// synth: checked contract, proof annotation, or structural delimiter
  ensures status != 0 ==> language == []
// synth: checked contract, proof annotation, or structural delimiter
  ensures status == 0 ==> language == MCat(a, b, word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
  language := [];
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
  status, stepsOut, usedOut := Tick(inc, used, steps, limit);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:262 | expr* cat(expr* x, expr* y) { tick(); return keep(rw.mk_re_append(x, y)); }
  language := MCat(a, b, word);
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
method MakeUnion(a: seq<bool>, b: seq<bool>, word: seq<int>, inc: seq<bool>, used: int, steps: int, limit: int) returns (language: seq<bool>, status: int, stepsOut: int, usedOut: int)
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= used < |inc|
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= steps < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= limit < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures usedOut == used + 1
// synth: checked contract, proof annotation, or structural delimiter
  ensures 0 <= stepsOut < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures status == (if !inc[used] then 2 else if (steps + 1) % 4294967296 > limit then 1 else 0)
// synth: checked contract, proof annotation, or structural delimiter
  ensures stepsOut == (if inc[used] then (steps + 1) % 4294967296 else steps)
// synth: checked contract, proof annotation, or structural delimiter
  ensures status != 0 ==> language == []
// synth: checked contract, proof annotation, or structural delimiter
  ensures status == 0 ==> language == MUnion(a, b, word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
  language := [];
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
  status, stepsOut, usedOut := Tick(inc, used, steps, limit);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:268 | expr* join(expr* x, expr* y) { tick(); return keep(rw.mk_union(x, y)); }
  language := MUnion(a, b, word);
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
method MakeStar(a: seq<bool>, word: seq<int>, inc: seq<bool>, used: int, steps: int, limit: int) returns (language: seq<bool>, status: int, stepsOut: int, usedOut: int)
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= used < |inc|
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= steps < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= limit < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures usedOut == used + 1
// synth: checked contract, proof annotation, or structural delimiter
  ensures 0 <= stepsOut < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  ensures status == (if !inc[used] then 2 else if (steps + 1) % 4294967296 > limit then 1 else 0)
// synth: checked contract, proof annotation, or structural delimiter
  ensures stepsOut == (if inc[used] then (steps + 1) % 4294967296 else steps)
// synth: checked contract, proof annotation, or structural delimiter
  ensures status != 0 ==> language == []
// synth: checked contract, proof annotation, or structural delimiter
  ensures status == 0 ==> language == MStar(a, word)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
  language := [];
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
  status, stepsOut, usedOut := Tick(inc, used, steps, limit);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:269 | expr* star(expr* x) { tick(); return keep(rw.mk_star(x)); }
  language := MStar(a, word);
// synth: checked contract, proof annotation, or structural delimiter
}
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:287 | expr* decimal_greater(rational const& bound) {
method DecimalGreater(bound: int, word: seq<int>, incResults: seq<bool>, initialSteps: int, maxSteps: int) returns (language: seq<bool>, status: int, finalSteps: int, used: int)
// synth: checked contract, proof annotation, or structural delimiter
  requires bound >= 0
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= initialSteps < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  requires 0 <= maxSteps < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
  requires |incResults| >= TickCapacity(bound)
// synth: checked contract, proof annotation, or structural delimiter
{
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:287 | expr* decimal_greater(rational const& bound) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:288 | SASSERT(bound.is_int() && bound >= 0);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  language := [];
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:287 | expr* decimal_greater(rational const& bound) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:288 | SASSERT(bound.is_int() && bound >= 0);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  status := 0;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:287 | expr* decimal_greater(rational const& bound) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:288 | SASSERT(bound.is_int() && bound >= 0);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  finalSteps := initialSteps;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:287 | expr* decimal_greater(rational const& bound) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:288 | SASSERT(bound.is_int() && bound >= 0);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:90 | void tick() {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  used := 0;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:289 | std::string text = bound.to_string();
  var text := Digits(bound);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:290 | if (text.size() > 4096) throw failure::budget;
  if |text| > 4096 { status := 1; return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:291 | unsigned size = static_cast<unsigned>(text.size());
  var size := |text|;
// synth: checked contract, proof annotation, or structural delimiter
  assert |incResults| >= 10 + 4 * size + 3 * CountLowDigits(text);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:292 | expr* digits = decimal_range(0, 9);
  var digits: seq<bool>;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:292 | expr* digits = decimal_range(0, 9);
  digits, status, finalSteps, used := MakeRange(0, 9, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:292 | expr* digits = decimal_range(0, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:293 | expr* suffix = epsilon;
  var suffix := MEpsilon(word);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:294 | expr* greater = empty;
  var greater := MEmpty(word);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:295 | // Shared suffixes keep the lexicographic comparison linear in the numeral's size.
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:296 | for (unsigned i = size; i-- > 0;) {
  var i := size;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:295 | // Shared suffixes keep the lexicographic comparison linear in the numeral's size.
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:296 | for (unsigned i = size; i-- > 0;) {
  while i > 0
// synth: checked contract, proof annotation, or structural delimiter
    invariant 0 <= i <= size == |text|
// synth: checked contract, proof annotation, or structural delimiter
    invariant status == 0 && 0 <= finalSteps < 4294967296
// synth: checked contract, proof annotation, or structural delimiter
    invariant 0 <= used <= |incResults|
// synth: checked contract, proof annotation, or structural delimiter
    invariant used == 1 + 4 * (size - i) + 3 * (CountLowDigits(text) - CountLowDigits(text[..i]))
// synth: checked contract, proof annotation, or structural delimiter
    invariant |incResults| >= 10 + 4 * size + 3 * CountLowDigits(text)
// synth: checked contract, proof annotation, or structural delimiter
    decreases i
// synth: checked contract, proof annotation, or structural delimiter
  {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:296 | for (unsigned i = size; i-- > 0;) {
    i := i - 1;
// synth: checked contract, proof annotation, or structural delimiter
    assert CountLowDigits(text[..i + 1]) == CountLowDigits(text[..i]) + (if text[i] < 57 then 1 else 0);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:297 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
    status, finalSteps, used := Tick(incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:297 | tick();
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
    if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:298 | unsigned digit = text[i] - '0';
    var digit := text[i] - 48;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:299 | expr* exact = lit(zstring(static_cast<unsigned>(text[i])));
  var exact: seq<bool>;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:299 | expr* exact = lit(zstring(static_cast<unsigned>(text[i])));
  exact, status, finalSteps, used := MakeLiteral([text[i]], word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:299 | expr* exact = lit(zstring(static_cast<unsigned>(text[i])));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:300 | greater = cat(exact, greater);
  greater, status, finalSteps, used := MakeCat(exact, greater, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:300 | greater = cat(exact, greater);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:301 | if (digit < 9) {
    if digit < 9
// synth: checked contract, proof annotation, or structural delimiter
    {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:302 | expr* higher = decimal_range(digit + 1, 9);
  var higher: seq<bool>;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:302 | expr* higher = decimal_range(digit + 1, 9);
  higher, status, finalSteps, used := MakeRange(digit + 1, 9, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:302 | expr* higher = decimal_range(digit + 1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:303 | expr* alternative = cat(higher, suffix);
  var alternative: seq<bool>;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:303 | expr* alternative = cat(higher, suffix);
  alternative, status, finalSteps, used := MakeCat(higher, suffix, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:303 | expr* alternative = cat(higher, suffix);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:304 | greater = join(greater, alternative);
  greater, status, finalSteps, used := MakeUnion(greater, alternative, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:304 | greater = join(greater, alternative);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// synth: checked contract, proof annotation, or structural delimiter
    }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:306 | suffix = cat(digits, suffix);
  suffix, status, finalSteps, used := MakeCat(digits, suffix, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:306 | suffix = cat(digits, suffix);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// synth: checked contract, proof annotation, or structural delimiter
  }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:308 | expr* nonzero = decimal_range(1, 9);
  var nonzero: seq<bool>;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:308 | expr* nonzero = decimal_range(1, 9);
  nonzero, status, finalSteps, used := MakeRange(1, 9, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:308 | expr* nonzero = decimal_range(1, 9);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:309 | expr* arbitrary = star(digits);
  var arbitrary: seq<bool>;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:309 | expr* arbitrary = star(digits);
  arbitrary, status, finalSteps, used := MakeStar(digits, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:309 | expr* arbitrary = star(digits);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:263 | expr* cat(std::initializer_list<expr*> xs) {
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:264 | expr* result = epsilon;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:310 | expr* longer = cat({nonzero, suffix, arbitrary});
  var longer := MEpsilon(word);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:265 | for (expr* x : xs) result = cat(result, x);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:310 | expr* longer = cat({nonzero, suffix, arbitrary});
  longer, status, finalSteps, used := MakeCat(longer, nonzero, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:265 | for (expr* x : xs) result = cat(result, x);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:310 | expr* longer = cat({nonzero, suffix, arbitrary});
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:265 | for (expr* x : xs) result = cat(result, x);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:310 | expr* longer = cat({nonzero, suffix, arbitrary});
  longer, status, finalSteps, used := MakeCat(longer, suffix, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:265 | for (expr* x : xs) result = cat(result, x);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:310 | expr* longer = cat({nonzero, suffix, arbitrary});
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:265 | for (expr* x : xs) result = cat(result, x);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:310 | expr* longer = cat({nonzero, suffix, arbitrary});
  longer, status, finalSteps, used := MakeCat(longer, arbitrary, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:265 | for (expr* x : xs) result = cat(result, x);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:310 | expr* longer = cat({nonzero, suffix, arbitrary});
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:311 | greater = join(greater, longer);
  greater, status, finalSteps, used := MakeUnion(greater, longer, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:311 | greater = join(greater, longer);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:312 | expr* zeros = lit(zstring("0"));
  var zeros: seq<bool>;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:312 | expr* zeros = lit(zstring("0"));
  zeros, status, finalSteps, used := MakeLiteral([48], word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:312 | expr* zeros = lit(zstring("0"));
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:313 | zeros = star(zeros);
  zeros, status, finalSteps, used := MakeStar(zeros, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:313 | zeros = star(zeros);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:314 | return cat(zeros, greater);
  language, status, finalSteps, used := MakeCat(zeros, greater, word, incResults, used, finalSteps, maxSteps);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:314 | return cat(zeros, greater);
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:91 | if (!m.inc()) throw failure::canceled;
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:92 | if (++steps > max_steps) throw failure::budget;
  if status != 0 { return; }
// src: src/ast/simplifiers/seq_regular_simplifier.cpp:315 | }
}
