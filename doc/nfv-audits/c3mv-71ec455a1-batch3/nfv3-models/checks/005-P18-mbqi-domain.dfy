// src: src/ast/seq/seq_power_facet.cpp:131 | expr_ref rhs(m);
// src: src/ast/seq/seq_power_facet.cpp:132 | if (!v.is_pos())
// src: src/ast/seq/seq_power_facet.cpp:135 | rhs = mk_power_unfold(u, m, p.m_s.get(), v.get_unsigned());
function Power(word: seq<int>, n: int): seq<int>
// synth: specification, checked annotation, or structural delimiter
  decreases if n > 0 then n else 0
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:132 | if (!v.is_pos())
// src: src/ast/seq/seq_power_facet.cpp:135 | rhs = mk_power_unfold(u, m, p.m_s.get(), v.get_unsigned());
  if n <= 0 then [] else word + Power(word,n-1)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:466 | expr_ref_vector xs(m), ys(m);
// src: src/ast/seq/seq_power_facet.cpp:467 | u.str.get_concat_units(X, xs);
predicate TokenView(word: seq<int>, bounds: seq<int>, flags: seq<bool>)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:466 | expr_ref_vector xs(m), ys(m);
// src: src/ast/seq/seq_power_facet.cpp:467 | u.str.get_concat_units(X, xs);
  |bounds| == |flags| + 1 && bounds[0] == 0 && bounds[|flags|] == |word| && (forall j :: 0 <= j < |flags| ==> 0 <= bounds[j] <= bounds[j+1] <= |word| && (flags[j] ==> bounds[j+1] == bounds[j]+1))
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:271 | static bool constant_word(seq_util& u, expr_ref_vector const& toks, zstring& s) {
function ConstantWord(word: seq<int>, bounds: seq<int>, flags: seq<bool>, i: int, acc: seq<int>): (bool,seq<int>)
// synth: specification, checked annotation, or structural delimiter
  requires TokenView(word,bounds,flags) && 0 <= i <= |flags|
// synth: specification, checked annotation, or structural delimiter
  requires acc == word[..bounds[i]]
// synth: specification, checked annotation, or structural delimiter
  ensures ConstantWord(word,bounds,flags,i,acc).0 ==> ConstantWord(word,bounds,flags,i,acc).1 == word && 0 < |word|
// synth: specification, checked annotation, or structural delimiter
  decreases |flags| - i
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:273 | for (expr* t : toks) {
// src: src/ast/seq/seq_power_facet.cpp:276 | if (!u.str.is_unit(t, ch) || !u.is_const_char(ch, c))
// src: src/ast/seq/seq_power_facet.cpp:277 | return false;
// src: src/ast/seq/seq_power_facet.cpp:278 | s += zstring(c);
// src: src/ast/seq/seq_power_facet.cpp:280 | return !s.empty();
  if i == |flags| then (0 < |acc|,acc) else if !flags[i] then (false,acc) else ConstantWord(word,bounds,flags,i+1,acc+[word[bounds[i]]])
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:283 | static bool has_period(zstring const& s, unsigned r) {
function PeriodScan(word: seq<int>, r: int, i: int): bool
// synth: specification, checked annotation, or structural delimiter
  requires r > 0 && i >= 0
// synth: specification, checked annotation, or structural delimiter
  decreases if i+r < |word| then |word|-i-r else 0
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:284 | for (unsigned i = 0; i + r < s.length(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:285 | if (s[i] != s[i + r])
// src: src/ast/seq/seq_power_facet.cpp:286 | return false;
// src: src/ast/seq/seq_power_facet.cpp:288 | return true;
  if i+r >= |word| then true else word[i] == word[i+r] && PeriodScan(word,r,i+1)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:291 | static zstring primitive_root(zstring const& s) {
function RootScan(word: seq<int>, d: int): seq<int>
// synth: specification, checked annotation, or structural delimiter
  requires 0 < |word| && 1 <= d <= |word|
// synth: specification, checked annotation, or structural delimiter
  ensures 0 < |RootScan(word,d)| <= |word|
// synth: specification, checked annotation, or structural delimiter
  decreases |word| - d
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:292 | for (unsigned d = 1; d < s.length(); ++d) {
// src: src/ast/seq/seq_power_facet.cpp:293 | if (s.length() % d == 0 && has_period(s, d))
// src: src/ast/seq/seq_power_facet.cpp:294 | return s.extract(0, d);
// src: src/ast/seq/seq_power_facet.cpp:296 | return s;
  if d == |word| then word else if |word| % d == 0 && PeriodScan(word,d,0) then word[..d] else RootScan(word,d+1)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:291 | static zstring primitive_root(zstring const& s) {
function PrimitiveRoot(word: seq<int>): seq<int>
// synth: specification, checked annotation, or structural delimiter
  requires 0 < |word|
// synth: specification, checked annotation, or structural delimiter
  ensures 0 < |PrimitiveRoot(word)| <= |word|
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:292 | for (unsigned d = 1; d < s.length(); ++d) {
// src: src/ast/seq/seq_power_facet.cpp:296 | return s;
  RootScan(word,1)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:447 | if (has_period(sx, r) && (!gy || (sy.length() >= sx.length() + r && (sy.length() - r) % sx.length() == 0)))
function U32(value: int): int
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:447 | if (has_period(sx, r) && (!gy || (sy.length() >= sx.length() + r && (sy.length() - r) % sx.length() == 0)))
  value % 4294967296
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:414 | void power_trichotomy::enumerate(eq_tree::node& n, trigger const& t, branches& out) const {
// src: src/ast/seq/seq_power_facet.cpp:431 | zstring sx, sy;
// src: src/ast/seq/seq_power_facet.cpp:443 | if (!gx)
predicate EnumerationDomain(b: int, param: int, A: seq<int>, B: seq<int>, aBounds: seq<int>, bBounds: seq<int>, aLiteral: seq<bool>, bLiteral: seq<bool>)
// synth: specification, checked annotation, or structural delimiter
  requires 0 <= b < 10
// synth: specification, checked annotation, or structural delimiter
  requires TokenView(A,aBounds,aLiteral) && TokenView(B,bBounds,bLiteral)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:431 | zstring sx, sy;
// src: src/ast/seq/seq_power_facet.cpp:455 | void power_trichotomy::apply(eq_tree::node& n, trigger const& t, unsigned b, unsigned param) const {
// src: src/ast/seq/seq_power_facet.cpp:460 | bool dir_u = b < 5;
  var X := if b < 5 then A else B;
// src: src/ast/seq/seq_power_facet.cpp:431 | zstring sx, sy;
// src: src/ast/seq/seq_power_facet.cpp:455 | void power_trichotomy::apply(eq_tree::node& n, trigger const& t, unsigned b, unsigned param) const {
// src: src/ast/seq/seq_power_facet.cpp:460 | bool dir_u = b < 5;
  var Y := if b < 5 then B else A;
// src: src/ast/seq/seq_power_facet.cpp:431 | zstring sx, sy;
// src: src/ast/seq/seq_power_facet.cpp:473 | auto mk_pow = [&](expr* base, expr* exp) {
  var gx := ConstantWord(X,if b < 5 then aBounds else bBounds,if b < 5 then aLiteral else bLiteral,0,[]).0;
// src: src/ast/seq/seq_power_facet.cpp:431 | zstring sx, sy;
// src: src/ast/seq/seq_power_facet.cpp:473 | auto mk_pow = [&](expr* base, expr* exp) {
  var gy := ConstantWord(Y,if b < 5 then bBounds else aBounds,if b < 5 then bLiteral else aLiteral,0,[]).0;
// src: src/ast/seq/seq_power_facet.cpp:441 | if (!(gx && gy && sx + sy != sy + sx))
// src: src/ast/seq/seq_power_facet.cpp:442 | out.push_back({b + 2, 0});
// src: src/ast/seq/seq_power_facet.cpp:443 | if (!gx)
// src: src/ast/seq/seq_power_facet.cpp:444 | out.push_back({b + 3, 0});
// src: src/ast/seq/seq_power_facet.cpp:446 | for (unsigned r = 1; r < sx.length(); ++r) {
// src: src/ast/seq/seq_power_facet.cpp:447 | if (has_period(sx, r) && (!gy || (sy.length() >= sx.length() + r && (sy.length() - r) % sx.length() == 0)))
// src: src/ast/seq/seq_power_facet.cpp:448 | out.push_back({b + 3, r});
  (if b % 5 == 3 then (gx <==> param > 0) && (param > 0 ==> param < |X| && PeriodScan(X,param,0)) && (gx && gy ==> |Y| >= U32(|X|+param) && U32(|Y|-param) % |X| == 0) else param == 0) && (b % 5 == 2 && gx && gy ==> X+Y == Y+X) && (gx ==> |X| < 4294967296) && (gy ==> |Y| < 4294967296)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:455 | void power_trichotomy::apply(eq_tree::node& n, trigger const& t, unsigned b, unsigned param) const {
// src: src/ast/seq/seq_power_facet.cpp:456 | auto ac = get_ambient(n);
// src: src/ast/seq/seq_power_facet.cpp:457 | auto& f = ac.power_facet_ref();
// src: src/ast/seq/seq_power_facet.cpp:458 | auto& ef = ac.eq_facet_ref();
// src: src/ast/seq/seq_power_facet.cpp:459 | auto& sf = ac.solver_facet_ref();
// src: src/ast/seq/seq_power_facet.cpp:464 | eq_tree::dep_tracker dep = t.m_dep;
// src: src/ast/seq/seq_power_facet.cpp:468 | u.str.get_concat_units(Y, ys);
// src: src/ast/seq/seq_power_facet.cpp:469 | zstring sx, sy;
method PowerRewriteEntry(b: int, param: int, A: seq<int>, B: seq<int>, aBounds: seq<int>, bBounds: seq<int>, aLiteral: seq<bool>, bLiteral: seq<bool>, expA: int, expB: int, y1: seq<int>, y2: seq<int>, wFresh: seq<int>, iFresh: int, jFresh: int, p1Fresh: seq<int>, p2Fresh: seq<int>, kFresh: int, qFresh: int) returns (constraints_ok: bool, fromWord: seq<int>, toWord: seq<int>)
// synth: specification, checked annotation, or structural delimiter
  requires 0 <= b < 10 && 0 <= param < 4294967296
// synth: specification, checked annotation, or structural delimiter
  requires TokenView(A,aBounds,aLiteral) && TokenView(B,bBounds,bLiteral)
// synth: specification, checked annotation, or structural delimiter
  requires |aLiteral| < 4294967296 && |bLiteral| < 4294967296
// synth: specification, checked annotation, or structural delimiter
  requires EnumerationDomain(b,param,A,B,aBounds,bBounds,aLiteral,bLiteral)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:460 | bool dir_u = b < 5;
  var dir_u := b < 5;
// src: src/ast/seq/seq_power_facet.cpp:462 | str_power px = f.powers()[dir_u ? t.m_x_idx : t.m_y_idx]; // the shorter power X^M
// src: src/ast/seq/seq_power_facet.cpp:465 | expr* X = px.m_s, *M = px.m_n, *Y = py.m_s, *N = py.m_n;
  var X := if dir_u then A else B;
// src: src/ast/seq/seq_power_facet.cpp:463 | str_power py = f.powers()[dir_u ? t.m_y_idx : t.m_x_idx]; // the longer power Y^N
// src: src/ast/seq/seq_power_facet.cpp:465 | expr* X = px.m_s, *M = px.m_n, *Y = py.m_s, *N = py.m_n;
  var Y := if dir_u then B else A;
// src: src/ast/seq/seq_power_facet.cpp:462 | str_power px = f.powers()[dir_u ? t.m_x_idx : t.m_y_idx]; // the shorter power X^M
// src: src/ast/seq/seq_power_facet.cpp:465 | expr* X = px.m_s, *M = px.m_n, *Y = py.m_s, *N = py.m_n;
  var M := if dir_u then expA else expB;
// src: src/ast/seq/seq_power_facet.cpp:463 | str_power py = f.powers()[dir_u ? t.m_y_idx : t.m_x_idx]; // the longer power Y^N
// src: src/ast/seq/seq_power_facet.cpp:465 | expr* X = px.m_s, *M = px.m_n, *Y = py.m_s, *N = py.m_n;
  var N := if dir_u then expB else expA;
// src: src/ast/seq/seq_power_facet.cpp:466 | expr_ref_vector xs(m), ys(m);
// src: src/ast/seq/seq_power_facet.cpp:467 | u.str.get_concat_units(X, xs);
// src: src/ast/seq/seq_power_facet.cpp:470 | bool gx = constant_word(u, xs, sx), gy = constant_word(u, ys, sy);
  var cx := ConstantWord(X,if dir_u then aBounds else bBounds,if dir_u then aLiteral else bLiteral,0,[]);
// src: src/ast/seq/seq_power_facet.cpp:466 | expr_ref_vector xs(m), ys(m);
// src: src/ast/seq/seq_power_facet.cpp:468 | u.str.get_concat_units(Y, ys);
// src: src/ast/seq/seq_power_facet.cpp:470 | bool gx = constant_word(u, xs, sx), gy = constant_word(u, ys, sy);
  var cy := ConstantWord(Y,if dir_u then bBounds else aBounds,if dir_u then bLiteral else aLiteral,0,[]);
// src: src/ast/seq/seq_power_facet.cpp:470 | bool gx = constant_word(u, xs, sx), gy = constant_word(u, ys, sy);
  var gx, sx := cx.0, cx.1;
// src: src/ast/seq/seq_power_facet.cpp:470 | bool gx = constant_word(u, xs, sx), gy = constant_word(u, ys, sy);
  var gy, sy := cy.0, cy.1;
// src: src/ast/seq/seq_power_facet.cpp:472 | auto constrain = [&](expr* c) { sf.add_constraint(c, dep); };
// src: src/ast/seq/seq_power_facet.cpp:499 | constrain(dir_u ? a.mk_le(mk_len(u, m, px.m_e), mk_len(u, m, py.m_e))
// src: src/ast/seq/seq_power_facet.cpp:500 | : a.mk_lt(mk_len(u, m, px.m_e), mk_len(u, m, py.m_e)));
  constraints_ok := if dir_u then |Power(X,M)| <= |Power(Y,N)| else |Power(X,M)| < |Power(Y,N)|;
// src: src/ast/seq/seq_power_facet.cpp:473 | auto mk_pow = [&](expr* base, expr* exp) {
// src: src/ast/seq/seq_power_facet.cpp:474 | expr_ref e = mk_exp(m, exp);
// src: src/ast/seq/seq_power_facet.cpp:475 | expr_ref tok(u.str.mk_power(base, e), m);
// src: src/ast/seq/seq_power_facet.cpp:476 | f.add_power(tok, base, e, dep);
// src: src/ast/seq/seq_power_facet.cpp:483 | u.str.get_concat_units(u.str.mk_string(s), r);
// src: src/ast/seq/seq_power_facet.cpp:484 | return r;
// src: src/ast/seq/seq_power_facet.cpp:485 | };
// src: src/ast/seq/seq_power_facet.cpp:487 | expr_ref_vector r(m);
// src: src/ast/seq/seq_power_facet.cpp:489 | return r;
// src: src/ast/seq/seq_power_facet.cpp:490 | };
// src: src/ast/seq/seq_power_facet.cpp:491 | auto cat = [&](std::initializer_list<expr_ref_vector> parts) {
// src: src/ast/seq/seq_power_facet.cpp:492 | expr_ref_vector r(m);
// src: src/ast/seq/seq_power_facet.cpp:493 | for (auto const& p : parts) {
// src: src/ast/seq/seq_power_facet.cpp:503 | expr_ref_vector z(m);
  var z: seq<int> := [];
// src: src/ast/seq/seq_power_facet.cpp:504 | switch (b % 5) {
  if b % 5 == 0 {
// src: src/ast/seq/seq_power_facet.cpp:507 | constrain(m.mk_or(a.mk_le(M, a.mk_int(0)), m.mk_eq(mk_len_sum(u, a, m, xs, 0, xs.size()), a.mk_int(0))));
    constraints_ok := constraints_ok && (M <= 0 || |X| == 0);
// src: src/ast/seq/seq_power_facet.cpp:508 | broadcast_subst(n, px.m_e, expr_ref_vector(m), dep);
    fromWord := Power(X,M);
// src: src/ast/seq/seq_power_facet.cpp:508 | broadcast_subst(n, px.m_e, expr_ref_vector(m), dep);
    toWord := [];
// src: src/ast/seq/seq_power_facet.cpp:509 | return;
    return;
// src: src/ast/seq/seq_power_facet.cpp:510 | case 1: {
  } else if b % 5 == 1 {
// src: src/ast/seq/seq_power_facet.cpp:512 | expr_ref y1 = fresh_str("power-trichotomy-f1-y");
// src: src/ast/seq/seq_power_facet.cpp:513 | constrain(a.mk_ge(N, a.mk_int(1)));
    constraints_ok := constraints_ok && N >= 1;
// src: src/ast/seq/seq_power_facet.cpp:514 | ef.add_equation(ys, cat({one(px.m_e), one(y1)}), dep);
    constraints_ok := constraints_ok && Y == Power(X,M) + y1;
// src: src/ast/seq/seq_power_facet.cpp:515 | z = cat({one(y1), one(mk_pow(Y, a.mk_sub(N, a.mk_int(1))))});
    z := y1 + Power(Y,N-1);
// src: src/ast/seq/seq_power_facet.cpp:518 | case 2: {
  } else if b % 5 == 2 {
// src: src/ast/seq/seq_power_facet.cpp:520 | expr_ref w(m), i(m), j(m);
    var w: seq<int>;
// src: src/ast/seq/seq_power_facet.cpp:520 | expr_ref w(m), i(m), j(m);
    var i, j := iFresh, jFresh;
// src: src/ast/seq/seq_power_facet.cpp:521 | constrain(a.mk_ge(M, a.mk_int(1)));
    constraints_ok := constraints_ok && M >= 1;
// src: src/ast/seq/seq_power_facet.cpp:522 | if (gx || gy) {
    if gx || gy {
// src: src/ast/seq/seq_power_facet.cpp:523 | zstring root = primitive_root(gx ? sx : sy);
      var rt := PrimitiveRoot(if gx then sx else sy);
// src: src/ast/seq/seq_power_facet.cpp:524 | w = u.str.mk_string(root);
      w := rt;
// src: src/ast/seq/seq_power_facet.cpp:525 | if (gx)
      if gx {
// src: src/ast/seq/seq_power_facet.cpp:526 | i = a.mk_int(sx.length() / root.length());
        i := |sx| / |rt|;
// synth: specification, checked annotation, or structural delimiter
      }
// src: src/ast/seq/seq_power_facet.cpp:527 | if (gy)
      if gy {
// src: src/ast/seq/seq_power_facet.cpp:528 | j = a.mk_int(sy.length() / root.length());
        j := |sy| / |rt|;
// synth: specification, checked annotation, or structural delimiter
      }
// src: src/ast/seq/seq_power_facet.cpp:530 | else
    } else {
// src: src/ast/seq/seq_power_facet.cpp:531 | w = fresh_str("power-trichotomy-f2-w");
      w := wFresh;
// synth: specification, checked annotation, or structural delimiter
    }
// src: src/ast/seq/seq_power_facet.cpp:532 | if (!i) {
// src: src/ast/seq/seq_power_facet.cpp:533 | i = fresh_int("power-trichotomy-f2-i");
// src: src/ast/seq/seq_power_facet.cpp:534 | constrain(a.mk_ge(i, a.mk_int(1)));
// src: src/ast/seq/seq_power_facet.cpp:535 | ef.add_equation(xs, one(mk_pow(w, i)), dep);
    if !gx { i := iFresh; constraints_ok := constraints_ok && i >= 1 && X == Power(w,i); }
// src: src/ast/seq/seq_power_facet.cpp:537 | if (!j) {
// src: src/ast/seq/seq_power_facet.cpp:538 | j = fresh_int("power-trichotomy-f2-j");
// src: src/ast/seq/seq_power_facet.cpp:539 | constrain(a.mk_ge(j, a.mk_int(1)));
// src: src/ast/seq/seq_power_facet.cpp:540 | ef.add_equation(ys, one(mk_pow(w, j)), dep);
    if !gy { j := jFresh; constraints_ok := constraints_ok && j >= 1 && Y == Power(w,j); }
// src: src/ast/seq/seq_power_facet.cpp:542 | z = one(mk_pow(w, a.mk_sub(a.mk_mul(j, N), a.mk_mul(i, M))));
    z := Power(w,j*N-i*M);
// src: src/ast/seq/seq_power_facet.cpp:545 | case 3: {
  } else if b % 5 == 3 {
// src: src/ast/seq/seq_power_facet.cpp:547 | expr_ref_vector p1(m), p2(m);
    var p1, p2 := p1Fresh, p2Fresh;
// src: src/ast/seq/seq_power_facet.cpp:548 | constrain(a.mk_ge(M, a.mk_int(2)));
// src: src/ast/seq/seq_power_facet.cpp:549 | constrain(a.mk_ge(N, a.mk_int(2)));
    constraints_ok := constraints_ok && M >= 2 && N >= 2;
// src: src/ast/seq/seq_power_facet.cpp:550 | if (param > 0) {
    if param > 0 {
// src: src/ast/seq/seq_power_facet.cpp:552 | unsigned r = param, l1 = sx.length() % r;
      var l1 := |sx| % param;
// src: src/ast/seq/seq_power_facet.cpp:553 | p1 = word(sx.extract(sx.length() - l1, l1));
      p1 := sx[|sx|-l1..];
// src: src/ast/seq/seq_power_facet.cpp:554 | p2 = word(sx.extract(l1, r - l1));
      p2 := sx[l1..param];
// src: src/ast/seq/seq_power_facet.cpp:556 | else {
    } else {
// src: src/ast/seq/seq_power_facet.cpp:558 | p1 = one(v1);
// src: src/ast/seq/seq_power_facet.cpp:559 | p2 = one(v2);
// src: src/ast/seq/seq_power_facet.cpp:560 | ef.add_equation(xs, cat({one(mk_pow(u.str.mk_concat(v1, v2), k)), p1}), dep);
      constraints_ok := constraints_ok && X == Power(p1+p2,kFresh)+p1;
// synth: specification, checked annotation, or structural delimiter
    }
// src: src/ast/seq/seq_power_facet.cpp:562 | ef.add_equation(ys, cat({one(mk_pow(X, a.mk_sub(M, a.mk_int(1)))), p1, p2}), dep);
    constraints_ok := constraints_ok && Y == Power(X,M-1)+p1+p2;
// src: src/ast/seq/seq_power_facet.cpp:563 | z = cat({p2, p1, one(mk_pow(X, a.mk_sub(M, a.mk_int(2)))), p1, p2, one(mk_pow(Y, a.mk_sub(N, a.mk_int(2))))});
    z := p2+p1+Power(X,M-2)+p1+p2+Power(Y,N-2);
// src: src/ast/seq/seq_power_facet.cpp:566 | default: {
  } else {
// src: src/ast/seq/seq_power_facet.cpp:568 | expr_ref y1 = fresh_str("power-trichotomy-f4-y1"), y2 = fresh_str("power-trichotomy-f4-y2"), q = fresh_int("power-trichotomy-f4-q");
// src: src/ast/seq/seq_power_facet.cpp:569 | constrain(m.mk_eq(M, a.mk_int(1)));
// src: src/ast/seq/seq_power_facet.cpp:570 | constrain(a.mk_ge(q, a.mk_int(0)));
// src: src/ast/seq/seq_power_facet.cpp:571 | constrain(a.mk_le(a.mk_add(q, a.mk_int(1)), N));
    constraints_ok := constraints_ok && M == 1 && qFresh >= 0 && qFresh+1 <= N;
// src: src/ast/seq/seq_power_facet.cpp:572 | ef.add_equation(ys, cat({one(y1), one(y2)}), dep);
    constraints_ok := constraints_ok && Y == y1+y2;
// src: src/ast/seq/seq_power_facet.cpp:573 | ef.add_equation(xs, cat({one(mk_pow(Y, q)), one(y1)}), dep);
    constraints_ok := constraints_ok && X == Power(Y,qFresh)+y1;
// src: src/ast/seq/seq_power_facet.cpp:574 | z = cat({one(y2), one(mk_pow(Y, a.mk_sub(a.mk_sub(N, q), a.mk_int(1))))});
    z := y2+Power(Y,N-qFresh-1);
// synth: specification, checked annotation, or structural delimiter
  }
// src: src/ast/seq/seq_power_facet.cpp:578 | broadcast_subst(n, py.m_e, cat({one(px.m_e), z}), dep);
  fromWord := Power(Y,N);
// src: src/ast/seq/seq_power_facet.cpp:578 | broadcast_subst(n, py.m_e, cat({one(px.m_e), z}), dep);
  toWord := Power(X,M)+z;
// synth: specification, checked annotation, or structural delimiter
}

// Independent concrete proof harness, not a source-translated entry.
method ConcreteDomain0()
{
  var out0, out1, out2 := PowerRewriteEntry(0, 0, [97], [98], [0, 1], [0, 1], [true], [true], (-1), 1, [], [], [], 0, 0, [], [], 0, 0);
}

// Independent concrete proof harness, not a source-translated entry.
method ConcreteDomain1()
{
  var out0, out1, out2 := PowerRewriteEntry(1, 0, [97], [97, 98], [0, 1], [0, 1, 2], [true], [true, true], 1, 2, [98], [], [], 0, 0, [], [], 0, 0);
}

// Independent concrete proof harness, not a source-translated entry.
method ConcreteDomain2()
{
  var out0, out1, out2 := PowerRewriteEntry(2, 0, [], [], [0, 0], [0, 0], [false], [false], 2, (-1), [], [], [], 1, 1, [], [], 0, 0);
}

// Independent concrete proof harness, not a source-translated entry.
method ConcreteDomain3()
{
  var out0, out1, out2 := PowerRewriteEntry(2, 0, [97, 97], [97, 97, 97], [0, 1, 2], [0, 1, 2, 3], [true, true], [true, true, true], 1, 1, [], [], [], 0, 0, [], [], 0, 0);
}

// Independent concrete proof harness, not a source-translated entry.
method ConcreteDomain4()
{
  var out0, out1, out2 := PowerRewriteEntry(3, 0, [97], [97, 97, 98], [0, 1], [0, 3], [false], [false], 2, 2, [], [], [], 0, 0, [97], [98], (-1), 0);
}

// Independent concrete proof harness, not a source-translated entry.
method ConcreteDomain5()
{
  var out0, out1, out2 := PowerRewriteEntry(3, 2, [97, 98, 97, 98, 97], [97, 98, 97, 98, 97, 97, 98], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5, 6, 7], [true, true, true, true, true], [true, true, true, true, true, true, true], 2, 2, [], [], [], 0, 0, [], [], 0, 0);
}

// Independent concrete proof harness, not a source-translated entry.
method ConcreteDomain6()
{
  var out0, out1, out2 := PowerRewriteEntry(4, 0, [97, 98, 97], [97, 98], [0, 1, 2, 3], [0, 1, 2], [true, true, true], [true, true], 1, 2, [97], [98], [], 0, 0, [], [], 0, 1);
}

// Independent concrete proof harness, not a source-translated entry.
method ConcreteDomain7()
{
  var out0, out1, out2 := PowerRewriteEntry(6, 0, [97, 98], [97], [0, 1, 2], [0, 1], [true, true], [true], 2, 1, [98], [], [], 0, 0, [], [], 0, 0);
}
