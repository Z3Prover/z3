// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
function I(s: seq<int>, i: int): int
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
{ if 0 <= i < |s| then s[i] else 0 }
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
function B(s: seq<bool>, i: int): bool
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
{ 0 <= i < |s| && s[i] }
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
function R(s: seq<seq<int>>, i: int): seq<int>
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
{ if 0 <= i < |s| then s[i] else [] }
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
function Index(s: seq<int>, v: int, i: int): int
// synth: specification, checked annotation, or structural delimiter
  decreases |s|-i
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
{ if 0 <= i < |s| then (if s[i]==v then i else Index(s,v,i+1)) else -1 }
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
function Count(s: seq<int>, v: int): int
// synth: specification, checked annotation, or structural delimiter
  decreases |s|
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
{ if |s|==0 then 0 else (if s[0]==v then 1 else 0)+Count(s[1..],v) }
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
function Pick(s: seq<int>, ps: seq<int>): seq<int>
// synth: specification, checked annotation, or structural delimiter
  decreases |ps|
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
{ if |ps|==0 then [] else [I(s,ps[0])]+Pick(s,ps[1..]) }
// src: src/ast/seq_decl_plugin.cpp:1040 | void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
// src: src/ast/seq_decl_plugin.cpp:1041 | expr* e1, *e2;
// src: src/ast/seq_decl_plugin.cpp:1042 | while (is_concat(e, e1, e2)) {
// src: src/ast/seq_decl_plugin.cpp:1043 | get_concat_units(e1, es);
// src: src/ast/seq_decl_plugin.cpp:1044 | e = e2;
// src: src/ast/seq_decl_plugin.cpp:1045 | }
// src: src/ast/seq_decl_plugin.cpp:1046 | zstring s;
// src: src/ast/seq_decl_plugin.cpp:1047 | if (is_string(e, s)) {
// src: src/ast/seq_decl_plugin.cpp:1048 | unsigned sz = s.length();
// src: src/ast/seq_decl_plugin.cpp:1049 | for (unsigned j = 0; j < sz; ++j) {
// src: src/ast/seq_decl_plugin.cpp:1050 | es.push_back(mk_unit(mk_char(s, j)));
// src: src/ast/seq_decl_plugin.cpp:1051 | }
// src: src/ast/seq_decl_plugin.cpp:1052 | }
// src: src/ast/seq_decl_plugin.cpp:1053 | else if (!is_empty(e)) {
// src: src/ast/seq_decl_plugin.cpp:1054 | es.push_back(e);
// src: src/ast/seq_decl_plugin.cpp:1055 | }
function Rows(w: seq<int>, f: seq<int>): seq<seq<int>>
// synth: specification, checked annotation, or structural delimiter
  decreases |w|
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq_decl_plugin.cpp:1040 | void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
// src: src/ast/seq_decl_plugin.cpp:1041 | expr* e1, *e2;
// src: src/ast/seq_decl_plugin.cpp:1042 | while (is_concat(e, e1, e2)) {
// src: src/ast/seq_decl_plugin.cpp:1043 | get_concat_units(e1, es);
// src: src/ast/seq_decl_plugin.cpp:1044 | e = e2;
// src: src/ast/seq_decl_plugin.cpp:1045 | }
// src: src/ast/seq_decl_plugin.cpp:1046 | zstring s;
// src: src/ast/seq_decl_plugin.cpp:1047 | if (is_string(e, s)) {
// src: src/ast/seq_decl_plugin.cpp:1048 | unsigned sz = s.length();
// src: src/ast/seq_decl_plugin.cpp:1049 | for (unsigned j = 0; j < sz; ++j) {
// src: src/ast/seq_decl_plugin.cpp:1050 | es.push_back(mk_unit(mk_char(s, j)));
// src: src/ast/seq_decl_plugin.cpp:1051 | }
// src: src/ast/seq_decl_plugin.cpp:1052 | }
// src: src/ast/seq_decl_plugin.cpp:1053 | else if (!is_empty(e)) {
// src: src/ast/seq_decl_plugin.cpp:1054 | es.push_back(e);
// src: src/ast/seq_decl_plugin.cpp:1055 | }
  if |w|==0 then [] else
// src: src/ast/seq_decl_plugin.cpp:1040 | void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
// src: src/ast/seq_decl_plugin.cpp:1041 | expr* e1, *e2;
// src: src/ast/seq_decl_plugin.cpp:1042 | while (is_concat(e, e1, e2)) {
// src: src/ast/seq_decl_plugin.cpp:1043 | get_concat_units(e1, es);
// src: src/ast/seq_decl_plugin.cpp:1044 | e = e2;
// src: src/ast/seq_decl_plugin.cpp:1045 | }
// src: src/ast/seq_decl_plugin.cpp:1046 | zstring s;
// src: src/ast/seq_decl_plugin.cpp:1047 | if (is_string(e, s)) {
// src: src/ast/seq_decl_plugin.cpp:1048 | unsigned sz = s.length();
// src: src/ast/seq_decl_plugin.cpp:1049 | for (unsigned j = 0; j < sz; ++j) {
// src: src/ast/seq_decl_plugin.cpp:1050 | es.push_back(mk_unit(mk_char(s, j)));
// src: src/ast/seq_decl_plugin.cpp:1051 | }
// src: src/ast/seq_decl_plugin.cpp:1052 | }
// src: src/ast/seq_decl_plugin.cpp:1053 | else if (!is_empty(e)) {
// src: src/ast/seq_decl_plugin.cpp:1054 | es.push_back(e);
// src: src/ast/seq_decl_plugin.cpp:1055 | }
  var n := if 0 <= w[0] <= |f| then w[0] else 0;
// src: src/ast/seq_decl_plugin.cpp:1040 | void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
// src: src/ast/seq_decl_plugin.cpp:1041 | expr* e1, *e2;
// src: src/ast/seq_decl_plugin.cpp:1042 | while (is_concat(e, e1, e2)) {
// src: src/ast/seq_decl_plugin.cpp:1043 | get_concat_units(e1, es);
// src: src/ast/seq_decl_plugin.cpp:1044 | e = e2;
// src: src/ast/seq_decl_plugin.cpp:1045 | }
// src: src/ast/seq_decl_plugin.cpp:1046 | zstring s;
// src: src/ast/seq_decl_plugin.cpp:1047 | if (is_string(e, s)) {
// src: src/ast/seq_decl_plugin.cpp:1048 | unsigned sz = s.length();
// src: src/ast/seq_decl_plugin.cpp:1049 | for (unsigned j = 0; j < sz; ++j) {
// src: src/ast/seq_decl_plugin.cpp:1050 | es.push_back(mk_unit(mk_char(s, j)));
// src: src/ast/seq_decl_plugin.cpp:1051 | }
// src: src/ast/seq_decl_plugin.cpp:1052 | }
// src: src/ast/seq_decl_plugin.cpp:1053 | else if (!is_empty(e)) {
// src: src/ast/seq_decl_plugin.cpp:1054 | es.push_back(e);
// src: src/ast/seq_decl_plugin.cpp:1055 | }
  [f[..n]]+Rows(w[1..],f[n..])
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq_decl_plugin.cpp:1040 | void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
// src: src/ast/seq_decl_plugin.cpp:1041 | expr* e1, *e2;
// src: src/ast/seq_decl_plugin.cpp:1042 | while (is_concat(e, e1, e2)) {
// src: src/ast/seq_decl_plugin.cpp:1043 | get_concat_units(e1, es);
// src: src/ast/seq_decl_plugin.cpp:1044 | e = e2;
// src: src/ast/seq_decl_plugin.cpp:1045 | }
// src: src/ast/seq_decl_plugin.cpp:1046 | zstring s;
// src: src/ast/seq_decl_plugin.cpp:1047 | if (is_string(e, s)) {
// src: src/ast/seq_decl_plugin.cpp:1048 | unsigned sz = s.length();
// src: src/ast/seq_decl_plugin.cpp:1049 | for (unsigned j = 0; j < sz; ++j) {
// src: src/ast/seq_decl_plugin.cpp:1050 | es.push_back(mk_unit(mk_char(s, j)));
// src: src/ast/seq_decl_plugin.cpp:1051 | }
// src: src/ast/seq_decl_plugin.cpp:1052 | }
// src: src/ast/seq_decl_plugin.cpp:1053 | else if (!is_empty(e)) {
// src: src/ast/seq_decl_plugin.cpp:1054 | es.push_back(e);
// src: src/ast/seq_decl_plugin.cpp:1055 | }
function Widths(rows: seq<seq<int>>): seq<int>
// src: src/ast/seq_decl_plugin.cpp:1040 | void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
// src: src/ast/seq_decl_plugin.cpp:1041 | expr* e1, *e2;
// src: src/ast/seq_decl_plugin.cpp:1042 | while (is_concat(e, e1, e2)) {
// src: src/ast/seq_decl_plugin.cpp:1043 | get_concat_units(e1, es);
// src: src/ast/seq_decl_plugin.cpp:1044 | e = e2;
// src: src/ast/seq_decl_plugin.cpp:1045 | }
// src: src/ast/seq_decl_plugin.cpp:1046 | zstring s;
// src: src/ast/seq_decl_plugin.cpp:1047 | if (is_string(e, s)) {
// src: src/ast/seq_decl_plugin.cpp:1048 | unsigned sz = s.length();
// src: src/ast/seq_decl_plugin.cpp:1049 | for (unsigned j = 0; j < sz; ++j) {
// src: src/ast/seq_decl_plugin.cpp:1050 | es.push_back(mk_unit(mk_char(s, j)));
// src: src/ast/seq_decl_plugin.cpp:1051 | }
// src: src/ast/seq_decl_plugin.cpp:1052 | }
// src: src/ast/seq_decl_plugin.cpp:1053 | else if (!is_empty(e)) {
// src: src/ast/seq_decl_plugin.cpp:1054 | es.push_back(e);
// src: src/ast/seq_decl_plugin.cpp:1055 | }
{ seq(|rows|, i => |rows[i]|) }
// src: src/ast/seq_decl_plugin.cpp:1040 | void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
// src: src/ast/seq_decl_plugin.cpp:1041 | expr* e1, *e2;
// src: src/ast/seq_decl_plugin.cpp:1042 | while (is_concat(e, e1, e2)) {
// src: src/ast/seq_decl_plugin.cpp:1043 | get_concat_units(e1, es);
// src: src/ast/seq_decl_plugin.cpp:1044 | e = e2;
// src: src/ast/seq_decl_plugin.cpp:1045 | }
// src: src/ast/seq_decl_plugin.cpp:1046 | zstring s;
// src: src/ast/seq_decl_plugin.cpp:1047 | if (is_string(e, s)) {
// src: src/ast/seq_decl_plugin.cpp:1048 | unsigned sz = s.length();
// src: src/ast/seq_decl_plugin.cpp:1049 | for (unsigned j = 0; j < sz; ++j) {
// src: src/ast/seq_decl_plugin.cpp:1050 | es.push_back(mk_unit(mk_char(s, j)));
// src: src/ast/seq_decl_plugin.cpp:1051 | }
// src: src/ast/seq_decl_plugin.cpp:1052 | }
// src: src/ast/seq_decl_plugin.cpp:1053 | else if (!is_empty(e)) {
// src: src/ast/seq_decl_plugin.cpp:1054 | es.push_back(e);
// src: src/ast/seq_decl_plugin.cpp:1055 | }
function Flat(rows: seq<seq<int>>): seq<int>
// synth: specification, checked annotation, or structural delimiter
  decreases |rows|
// src: src/ast/seq_decl_plugin.cpp:1040 | void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
// src: src/ast/seq_decl_plugin.cpp:1041 | expr* e1, *e2;
// src: src/ast/seq_decl_plugin.cpp:1042 | while (is_concat(e, e1, e2)) {
// src: src/ast/seq_decl_plugin.cpp:1043 | get_concat_units(e1, es);
// src: src/ast/seq_decl_plugin.cpp:1044 | e = e2;
// src: src/ast/seq_decl_plugin.cpp:1045 | }
// src: src/ast/seq_decl_plugin.cpp:1046 | zstring s;
// src: src/ast/seq_decl_plugin.cpp:1047 | if (is_string(e, s)) {
// src: src/ast/seq_decl_plugin.cpp:1048 | unsigned sz = s.length();
// src: src/ast/seq_decl_plugin.cpp:1049 | for (unsigned j = 0; j < sz; ++j) {
// src: src/ast/seq_decl_plugin.cpp:1050 | es.push_back(mk_unit(mk_char(s, j)));
// src: src/ast/seq_decl_plugin.cpp:1051 | }
// src: src/ast/seq_decl_plugin.cpp:1052 | }
// src: src/ast/seq_decl_plugin.cpp:1053 | else if (!is_empty(e)) {
// src: src/ast/seq_decl_plugin.cpp:1054 | es.push_back(e);
// src: src/ast/seq_decl_plugin.cpp:1055 | }
{ if |rows|==0 then [] else rows[0]+Flat(rows[1..]) }
// src: src/ast/seq_decl_plugin.cpp:1040 | void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
// src: src/ast/seq_decl_plugin.cpp:1041 | expr* e1, *e2;
// src: src/ast/seq_decl_plugin.cpp:1042 | while (is_concat(e, e1, e2)) {
// src: src/ast/seq_decl_plugin.cpp:1043 | get_concat_units(e1, es);
// src: src/ast/seq_decl_plugin.cpp:1044 | e = e2;
// src: src/ast/seq_decl_plugin.cpp:1045 | }
// src: src/ast/seq_decl_plugin.cpp:1046 | zstring s;
// src: src/ast/seq_decl_plugin.cpp:1047 | if (is_string(e, s)) {
// src: src/ast/seq_decl_plugin.cpp:1048 | unsigned sz = s.length();
// src: src/ast/seq_decl_plugin.cpp:1049 | for (unsigned j = 0; j < sz; ++j) {
// src: src/ast/seq_decl_plugin.cpp:1050 | es.push_back(mk_unit(mk_char(s, j)));
// src: src/ast/seq_decl_plugin.cpp:1051 | }
// src: src/ast/seq_decl_plugin.cpp:1052 | }
// src: src/ast/seq_decl_plugin.cpp:1053 | else if (!is_empty(e)) {
// src: src/ast/seq_decl_plugin.cpp:1054 | es.push_back(e);
// src: src/ast/seq_decl_plugin.cpp:1055 | }
ghost predicate Partition(w: seq<int>, f: seq<int>)
// src: src/ast/seq_decl_plugin.cpp:1040 | void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
// src: src/ast/seq_decl_plugin.cpp:1041 | expr* e1, *e2;
// src: src/ast/seq_decl_plugin.cpp:1042 | while (is_concat(e, e1, e2)) {
// src: src/ast/seq_decl_plugin.cpp:1043 | get_concat_units(e1, es);
// src: src/ast/seq_decl_plugin.cpp:1044 | e = e2;
// src: src/ast/seq_decl_plugin.cpp:1045 | }
// src: src/ast/seq_decl_plugin.cpp:1046 | zstring s;
// src: src/ast/seq_decl_plugin.cpp:1047 | if (is_string(e, s)) {
// src: src/ast/seq_decl_plugin.cpp:1048 | unsigned sz = s.length();
// src: src/ast/seq_decl_plugin.cpp:1049 | for (unsigned j = 0; j < sz; ++j) {
// src: src/ast/seq_decl_plugin.cpp:1050 | es.push_back(mk_unit(mk_char(s, j)));
// src: src/ast/seq_decl_plugin.cpp:1051 | }
// src: src/ast/seq_decl_plugin.cpp:1052 | }
// src: src/ast/seq_decl_plugin.cpp:1053 | else if (!is_empty(e)) {
// src: src/ast/seq_decl_plugin.cpp:1054 | es.push_back(e);
// src: src/ast/seq_decl_plugin.cpp:1055 | }
{ Widths(Rows(w,f))==w && Flat(Rows(w,f))==f }
// src: src/util/stx_search_tree.h:600 | }
// src: src/util/stx_search_tree.h:601 | unsigned intern(constraint_i const& c) {
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
// src: src/util/stx_search_tree.h:610 | return id;
// src: src/util/stx_search_tree.h:611 | }
ghost predicate Unique(s: seq<int>)
// src: src/util/stx_search_tree.h:600 | }
// src: src/util/stx_search_tree.h:601 | unsigned intern(constraint_i const& c) {
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
// src: src/util/stx_search_tree.h:610 | return id;
// src: src/util/stx_search_tree.h:611 | }
{ forall i,j :: 0 <= i < j < |s| ==> s[i]!=s[j] }

// src: src/util/stx_search_tree.h:637 | bool cache_eligible(node const& n) const {
// src: src/util/stx_search_tree.h:638 | for (facet_id id = 0; id < n.num_facets(); ++id) {
// src: src/util/stx_search_tree.h:639 | if (!n.has_facet(id))
// src: src/util/stx_search_tree.h:640 | continue;
// src: src/util/stx_search_tree.h:641 | facet_i const& f = n.facet(id);
// src: src/util/stx_search_tree.h:642 | if (!f.contributes_to_signature() && !f.is_satisfied())
// src: src/util/stx_search_tree.h:643 | return false;
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
// src: src/util/stx_search_tree.h:658 | }
function Eligible(c: seq<bool>, sat: seq<bool>, i: int): bool
// synth: specification, checked annotation, or structural delimiter
  decreases |c|-i
// src: src/util/stx_search_tree.h:637 | bool cache_eligible(node const& n) const {
// src: src/util/stx_search_tree.h:638 | for (facet_id id = 0; id < n.num_facets(); ++id) {
// src: src/util/stx_search_tree.h:639 | if (!n.has_facet(id))
// src: src/util/stx_search_tree.h:640 | continue;
// src: src/util/stx_search_tree.h:641 | facet_i const& f = n.facet(id);
// src: src/util/stx_search_tree.h:642 | if (!f.contributes_to_signature() && !f.is_satisfied())
// src: src/util/stx_search_tree.h:643 | return false;
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
// src: src/util/stx_search_tree.h:658 | }
{ if 0<=i<|c| then (c[i] || B(sat,i)) && Eligible(c,sat,i+1) else true }
// src: src/util/stx_search_tree.h:637 | bool cache_eligible(node const& n) const {
// src: src/util/stx_search_tree.h:638 | for (facet_id id = 0; id < n.num_facets(); ++id) {
// src: src/util/stx_search_tree.h:639 | if (!n.has_facet(id))
// src: src/util/stx_search_tree.h:640 | continue;
// src: src/util/stx_search_tree.h:641 | facet_i const& f = n.facet(id);
// src: src/util/stx_search_tree.h:642 | if (!f.contributes_to_signature() && !f.is_satisfied())
// src: src/util/stx_search_tree.h:643 | return false;
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
// src: src/util/stx_search_tree.h:658 | }
function Collect(c: seq<bool>, w: seq<int>, i: int, offset: int): seq<int>
// synth: specification, checked annotation, or structural delimiter
  decreases |w|-i
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:637 | bool cache_eligible(node const& n) const {
// src: src/util/stx_search_tree.h:638 | for (facet_id id = 0; id < n.num_facets(); ++id) {
// src: src/util/stx_search_tree.h:639 | if (!n.has_facet(id))
// src: src/util/stx_search_tree.h:640 | continue;
// src: src/util/stx_search_tree.h:641 | facet_i const& f = n.facet(id);
// src: src/util/stx_search_tree.h:642 | if (!f.contributes_to_signature() && !f.is_satisfied())
// src: src/util/stx_search_tree.h:643 | return false;
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
// src: src/util/stx_search_tree.h:658 | }
  if 0<=i<|w| then
// src: src/util/stx_search_tree.h:637 | bool cache_eligible(node const& n) const {
// src: src/util/stx_search_tree.h:638 | for (facet_id id = 0; id < n.num_facets(); ++id) {
// src: src/util/stx_search_tree.h:639 | if (!n.has_facet(id))
// src: src/util/stx_search_tree.h:640 | continue;
// src: src/util/stx_search_tree.h:641 | facet_i const& f = n.facet(id);
// src: src/util/stx_search_tree.h:642 | if (!f.contributes_to_signature() && !f.is_satisfied())
// src: src/util/stx_search_tree.h:643 | return false;
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
// src: src/util/stx_search_tree.h:658 | }
  var n := if w[i]>=0 then w[i] else 0;
// src: src/util/stx_search_tree.h:637 | bool cache_eligible(node const& n) const {
// src: src/util/stx_search_tree.h:638 | for (facet_id id = 0; id < n.num_facets(); ++id) {
// src: src/util/stx_search_tree.h:639 | if (!n.has_facet(id))
// src: src/util/stx_search_tree.h:640 | continue;
// src: src/util/stx_search_tree.h:641 | facet_i const& f = n.facet(id);
// src: src/util/stx_search_tree.h:642 | if (!f.contributes_to_signature() && !f.is_satisfied())
// src: src/util/stx_search_tree.h:643 | return false;
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
// src: src/util/stx_search_tree.h:658 | }
  (if B(c,i) then seq(n,j=>offset+j) else [])+Collect(c,w,i+1,offset+n)
// src: src/util/stx_search_tree.h:637 | bool cache_eligible(node const& n) const {
// src: src/util/stx_search_tree.h:638 | for (facet_id id = 0; id < n.num_facets(); ++id) {
// src: src/util/stx_search_tree.h:639 | if (!n.has_facet(id))
// src: src/util/stx_search_tree.h:640 | continue;
// src: src/util/stx_search_tree.h:641 | facet_i const& f = n.facet(id);
// src: src/util/stx_search_tree.h:642 | if (!f.contributes_to_signature() && !f.is_satisfied())
// src: src/util/stx_search_tree.h:643 | return false;
// src: src/util/stx_search_tree.h:644 | }
// src: src/util/stx_search_tree.h:645 | return true;
// src: src/util/stx_search_tree.h:646 | }
// src: src/util/stx_search_tree.h:647 | 
// src: src/util/stx_search_tree.h:648 | // Canonical constraint list: concatenate every contributing
// src: src/util/stx_search_tree.h:649 | // facet's own append_constraints() output (borrowed pointers into
// src: src/util/stx_search_tree.h:650 | // the facet's own live, active elements), in ascending facet_id
// src: src/util/stx_search_tree.h:651 | // order.
// src: src/util/stx_search_tree.h:652 | static vector<constraint_i const*> compute_constraints(node const& n) {
// src: src/util/stx_search_tree.h:653 | vector<constraint_i const*> cs;
// src: src/util/stx_search_tree.h:654 | for (facet_id id = 0; id < n.num_facets(); ++id)
// src: src/util/stx_search_tree.h:655 | if (n.has_facet(id) && n.facet(id).contributes_to_signature())
// src: src/util/stx_search_tree.h:656 | n.facet(id).append_constraints(cs);
// src: src/util/stx_search_tree.h:657 | return cs;
// src: src/util/stx_search_tree.h:658 | }
  else []
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/dependency.h:235 | bool contains(dependency * d, value const & v) {
// src: src/util/dependency.h:236 | if (d) {
// src: src/util/dependency.h:237 | m_todo.reset();
// src: src/util/dependency.h:238 | d->mark();
// src: src/util/dependency.h:239 | m_todo.push_back(d);
// src: src/util/dependency.h:240 | unsigned qhead = 0;
// src: src/util/dependency.h:241 | while (qhead < m_todo.size()) {
// src: src/util/dependency.h:242 | d = m_todo[qhead];
// src: src/util/dependency.h:243 | qhead++;
// src: src/util/dependency.h:244 | if (d->is_leaf()) {
// src: src/util/dependency.h:245 | if (to_leaf(d)->m_value == v) {
// src: src/util/dependency.h:246 | unmark_todo();
// src: src/util/dependency.h:247 | return true;
// src: src/util/dependency.h:248 | }
// src: src/util/dependency.h:249 | }
// src: src/util/dependency.h:250 | else {
// src: src/util/dependency.h:251 | for (unsigned i = 0; i < 2; ++i) {
// src: src/util/dependency.h:252 | dependency * child = to_join(d)->m_children[i];
// src: src/util/dependency.h:253 | if (child && !child->is_marked()) {
// src: src/util/dependency.h:254 | m_todo.push_back(child);
// src: src/util/dependency.h:255 | child->mark();
// src: src/util/dependency.h:256 | }
// src: src/util/dependency.h:257 | }
// src: src/util/dependency.h:258 | }
// src: src/util/dependency.h:259 | }
// src: src/util/dependency.h:260 | unmark_todo();
// src: src/util/dependency.h:261 | }
// src: src/util/dependency.h:262 | return false;
// src: src/util/dependency.h:263 | }
// src: src/util/dependency.h:264 | 
// src: src/util/dependency.h:265 | 
// src: src/util/dependency.h:266 | 
// src: src/util/dependency.h:267 | void linearize(dependency * d, vector<value, false> & vs) const {
// src: src/util/dependency.h:268 | if (!d)
// src: src/util/dependency.h:269 | return;
// src: src/util/dependency.h:270 | SASSERT(m_todo.empty());
// src: src/util/dependency.h:271 | d->mark();
// src: src/util/dependency.h:272 | m_todo.push_back(d);
// src: src/util/dependency.h:273 | linearize_todo(m_todo, vs);
// src: src/util/dependency.h:274 | m_todo.reset();
// src: src/util/dependency.h:275 | }
function Subset(a: seq<int>, b: seq<int>): bool
// synth: specification, checked annotation, or structural delimiter
  decreases |a|
// src: src/util/dependency.h:235 | bool contains(dependency * d, value const & v) {
// src: src/util/dependency.h:236 | if (d) {
// src: src/util/dependency.h:237 | m_todo.reset();
// src: src/util/dependency.h:238 | d->mark();
// src: src/util/dependency.h:239 | m_todo.push_back(d);
// src: src/util/dependency.h:240 | unsigned qhead = 0;
// src: src/util/dependency.h:241 | while (qhead < m_todo.size()) {
// src: src/util/dependency.h:242 | d = m_todo[qhead];
// src: src/util/dependency.h:243 | qhead++;
// src: src/util/dependency.h:244 | if (d->is_leaf()) {
// src: src/util/dependency.h:245 | if (to_leaf(d)->m_value == v) {
// src: src/util/dependency.h:246 | unmark_todo();
// src: src/util/dependency.h:247 | return true;
// src: src/util/dependency.h:248 | }
// src: src/util/dependency.h:249 | }
// src: src/util/dependency.h:250 | else {
// src: src/util/dependency.h:251 | for (unsigned i = 0; i < 2; ++i) {
// src: src/util/dependency.h:252 | dependency * child = to_join(d)->m_children[i];
// src: src/util/dependency.h:253 | if (child && !child->is_marked()) {
// src: src/util/dependency.h:254 | m_todo.push_back(child);
// src: src/util/dependency.h:255 | child->mark();
// src: src/util/dependency.h:256 | }
// src: src/util/dependency.h:257 | }
// src: src/util/dependency.h:258 | }
// src: src/util/dependency.h:259 | }
// src: src/util/dependency.h:260 | unmark_todo();
// src: src/util/dependency.h:261 | }
// src: src/util/dependency.h:262 | return false;
// src: src/util/dependency.h:263 | }
// src: src/util/dependency.h:264 | 
// src: src/util/dependency.h:265 | 
// src: src/util/dependency.h:266 | 
// src: src/util/dependency.h:267 | void linearize(dependency * d, vector<value, false> & vs) const {
// src: src/util/dependency.h:268 | if (!d)
// src: src/util/dependency.h:269 | return;
// src: src/util/dependency.h:270 | SASSERT(m_todo.empty());
// src: src/util/dependency.h:271 | d->mark();
// src: src/util/dependency.h:272 | m_todo.push_back(d);
// src: src/util/dependency.h:273 | linearize_todo(m_todo, vs);
// src: src/util/dependency.h:274 | m_todo.reset();
// src: src/util/dependency.h:275 | }
{ if |a|==0 then true else a[0] in b && Subset(a[1..],b) }
// src: src/util/stx_search_tree.h:782 | void filter_by_conflict_dep(vector<constraint_i const*>& cs, dep_tracker conflict_dep) {
// src: src/util/stx_search_tree.h:783 | if (!conflict_dep)
// src: src/util/stx_search_tree.h:784 | return;
// src: src/util/stx_search_tree.h:785 | vector<constraint_i const*> kept;
// src: src/util/stx_search_tree.h:786 | vector<dep_source_t, false> fact_leaves;
// src: src/util/stx_search_tree.h:787 | for (constraint_i const* c : cs) {
// src: src/util/stx_search_tree.h:788 | dep_tracker fd = static_cast<dep_tracker>(c->dep_handle());
// src: src/util/stx_search_tree.h:789 | if (!fd) {
// src: src/util/stx_search_tree.h:790 | kept.push_back(c);
// src: src/util/stx_search_tree.h:791 | continue;
// src: src/util/stx_search_tree.h:792 | }
// src: src/util/stx_search_tree.h:793 | fact_leaves.reset();
// src: src/util/stx_search_tree.h:794 | m_dep_mgr.linearize(fd, fact_leaves);
// src: src/util/stx_search_tree.h:795 | bool all_contained = true;
// src: src/util/stx_search_tree.h:796 | for (auto const& v : fact_leaves) {
// src: src/util/stx_search_tree.h:797 | if (!m_dep_mgr.contains(conflict_dep, v)) {
// src: src/util/stx_search_tree.h:798 | all_contained = false;
// src: src/util/stx_search_tree.h:799 | break;
// src: src/util/stx_search_tree.h:800 | }
// src: src/util/stx_search_tree.h:801 | }
// src: src/util/stx_search_tree.h:802 | if (all_contained)
// src: src/util/stx_search_tree.h:803 | kept.push_back(c);
// src: src/util/stx_search_tree.h:804 | }
// src: src/util/stx_search_tree.h:805 | cs = std::move(kept);
function Filter(ps: seq<int>, has: seq<bool>, dw: seq<int>, di: seq<int>, ch: bool, cl: seq<int>): seq<int>
// synth: specification, checked annotation, or structural delimiter
  decreases |ps|
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:782 | void filter_by_conflict_dep(vector<constraint_i const*>& cs, dep_tracker conflict_dep) {
// src: src/util/stx_search_tree.h:783 | if (!conflict_dep)
// src: src/util/stx_search_tree.h:784 | return;
// src: src/util/stx_search_tree.h:785 | vector<constraint_i const*> kept;
// src: src/util/stx_search_tree.h:786 | vector<dep_source_t, false> fact_leaves;
// src: src/util/stx_search_tree.h:787 | for (constraint_i const* c : cs) {
// src: src/util/stx_search_tree.h:788 | dep_tracker fd = static_cast<dep_tracker>(c->dep_handle());
// src: src/util/stx_search_tree.h:789 | if (!fd) {
// src: src/util/stx_search_tree.h:790 | kept.push_back(c);
// src: src/util/stx_search_tree.h:791 | continue;
// src: src/util/stx_search_tree.h:792 | }
// src: src/util/stx_search_tree.h:793 | fact_leaves.reset();
// src: src/util/stx_search_tree.h:794 | m_dep_mgr.linearize(fd, fact_leaves);
// src: src/util/stx_search_tree.h:795 | bool all_contained = true;
// src: src/util/stx_search_tree.h:796 | for (auto const& v : fact_leaves) {
// src: src/util/stx_search_tree.h:797 | if (!m_dep_mgr.contains(conflict_dep, v)) {
// src: src/util/stx_search_tree.h:798 | all_contained = false;
// src: src/util/stx_search_tree.h:799 | break;
// src: src/util/stx_search_tree.h:800 | }
// src: src/util/stx_search_tree.h:801 | }
// src: src/util/stx_search_tree.h:802 | if (all_contained)
// src: src/util/stx_search_tree.h:803 | kept.push_back(c);
// src: src/util/stx_search_tree.h:804 | }
// src: src/util/stx_search_tree.h:805 | cs = std::move(kept);
  if |ps|==0 then [] else
// src: src/util/stx_search_tree.h:782 | void filter_by_conflict_dep(vector<constraint_i const*>& cs, dep_tracker conflict_dep) {
// src: src/util/stx_search_tree.h:783 | if (!conflict_dep)
// src: src/util/stx_search_tree.h:784 | return;
// src: src/util/stx_search_tree.h:785 | vector<constraint_i const*> kept;
// src: src/util/stx_search_tree.h:786 | vector<dep_source_t, false> fact_leaves;
// src: src/util/stx_search_tree.h:787 | for (constraint_i const* c : cs) {
// src: src/util/stx_search_tree.h:788 | dep_tracker fd = static_cast<dep_tracker>(c->dep_handle());
// src: src/util/stx_search_tree.h:789 | if (!fd) {
// src: src/util/stx_search_tree.h:790 | kept.push_back(c);
// src: src/util/stx_search_tree.h:791 | continue;
// src: src/util/stx_search_tree.h:792 | }
// src: src/util/stx_search_tree.h:793 | fact_leaves.reset();
// src: src/util/stx_search_tree.h:794 | m_dep_mgr.linearize(fd, fact_leaves);
// src: src/util/stx_search_tree.h:795 | bool all_contained = true;
// src: src/util/stx_search_tree.h:796 | for (auto const& v : fact_leaves) {
// src: src/util/stx_search_tree.h:797 | if (!m_dep_mgr.contains(conflict_dep, v)) {
// src: src/util/stx_search_tree.h:798 | all_contained = false;
// src: src/util/stx_search_tree.h:799 | break;
// src: src/util/stx_search_tree.h:800 | }
// src: src/util/stx_search_tree.h:801 | }
// src: src/util/stx_search_tree.h:802 | if (all_contained)
// src: src/util/stx_search_tree.h:803 | kept.push_back(c);
// src: src/util/stx_search_tree.h:804 | }
// src: src/util/stx_search_tree.h:805 | cs = std::move(kept);
  (if !ch || !B(has,ps[0]) || Subset(R(Rows(dw,di),ps[0]),cl) then [ps[0]] else [])+Filter(ps[1..],has,dw,di,ch,cl)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:601 | unsigned intern(constraint_i const& c) {
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
// src: src/util/stx_search_tree.h:610 | return id;
// src: src/util/stx_search_tree.h:611 | }
function InternList(values: seq<int>, store: seq<int>): (seq<int>,seq<int>)
// synth: specification, checked annotation, or structural delimiter
  decreases |values|
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:601 | unsigned intern(constraint_i const& c) {
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
// src: src/util/stx_search_tree.h:610 | return id;
// src: src/util/stx_search_tree.h:611 | }
  if |values|==0 then (store,[]) else
// src: src/util/stx_search_tree.h:601 | unsigned intern(constraint_i const& c) {
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
// src: src/util/stx_search_tree.h:610 | return id;
// src: src/util/stx_search_tree.h:611 | }
  var found := Index(store,values[0],0);
// src: src/util/stx_search_tree.h:601 | unsigned intern(constraint_i const& c) {
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
// src: src/util/stx_search_tree.h:610 | return id;
// src: src/util/stx_search_tree.h:611 | }
  var id := if found<0 then |store| else found;
// src: src/util/stx_search_tree.h:601 | unsigned intern(constraint_i const& c) {
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
// src: src/util/stx_search_tree.h:610 | return id;
// src: src/util/stx_search_tree.h:611 | }
  var ns := if found<0 then store+[values[0]] else store;
// src: src/util/stx_search_tree.h:601 | unsigned intern(constraint_i const& c) {
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
// src: src/util/stx_search_tree.h:610 | return id;
// src: src/util/stx_search_tree.h:611 | }
  var rest := InternList(values[1..],ns);
// src: src/util/stx_search_tree.h:601 | unsigned intern(constraint_i const& c) {
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
// src: src/util/stx_search_tree.h:610 | return id;
// src: src/util/stx_search_tree.h:611 | }
  (rest.0,[id]+rest.1)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:664 | void watch(unsigned id, unsigned core_idx) {
// src: src/util/stx_search_tree.h:665 | if (id >= m_watch_list.size())
// src: src/util/stx_search_tree.h:666 | m_watch_list.resize(id + 1);
// src: src/util/stx_search_tree.h:667 | m_watch_list[id].push_back(core_idx);
// src: src/util/stx_search_tree.h:668 | }
function WatchAdd(buckets: seq<seq<int>>, id: int, core: int): seq<seq<int>>
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:664 | void watch(unsigned id, unsigned core_idx) {
// src: src/util/stx_search_tree.h:665 | if (id >= m_watch_list.size())
// src: src/util/stx_search_tree.h:666 | m_watch_list.resize(id + 1);
// src: src/util/stx_search_tree.h:667 | m_watch_list[id].push_back(core_idx);
// src: src/util/stx_search_tree.h:668 | }
  if id<0 then buckets else if id<|buckets| then buckets[id:=buckets[id]+[core]] else buckets+seq(id-|buckets|,i=>[])+[[core]]
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:824 | void cache_insert(node const& n) {
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
// src: src/util/stx_search_tree.h:830 | // Narrow the over-approximate active set down to just the
// src: src/util/stx_search_tree.h:831 | // facts that could have contributed to THIS conflict (see
// src: src/util/stx_search_tree.h:832 | // filter_by_conflict_dep()'s comment) before interning
// src: src/util/stx_search_tree.h:833 | // anything: a smaller recorded core matches (as a subset)
// src: src/util/stx_search_tree.h:834 | // more future nodes, so this only ever helps the cache's hit
// src: src/util/stx_search_tree.h:835 | // rate, never hurts its soundness.
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
// src: src/util/stx_search_tree.h:846 | }
function CacheExpected(enabled: bool, fc: seq<bool>, fs: seq<bool>, fw: seq<int>, fv: seq<int>, dh: seq<bool>, dw: seq<int>, di: seq<int>, ch: bool, cl: seq<int>, store: seq<int>, cores: seq<seq<int>>, watches: seq<int>, buckets: seq<seq<int>>): (seq<int>,seq<seq<int>>,seq<int>,seq<seq<int>>,bool)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:824 | void cache_insert(node const& n) {
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
// src: src/util/stx_search_tree.h:830 | // Narrow the over-approximate active set down to just the
// src: src/util/stx_search_tree.h:831 | // facts that could have contributed to THIS conflict (see
// src: src/util/stx_search_tree.h:832 | // filter_by_conflict_dep()'s comment) before interning
// src: src/util/stx_search_tree.h:833 | // anything: a smaller recorded core matches (as a subset)
// src: src/util/stx_search_tree.h:834 | // more future nodes, so this only ever helps the cache's hit
// src: src/util/stx_search_tree.h:835 | // rate, never hurts its soundness.
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
// src: src/util/stx_search_tree.h:846 | }
  var ps := if enabled && Eligible(fc,fs,0) then Filter(Collect(fc,fw,0,0),dh,dw,di,ch,cl) else [];
// src: src/util/stx_search_tree.h:824 | void cache_insert(node const& n) {
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
// src: src/util/stx_search_tree.h:830 | // Narrow the over-approximate active set down to just the
// src: src/util/stx_search_tree.h:831 | // facts that could have contributed to THIS conflict (see
// src: src/util/stx_search_tree.h:832 | // filter_by_conflict_dep()'s comment) before interning
// src: src/util/stx_search_tree.h:833 | // anything: a smaller recorded core matches (as a subset)
// src: src/util/stx_search_tree.h:834 | // more future nodes, so this only ever helps the cache's hit
// src: src/util/stx_search_tree.h:835 | // rate, never hurts its soundness.
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
// src: src/util/stx_search_tree.h:846 | }
  if |ps|==0 then (store,cores,watches,buckets,false) else
// src: src/util/stx_search_tree.h:824 | void cache_insert(node const& n) {
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
// src: src/util/stx_search_tree.h:830 | // Narrow the over-approximate active set down to just the
// src: src/util/stx_search_tree.h:831 | // facts that could have contributed to THIS conflict (see
// src: src/util/stx_search_tree.h:832 | // filter_by_conflict_dep()'s comment) before interning
// src: src/util/stx_search_tree.h:833 | // anything: a smaller recorded core matches (as a subset)
// src: src/util/stx_search_tree.h:834 | // more future nodes, so this only ever helps the cache's hit
// src: src/util/stx_search_tree.h:835 | // rate, never hurts its soundness.
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
// src: src/util/stx_search_tree.h:846 | }
  var interned := InternList(Pick(fv,ps),store);
// src: src/util/stx_search_tree.h:824 | void cache_insert(node const& n) {
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
// src: src/util/stx_search_tree.h:830 | // Narrow the over-approximate active set down to just the
// src: src/util/stx_search_tree.h:831 | // facts that could have contributed to THIS conflict (see
// src: src/util/stx_search_tree.h:832 | // filter_by_conflict_dep()'s comment) before interning
// src: src/util/stx_search_tree.h:833 | // anything: a smaller recorded core matches (as a subset)
// src: src/util/stx_search_tree.h:834 | // more future nodes, so this only ever helps the cache's hit
// src: src/util/stx_search_tree.h:835 | // rate, never hurts its soundness.
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
// src: src/util/stx_search_tree.h:846 | }
  (interned.0,cores+[interned.1],watches+[0],WatchAdd(buckets,I(interned.1,0),|cores|),true)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_mem_facet.h:65 | struct str_mem : public stx::constraint_i {
// src: src/ast/seq/seq_mem_facet.h:66 | expr_ref_vector      m_str;
// src: src/ast/seq/seq_mem_facet.h:67 | view                 m_view;
// src: src/ast/seq/seq_mem_facet.h:68 | eq_tree::dep_tracker m_dep = nullptr;
// src: src/ast/seq/seq_mem_facet.h:69 | bool                 m_active = true;
// src: src/ast/seq/seq_mem_facet.h:70 | 
// src: src/ast/seq/seq_mem_facet.h:71 | str_mem(ast_manager& m, expr* s, view const& v, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_mem_facet.h:72 | m_str(m), m_view(v), m_dep(dep) {
// src: src/ast/seq/seq_mem_facet.h:73 | seq_util(m).str.get_concat_units(s, m_str);
// src: src/ast/seq/seq_mem_facet.h:74 | }
// src: src/ast/seq/seq_mem_facet.h:75 | str_mem(ast_manager& m, expr_ref_vector const& ts, view const& v, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_mem_facet.h:76 | m_str(ts), m_view(v), m_dep(dep) {}
// src: src/ast/seq/seq_mem_facet.h:77 | 
// src: src/ast/seq/seq_mem_facet.h:78 | bool is_plain() const { return m_view.is_membership(); }
// src: src/ast/seq/seq_mem_facet.h:79 | bool is_view() const { return m_view.is_reach(); }
// src: src/ast/seq/seq_mem_facet.h:80 | bool active() const { return m_active; }
// src: src/ast/seq/seq_mem_facet.h:81 | 
// src: src/ast/seq/seq_mem_facet.h:82 | // -- stx::constraint_i (unsat-cache identity) --
// src: src/ast/seq/seq_mem_facet.h:83 | // Identity is (token list, view): the same string term driving
// src: src/ast/seq/seq_mem_facet.h:84 | // the same (state,target) automaton view. `clone()` intentionally
// src: src/ast/seq/seq_mem_facet.h:85 | // drops `m_dep`/`m_active` - see stx::constraint_i's class
// src: src/ast/seq/seq_mem_facet.h:86 | // comment - and recovers the ast_manager it needs from
// src: src/ast/seq/seq_mem_facet.h:87 | // `m_str`'s own ref-vector (str_mem itself holds no separate
// src: src/ast/seq/seq_mem_facet.h:88 | // `ast_manager&` member).
// src: src/ast/seq/seq_mem_facet.h:89 | uint64_t hash() const override;
// src: src/ast/seq/seq_mem_facet.h:90 | bool equals(stx::constraint_i const& other) const override;
// src: src/ast/seq/seq_mem_facet.h:91 | stx::constraint_i* clone() const override { return alloc(str_mem, m_str.get_manager(), m_str, m_view); }
// src: src/ast/seq/seq_mem_facet.h:92 | void* dep_handle() const override { return m_dep; }
// src: src/ast/seq/seq_mem_facet.h:93 | };
// src: src/ast/seq/seq_mem_facet.h:94 | 
function AcceptWord(ids: seq<int>, words: seq<seq<int>>, word: seq<int>): bool
// synth: specification, checked annotation, or structural delimiter
  decreases |ids|
// src: src/ast/seq/seq_mem_facet.h:65 | struct str_mem : public stx::constraint_i {
// src: src/ast/seq/seq_mem_facet.h:66 | expr_ref_vector      m_str;
// src: src/ast/seq/seq_mem_facet.h:67 | view                 m_view;
// src: src/ast/seq/seq_mem_facet.h:68 | eq_tree::dep_tracker m_dep = nullptr;
// src: src/ast/seq/seq_mem_facet.h:69 | bool                 m_active = true;
// src: src/ast/seq/seq_mem_facet.h:70 | 
// src: src/ast/seq/seq_mem_facet.h:71 | str_mem(ast_manager& m, expr* s, view const& v, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_mem_facet.h:72 | m_str(m), m_view(v), m_dep(dep) {
// src: src/ast/seq/seq_mem_facet.h:73 | seq_util(m).str.get_concat_units(s, m_str);
// src: src/ast/seq/seq_mem_facet.h:74 | }
// src: src/ast/seq/seq_mem_facet.h:75 | str_mem(ast_manager& m, expr_ref_vector const& ts, view const& v, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_mem_facet.h:76 | m_str(ts), m_view(v), m_dep(dep) {}
// src: src/ast/seq/seq_mem_facet.h:77 | 
// src: src/ast/seq/seq_mem_facet.h:78 | bool is_plain() const { return m_view.is_membership(); }
// src: src/ast/seq/seq_mem_facet.h:79 | bool is_view() const { return m_view.is_reach(); }
// src: src/ast/seq/seq_mem_facet.h:80 | bool active() const { return m_active; }
// src: src/ast/seq/seq_mem_facet.h:81 | 
// src: src/ast/seq/seq_mem_facet.h:82 | // -- stx::constraint_i (unsat-cache identity) --
// src: src/ast/seq/seq_mem_facet.h:83 | // Identity is (token list, view): the same string term driving
// src: src/ast/seq/seq_mem_facet.h:84 | // the same (state,target) automaton view. `clone()` intentionally
// src: src/ast/seq/seq_mem_facet.h:85 | // drops `m_dep`/`m_active` - see stx::constraint_i's class
// src: src/ast/seq/seq_mem_facet.h:86 | // comment - and recovers the ast_manager it needs from
// src: src/ast/seq/seq_mem_facet.h:87 | // `m_str`'s own ref-vector (str_mem itself holds no separate
// src: src/ast/seq/seq_mem_facet.h:88 | // `ast_manager&` member).
// src: src/ast/seq/seq_mem_facet.h:89 | uint64_t hash() const override;
// src: src/ast/seq/seq_mem_facet.h:90 | bool equals(stx::constraint_i const& other) const override;
// src: src/ast/seq/seq_mem_facet.h:91 | stx::constraint_i* clone() const override { return alloc(str_mem, m_str.get_manager(), m_str, m_view); }
// src: src/ast/seq/seq_mem_facet.h:92 | void* dep_handle() const override { return m_dep; }
// src: src/ast/seq/seq_mem_facet.h:93 | };
// src: src/ast/seq/seq_mem_facet.h:94 | 
{ if |ids|==0 then false else R(words,ids[0])==word || AcceptWord(ids[1..],words,word) }
// src: src/ast/seq/seq_mem_facet.cpp:886 | expr_ref len_expr(u.str.mk_length(v), m);
// src: src/ast/seq/seq_mem_facet.cpp:887 | rational k;
// src: src/ast/seq/seq_mem_facet.cpp:888 | if (sf.value(len_expr, k) && k.is_unsigned())
// src: src/ast/seq/seq_mem_facet.cpp:889 | lens.push_back({v, k.get_unsigned()});
// src: src/ast/seq/seq_mem_facet.cpp:890 | }
// src: src/ast/seq/seq_mem_facet.cpp:891 | }
// src: src/ast/seq/seq_mem_facet.cpp:892 | arith_util& au = ac.solver_facet_ref().get_arith_util();
// src: src/ast/seq/seq_mem_facet.cpp:893 | auto mk_len_eq = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:894 | return expr_ref(m.mk_eq(u.str.mk_length(req.v), au.mk_int(req.len)), m);
// src: src/ast/seq/seq_mem_facet.cpp:895 | };
// src: src/ast/seq/seq_mem_facet.cpp:896 | auto mk_exact_len = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:897 | app* full_char = u.re.mk_full_char(u.re.mk_re(req.v->get_sort()));
// src: src/ast/seq/seq_mem_facet.cpp:898 | return expr_ref(u.re.mk_loop_proper(full_char, req.len, req.len), m);
// src: src/ast/seq/seq_mem_facet.cpp:899 | };
// src: src/ast/seq/seq_mem_facet.cpp:900 | for (auto const& req : lens) {
// src: src/ast/seq/seq_mem_facet.cpp:901 | eq_tree::dep_tracker cond_dep = ac.add_conditional_dep(mk_len_eq(req));
// src: src/ast/seq/seq_mem_facet.cpp:902 | vw.add_untrailed(req.v, view::membership(mk_exact_len(req), m), static_cast<void*>(cond_dep));
// src: src/ast/seq/seq_mem_facet.cpp:903 | }
// src: src/ast/seq/seq_mem_facet.cpp:904 | 
// src: src/ast/seq/seq_mem_facet.cpp:905 | vw.set_enable_witness(true);
// src: src/ast/seq/seq_mem_facet.cpp:906 | f.reset_vw_budget();
// src: src/ast/seq/seq_mem_facet.cpp:907 | lbool r = vw.check();
// src: src/ast/seq/seq_mem_facet.cpp:908 | if (r == l_false) {
// src: src/ast/seq/seq_mem_facet.cpp:909 | eq_tree::dep_tracker dep = nullptr;
// src: src/ast/seq/seq_mem_facet.cpp:910 | for (void* d : vw.core())
// src: src/ast/seq/seq_mem_facet.cpp:911 | dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
// src: src/ast/seq/seq_mem_facet.cpp:912 | n.set_conflict(stx::br_plugin_base, dep);
// src: src/ast/seq/seq_mem_facet.cpp:913 | return stx::simplify_result::conflict;
ghost predicate BackgroundAllows(any: bool, lengths: seq<int>, n: int)
// src: src/ast/seq/seq_mem_facet.cpp:886 | expr_ref len_expr(u.str.mk_length(v), m);
// src: src/ast/seq/seq_mem_facet.cpp:887 | rational k;
// src: src/ast/seq/seq_mem_facet.cpp:888 | if (sf.value(len_expr, k) && k.is_unsigned())
// src: src/ast/seq/seq_mem_facet.cpp:889 | lens.push_back({v, k.get_unsigned()});
// src: src/ast/seq/seq_mem_facet.cpp:890 | }
// src: src/ast/seq/seq_mem_facet.cpp:891 | }
// src: src/ast/seq/seq_mem_facet.cpp:892 | arith_util& au = ac.solver_facet_ref().get_arith_util();
// src: src/ast/seq/seq_mem_facet.cpp:893 | auto mk_len_eq = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:894 | return expr_ref(m.mk_eq(u.str.mk_length(req.v), au.mk_int(req.len)), m);
// src: src/ast/seq/seq_mem_facet.cpp:895 | };
// src: src/ast/seq/seq_mem_facet.cpp:896 | auto mk_exact_len = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:897 | app* full_char = u.re.mk_full_char(u.re.mk_re(req.v->get_sort()));
// src: src/ast/seq/seq_mem_facet.cpp:898 | return expr_ref(u.re.mk_loop_proper(full_char, req.len, req.len), m);
// src: src/ast/seq/seq_mem_facet.cpp:899 | };
// src: src/ast/seq/seq_mem_facet.cpp:900 | for (auto const& req : lens) {
// src: src/ast/seq/seq_mem_facet.cpp:901 | eq_tree::dep_tracker cond_dep = ac.add_conditional_dep(mk_len_eq(req));
// src: src/ast/seq/seq_mem_facet.cpp:902 | vw.add_untrailed(req.v, view::membership(mk_exact_len(req), m), static_cast<void*>(cond_dep));
// src: src/ast/seq/seq_mem_facet.cpp:903 | }
// src: src/ast/seq/seq_mem_facet.cpp:904 | 
// src: src/ast/seq/seq_mem_facet.cpp:905 | vw.set_enable_witness(true);
// src: src/ast/seq/seq_mem_facet.cpp:906 | f.reset_vw_budget();
// src: src/ast/seq/seq_mem_facet.cpp:907 | lbool r = vw.check();
// src: src/ast/seq/seq_mem_facet.cpp:908 | if (r == l_false) {
// src: src/ast/seq/seq_mem_facet.cpp:909 | eq_tree::dep_tracker dep = nullptr;
// src: src/ast/seq/seq_mem_facet.cpp:910 | for (void* d : vw.core())
// src: src/ast/seq/seq_mem_facet.cpp:911 | dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
// src: src/ast/seq/seq_mem_facet.cpp:912 | n.set_conflict(stx::br_plugin_base, dep);
// src: src/ast/seq/seq_mem_facet.cpp:913 | return stx::simplify_result::conflict;
{ n>=0 && (any || n in lengths) }
// src: src/ast/seq/seq_mem_facet.cpp:886 | expr_ref len_expr(u.str.mk_length(v), m);
// src: src/ast/seq/seq_mem_facet.cpp:887 | rational k;
// src: src/ast/seq/seq_mem_facet.cpp:888 | if (sf.value(len_expr, k) && k.is_unsigned())
// src: src/ast/seq/seq_mem_facet.cpp:889 | lens.push_back({v, k.get_unsigned()});
// src: src/ast/seq/seq_mem_facet.cpp:890 | }
// src: src/ast/seq/seq_mem_facet.cpp:891 | }
// src: src/ast/seq/seq_mem_facet.cpp:892 | arith_util& au = ac.solver_facet_ref().get_arith_util();
// src: src/ast/seq/seq_mem_facet.cpp:893 | auto mk_len_eq = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:894 | return expr_ref(m.mk_eq(u.str.mk_length(req.v), au.mk_int(req.len)), m);
// src: src/ast/seq/seq_mem_facet.cpp:895 | };
// src: src/ast/seq/seq_mem_facet.cpp:896 | auto mk_exact_len = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:897 | app* full_char = u.re.mk_full_char(u.re.mk_re(req.v->get_sort()));
// src: src/ast/seq/seq_mem_facet.cpp:898 | return expr_ref(u.re.mk_loop_proper(full_char, req.len, req.len), m);
// src: src/ast/seq/seq_mem_facet.cpp:899 | };
// src: src/ast/seq/seq_mem_facet.cpp:900 | for (auto const& req : lens) {
// src: src/ast/seq/seq_mem_facet.cpp:901 | eq_tree::dep_tracker cond_dep = ac.add_conditional_dep(mk_len_eq(req));
// src: src/ast/seq/seq_mem_facet.cpp:902 | vw.add_untrailed(req.v, view::membership(mk_exact_len(req), m), static_cast<void*>(cond_dep));
// src: src/ast/seq/seq_mem_facet.cpp:903 | }
// src: src/ast/seq/seq_mem_facet.cpp:904 | 
// src: src/ast/seq/seq_mem_facet.cpp:905 | vw.set_enable_witness(true);
// src: src/ast/seq/seq_mem_facet.cpp:906 | f.reset_vw_budget();
// src: src/ast/seq/seq_mem_facet.cpp:907 | lbool r = vw.check();
// src: src/ast/seq/seq_mem_facet.cpp:908 | if (r == l_false) {
// src: src/ast/seq/seq_mem_facet.cpp:909 | eq_tree::dep_tracker dep = nullptr;
// src: src/ast/seq/seq_mem_facet.cpp:910 | for (void* d : vw.core())
// src: src/ast/seq/seq_mem_facet.cpp:911 | dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
// src: src/ast/seq/seq_mem_facet.cpp:912 | n.set_conflict(stx::br_plugin_base, dep);
// src: src/ast/seq/seq_mem_facet.cpp:913 | return stx::simplify_result::conflict;
ghost predicate JointSatisfiable(values: seq<int>, words: seq<seq<int>>, langs: seq<seq<int>>, any: bool, lengths: seq<int>, guessed: bool, n: int)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_mem_facet.cpp:886 | expr_ref len_expr(u.str.mk_length(v), m);
// src: src/ast/seq/seq_mem_facet.cpp:887 | rational k;
// src: src/ast/seq/seq_mem_facet.cpp:888 | if (sf.value(len_expr, k) && k.is_unsigned())
// src: src/ast/seq/seq_mem_facet.cpp:889 | lens.push_back({v, k.get_unsigned()});
// src: src/ast/seq/seq_mem_facet.cpp:890 | }
// src: src/ast/seq/seq_mem_facet.cpp:891 | }
// src: src/ast/seq/seq_mem_facet.cpp:892 | arith_util& au = ac.solver_facet_ref().get_arith_util();
// src: src/ast/seq/seq_mem_facet.cpp:893 | auto mk_len_eq = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:894 | return expr_ref(m.mk_eq(u.str.mk_length(req.v), au.mk_int(req.len)), m);
// src: src/ast/seq/seq_mem_facet.cpp:895 | };
// src: src/ast/seq/seq_mem_facet.cpp:896 | auto mk_exact_len = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:897 | app* full_char = u.re.mk_full_char(u.re.mk_re(req.v->get_sort()));
// src: src/ast/seq/seq_mem_facet.cpp:898 | return expr_ref(u.re.mk_loop_proper(full_char, req.len, req.len), m);
// src: src/ast/seq/seq_mem_facet.cpp:899 | };
// src: src/ast/seq/seq_mem_facet.cpp:900 | for (auto const& req : lens) {
// src: src/ast/seq/seq_mem_facet.cpp:901 | eq_tree::dep_tracker cond_dep = ac.add_conditional_dep(mk_len_eq(req));
// src: src/ast/seq/seq_mem_facet.cpp:902 | vw.add_untrailed(req.v, view::membership(mk_exact_len(req), m), static_cast<void*>(cond_dep));
// src: src/ast/seq/seq_mem_facet.cpp:903 | }
// src: src/ast/seq/seq_mem_facet.cpp:904 | 
// src: src/ast/seq/seq_mem_facet.cpp:905 | vw.set_enable_witness(true);
// src: src/ast/seq/seq_mem_facet.cpp:906 | f.reset_vw_budget();
// src: src/ast/seq/seq_mem_facet.cpp:907 | lbool r = vw.check();
// src: src/ast/seq/seq_mem_facet.cpp:908 | if (r == l_false) {
// src: src/ast/seq/seq_mem_facet.cpp:909 | eq_tree::dep_tracker dep = nullptr;
// src: src/ast/seq/seq_mem_facet.cpp:910 | for (void* d : vw.core())
// src: src/ast/seq/seq_mem_facet.cpp:911 | dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
// src: src/ast/seq/seq_mem_facet.cpp:912 | n.set_conflict(stx::br_plugin_base, dep);
// src: src/ast/seq/seq_mem_facet.cpp:913 | return stx::simplify_result::conflict;
  if |values|==0 then (if guessed then BackgroundAllows(any,lengths,n) else any || (exists k :: k in lengths && k>=0))
// src: src/ast/seq/seq_mem_facet.cpp:886 | expr_ref len_expr(u.str.mk_length(v), m);
// src: src/ast/seq/seq_mem_facet.cpp:887 | rational k;
// src: src/ast/seq/seq_mem_facet.cpp:888 | if (sf.value(len_expr, k) && k.is_unsigned())
// src: src/ast/seq/seq_mem_facet.cpp:889 | lens.push_back({v, k.get_unsigned()});
// src: src/ast/seq/seq_mem_facet.cpp:890 | }
// src: src/ast/seq/seq_mem_facet.cpp:891 | }
// src: src/ast/seq/seq_mem_facet.cpp:892 | arith_util& au = ac.solver_facet_ref().get_arith_util();
// src: src/ast/seq/seq_mem_facet.cpp:893 | auto mk_len_eq = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:894 | return expr_ref(m.mk_eq(u.str.mk_length(req.v), au.mk_int(req.len)), m);
// src: src/ast/seq/seq_mem_facet.cpp:895 | };
// src: src/ast/seq/seq_mem_facet.cpp:896 | auto mk_exact_len = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:897 | app* full_char = u.re.mk_full_char(u.re.mk_re(req.v->get_sort()));
// src: src/ast/seq/seq_mem_facet.cpp:898 | return expr_ref(u.re.mk_loop_proper(full_char, req.len, req.len), m);
// src: src/ast/seq/seq_mem_facet.cpp:899 | };
// src: src/ast/seq/seq_mem_facet.cpp:900 | for (auto const& req : lens) {
// src: src/ast/seq/seq_mem_facet.cpp:901 | eq_tree::dep_tracker cond_dep = ac.add_conditional_dep(mk_len_eq(req));
// src: src/ast/seq/seq_mem_facet.cpp:902 | vw.add_untrailed(req.v, view::membership(mk_exact_len(req), m), static_cast<void*>(cond_dep));
// src: src/ast/seq/seq_mem_facet.cpp:903 | }
// src: src/ast/seq/seq_mem_facet.cpp:904 | 
// src: src/ast/seq/seq_mem_facet.cpp:905 | vw.set_enable_witness(true);
// src: src/ast/seq/seq_mem_facet.cpp:906 | f.reset_vw_budget();
// src: src/ast/seq/seq_mem_facet.cpp:907 | lbool r = vw.check();
// src: src/ast/seq/seq_mem_facet.cpp:908 | if (r == l_false) {
// src: src/ast/seq/seq_mem_facet.cpp:909 | eq_tree::dep_tracker dep = nullptr;
// src: src/ast/seq/seq_mem_facet.cpp:910 | for (void* d : vw.core())
// src: src/ast/seq/seq_mem_facet.cpp:911 | dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
// src: src/ast/seq/seq_mem_facet.cpp:912 | n.set_conflict(stx::br_plugin_base, dep);
// src: src/ast/seq/seq_mem_facet.cpp:913 | return stx::simplify_result::conflict;
  else exists w :: 0<=w<|words| && BackgroundAllows(any,lengths,|words[w]|) && (!guessed || |words[w]|==n) && (forall v :: v in values ==> AcceptWord(R(langs,v),words,words[w]))
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_mem_facet.cpp:886 | expr_ref len_expr(u.str.mk_length(v), m);
// src: src/ast/seq/seq_mem_facet.cpp:887 | rational k;
// src: src/ast/seq/seq_mem_facet.cpp:888 | if (sf.value(len_expr, k) && k.is_unsigned())
// src: src/ast/seq/seq_mem_facet.cpp:889 | lens.push_back({v, k.get_unsigned()});
// src: src/ast/seq/seq_mem_facet.cpp:890 | }
// src: src/ast/seq/seq_mem_facet.cpp:891 | }
// src: src/ast/seq/seq_mem_facet.cpp:892 | arith_util& au = ac.solver_facet_ref().get_arith_util();
// src: src/ast/seq/seq_mem_facet.cpp:893 | auto mk_len_eq = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:894 | return expr_ref(m.mk_eq(u.str.mk_length(req.v), au.mk_int(req.len)), m);
// src: src/ast/seq/seq_mem_facet.cpp:895 | };
// src: src/ast/seq/seq_mem_facet.cpp:896 | auto mk_exact_len = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:897 | app* full_char = u.re.mk_full_char(u.re.mk_re(req.v->get_sort()));
// src: src/ast/seq/seq_mem_facet.cpp:898 | return expr_ref(u.re.mk_loop_proper(full_char, req.len, req.len), m);
// src: src/ast/seq/seq_mem_facet.cpp:899 | };
// src: src/ast/seq/seq_mem_facet.cpp:900 | for (auto const& req : lens) {
// src: src/ast/seq/seq_mem_facet.cpp:901 | eq_tree::dep_tracker cond_dep = ac.add_conditional_dep(mk_len_eq(req));
// src: src/ast/seq/seq_mem_facet.cpp:902 | vw.add_untrailed(req.v, view::membership(mk_exact_len(req), m), static_cast<void*>(cond_dep));
// src: src/ast/seq/seq_mem_facet.cpp:903 | }
// src: src/ast/seq/seq_mem_facet.cpp:904 | 
// src: src/ast/seq/seq_mem_facet.cpp:905 | vw.set_enable_witness(true);
// src: src/ast/seq/seq_mem_facet.cpp:906 | f.reset_vw_budget();
// src: src/ast/seq/seq_mem_facet.cpp:907 | lbool r = vw.check();
// src: src/ast/seq/seq_mem_facet.cpp:908 | if (r == l_false) {
// src: src/ast/seq/seq_mem_facet.cpp:909 | eq_tree::dep_tracker dep = nullptr;
// src: src/ast/seq/seq_mem_facet.cpp:910 | for (void* d : vw.core())
// src: src/ast/seq/seq_mem_facet.cpp:911 | dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
// src: src/ast/seq/seq_mem_facet.cpp:912 | n.set_conflict(stx::br_plugin_base, dep);
// src: src/ast/seq/seq_mem_facet.cpp:913 | return stx::simplify_result::conflict;
ghost predicate ClosingCertificate(fc: seq<bool>, fw: seq<int>, fv: seq<int>, dh: seq<bool>, dw: seq<int>, di: seq<int>, ch: bool, cl: seq<int>, words: seq<seq<int>>, langs: seq<seq<int>>, any: bool, lengths: seq<int>, guessed: bool, n: int, leaf: int, proof: seq<int>)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_mem_facet.cpp:886 | expr_ref len_expr(u.str.mk_length(v), m);
// src: src/ast/seq/seq_mem_facet.cpp:887 | rational k;
// src: src/ast/seq/seq_mem_facet.cpp:888 | if (sf.value(len_expr, k) && k.is_unsigned())
// src: src/ast/seq/seq_mem_facet.cpp:889 | lens.push_back({v, k.get_unsigned()});
// src: src/ast/seq/seq_mem_facet.cpp:890 | }
// src: src/ast/seq/seq_mem_facet.cpp:891 | }
// src: src/ast/seq/seq_mem_facet.cpp:892 | arith_util& au = ac.solver_facet_ref().get_arith_util();
// src: src/ast/seq/seq_mem_facet.cpp:893 | auto mk_len_eq = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:894 | return expr_ref(m.mk_eq(u.str.mk_length(req.v), au.mk_int(req.len)), m);
// src: src/ast/seq/seq_mem_facet.cpp:895 | };
// src: src/ast/seq/seq_mem_facet.cpp:896 | auto mk_exact_len = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:897 | app* full_char = u.re.mk_full_char(u.re.mk_re(req.v->get_sort()));
// src: src/ast/seq/seq_mem_facet.cpp:898 | return expr_ref(u.re.mk_loop_proper(full_char, req.len, req.len), m);
// src: src/ast/seq/seq_mem_facet.cpp:899 | };
// src: src/ast/seq/seq_mem_facet.cpp:900 | for (auto const& req : lens) {
// src: src/ast/seq/seq_mem_facet.cpp:901 | eq_tree::dep_tracker cond_dep = ac.add_conditional_dep(mk_len_eq(req));
// src: src/ast/seq/seq_mem_facet.cpp:902 | vw.add_untrailed(req.v, view::membership(mk_exact_len(req), m), static_cast<void*>(cond_dep));
// src: src/ast/seq/seq_mem_facet.cpp:903 | }
// src: src/ast/seq/seq_mem_facet.cpp:904 | 
// src: src/ast/seq/seq_mem_facet.cpp:905 | vw.set_enable_witness(true);
// src: src/ast/seq/seq_mem_facet.cpp:906 | f.reset_vw_budget();
// src: src/ast/seq/seq_mem_facet.cpp:907 | lbool r = vw.check();
// src: src/ast/seq/seq_mem_facet.cpp:908 | if (r == l_false) {
// src: src/ast/seq/seq_mem_facet.cpp:909 | eq_tree::dep_tracker dep = nullptr;
// src: src/ast/seq/seq_mem_facet.cpp:910 | for (void* d : vw.core())
// src: src/ast/seq/seq_mem_facet.cpp:911 | dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
// src: src/ast/seq/seq_mem_facet.cpp:912 | n.set_conflict(stx::br_plugin_base, dep);
// src: src/ast/seq/seq_mem_facet.cpp:913 | return stx::simplify_result::conflict;
  var collected := Collect(fc,fw,0,0);
// src: src/ast/seq/seq_mem_facet.cpp:886 | expr_ref len_expr(u.str.mk_length(v), m);
// src: src/ast/seq/seq_mem_facet.cpp:887 | rational k;
// src: src/ast/seq/seq_mem_facet.cpp:888 | if (sf.value(len_expr, k) && k.is_unsigned())
// src: src/ast/seq/seq_mem_facet.cpp:889 | lens.push_back({v, k.get_unsigned()});
// src: src/ast/seq/seq_mem_facet.cpp:890 | }
// src: src/ast/seq/seq_mem_facet.cpp:891 | }
// src: src/ast/seq/seq_mem_facet.cpp:892 | arith_util& au = ac.solver_facet_ref().get_arith_util();
// src: src/ast/seq/seq_mem_facet.cpp:893 | auto mk_len_eq = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:894 | return expr_ref(m.mk_eq(u.str.mk_length(req.v), au.mk_int(req.len)), m);
// src: src/ast/seq/seq_mem_facet.cpp:895 | };
// src: src/ast/seq/seq_mem_facet.cpp:896 | auto mk_exact_len = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:897 | app* full_char = u.re.mk_full_char(u.re.mk_re(req.v->get_sort()));
// src: src/ast/seq/seq_mem_facet.cpp:898 | return expr_ref(u.re.mk_loop_proper(full_char, req.len, req.len), m);
// src: src/ast/seq/seq_mem_facet.cpp:899 | };
// src: src/ast/seq/seq_mem_facet.cpp:900 | for (auto const& req : lens) {
// src: src/ast/seq/seq_mem_facet.cpp:901 | eq_tree::dep_tracker cond_dep = ac.add_conditional_dep(mk_len_eq(req));
// src: src/ast/seq/seq_mem_facet.cpp:902 | vw.add_untrailed(req.v, view::membership(mk_exact_len(req), m), static_cast<void*>(cond_dep));
// src: src/ast/seq/seq_mem_facet.cpp:903 | }
// src: src/ast/seq/seq_mem_facet.cpp:904 | 
// src: src/ast/seq/seq_mem_facet.cpp:905 | vw.set_enable_witness(true);
// src: src/ast/seq/seq_mem_facet.cpp:906 | f.reset_vw_budget();
// src: src/ast/seq/seq_mem_facet.cpp:907 | lbool r = vw.check();
// src: src/ast/seq/seq_mem_facet.cpp:908 | if (r == l_false) {
// src: src/ast/seq/seq_mem_facet.cpp:909 | eq_tree::dep_tracker dep = nullptr;
// src: src/ast/seq/seq_mem_facet.cpp:910 | for (void* d : vw.core())
// src: src/ast/seq/seq_mem_facet.cpp:911 | dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
// src: src/ast/seq/seq_mem_facet.cpp:912 | n.set_conflict(stx::br_plugin_base, dep);
// src: src/ast/seq/seq_mem_facet.cpp:913 | return stx::simplify_result::conflict;
  (forall p :: p in proof ==> p in collected && (if ch then !B(dh,p) || Subset(R(Rows(dw,di),p),cl) else !B(dh,p))) &&
// src: src/ast/seq/seq_mem_facet.cpp:886 | expr_ref len_expr(u.str.mk_length(v), m);
// src: src/ast/seq/seq_mem_facet.cpp:887 | rational k;
// src: src/ast/seq/seq_mem_facet.cpp:888 | if (sf.value(len_expr, k) && k.is_unsigned())
// src: src/ast/seq/seq_mem_facet.cpp:889 | lens.push_back({v, k.get_unsigned()});
// src: src/ast/seq/seq_mem_facet.cpp:890 | }
// src: src/ast/seq/seq_mem_facet.cpp:891 | }
// src: src/ast/seq/seq_mem_facet.cpp:892 | arith_util& au = ac.solver_facet_ref().get_arith_util();
// src: src/ast/seq/seq_mem_facet.cpp:893 | auto mk_len_eq = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:894 | return expr_ref(m.mk_eq(u.str.mk_length(req.v), au.mk_int(req.len)), m);
// src: src/ast/seq/seq_mem_facet.cpp:895 | };
// src: src/ast/seq/seq_mem_facet.cpp:896 | auto mk_exact_len = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:897 | app* full_char = u.re.mk_full_char(u.re.mk_re(req.v->get_sort()));
// src: src/ast/seq/seq_mem_facet.cpp:898 | return expr_ref(u.re.mk_loop_proper(full_char, req.len, req.len), m);
// src: src/ast/seq/seq_mem_facet.cpp:899 | };
// src: src/ast/seq/seq_mem_facet.cpp:900 | for (auto const& req : lens) {
// src: src/ast/seq/seq_mem_facet.cpp:901 | eq_tree::dep_tracker cond_dep = ac.add_conditional_dep(mk_len_eq(req));
// src: src/ast/seq/seq_mem_facet.cpp:902 | vw.add_untrailed(req.v, view::membership(mk_exact_len(req), m), static_cast<void*>(cond_dep));
// src: src/ast/seq/seq_mem_facet.cpp:903 | }
// src: src/ast/seq/seq_mem_facet.cpp:904 | 
// src: src/ast/seq/seq_mem_facet.cpp:905 | vw.set_enable_witness(true);
// src: src/ast/seq/seq_mem_facet.cpp:906 | f.reset_vw_budget();
// src: src/ast/seq/seq_mem_facet.cpp:907 | lbool r = vw.check();
// src: src/ast/seq/seq_mem_facet.cpp:908 | if (r == l_false) {
// src: src/ast/seq/seq_mem_facet.cpp:909 | eq_tree::dep_tracker dep = nullptr;
// src: src/ast/seq/seq_mem_facet.cpp:910 | for (void* d : vw.core())
// src: src/ast/seq/seq_mem_facet.cpp:911 | dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
// src: src/ast/seq/seq_mem_facet.cpp:912 | n.set_conflict(stx::br_plugin_base, dep);
// src: src/ast/seq/seq_mem_facet.cpp:913 | return stx::simplify_result::conflict;
  (guessed ==> ch && leaf in cl && BackgroundAllows(any,lengths,n) && (forall p :: p in collected ==> exists w :: 0<=w<|words| && |words[w]|==n && AcceptWord(R(langs,I(fv,p)),words,words[w]))) &&
// src: src/ast/seq/seq_mem_facet.cpp:886 | expr_ref len_expr(u.str.mk_length(v), m);
// src: src/ast/seq/seq_mem_facet.cpp:887 | rational k;
// src: src/ast/seq/seq_mem_facet.cpp:888 | if (sf.value(len_expr, k) && k.is_unsigned())
// src: src/ast/seq/seq_mem_facet.cpp:889 | lens.push_back({v, k.get_unsigned()});
// src: src/ast/seq/seq_mem_facet.cpp:890 | }
// src: src/ast/seq/seq_mem_facet.cpp:891 | }
// src: src/ast/seq/seq_mem_facet.cpp:892 | arith_util& au = ac.solver_facet_ref().get_arith_util();
// src: src/ast/seq/seq_mem_facet.cpp:893 | auto mk_len_eq = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:894 | return expr_ref(m.mk_eq(u.str.mk_length(req.v), au.mk_int(req.len)), m);
// src: src/ast/seq/seq_mem_facet.cpp:895 | };
// src: src/ast/seq/seq_mem_facet.cpp:896 | auto mk_exact_len = [&](len_req const& req) {
// src: src/ast/seq/seq_mem_facet.cpp:897 | app* full_char = u.re.mk_full_char(u.re.mk_re(req.v->get_sort()));
// src: src/ast/seq/seq_mem_facet.cpp:898 | return expr_ref(u.re.mk_loop_proper(full_char, req.len, req.len), m);
// src: src/ast/seq/seq_mem_facet.cpp:899 | };
// src: src/ast/seq/seq_mem_facet.cpp:900 | for (auto const& req : lens) {
// src: src/ast/seq/seq_mem_facet.cpp:901 | eq_tree::dep_tracker cond_dep = ac.add_conditional_dep(mk_len_eq(req));
// src: src/ast/seq/seq_mem_facet.cpp:902 | vw.add_untrailed(req.v, view::membership(mk_exact_len(req), m), static_cast<void*>(cond_dep));
// src: src/ast/seq/seq_mem_facet.cpp:903 | }
// src: src/ast/seq/seq_mem_facet.cpp:904 | 
// src: src/ast/seq/seq_mem_facet.cpp:905 | vw.set_enable_witness(true);
// src: src/ast/seq/seq_mem_facet.cpp:906 | f.reset_vw_budget();
// src: src/ast/seq/seq_mem_facet.cpp:907 | lbool r = vw.check();
// src: src/ast/seq/seq_mem_facet.cpp:908 | if (r == l_false) {
// src: src/ast/seq/seq_mem_facet.cpp:909 | eq_tree::dep_tracker dep = nullptr;
// src: src/ast/seq/seq_mem_facet.cpp:910 | for (void* d : vw.core())
// src: src/ast/seq/seq_mem_facet.cpp:911 | dep = f.dm().mk_join(dep, static_cast<eq_tree::dep_tracker>(d));
// src: src/ast/seq/seq_mem_facet.cpp:912 | n.set_conflict(stx::br_plugin_base, dep);
// src: src/ast/seq/seq_mem_facet.cpp:913 | return stx::simplify_result::conflict;
  !JointSatisfiable(Pick(fv,proof),words,langs,any,lengths,guessed,n)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:619 | struct unsat_core_entry {
// src: src/util/stx_search_tree.h:620 | vector<unsigned> lits;   // over-approximate unsat core, as constraint-store ids
// src: src/util/stx_search_tree.h:621 | unsigned         watch;  // index into lits currently registered in m_watch_list
// src: src/util/stx_search_tree.h:622 | };
// src: src/util/stx_search_tree.h:623 | vector<unsat_core_entry>                          m_unsat_cores;
// src: src/util/stx_search_tree.h:624 | // constraint-store id -> indices (into m_unsat_cores) of cores
// src: src/util/stx_search_tree.h:625 | // currently watching it. Grown (via watch()) on demand as new ids
// src: src/util/stx_search_tree.h:626 | // are interned; an id past the current size simply has no cores
// src: src/util/stx_search_tree.h:627 | // watching it yet.
// src: src/util/stx_search_tree.h:628 | vector<vector<unsigned>>                          m_watch_list;
// src: src/util/stx_search_tree.h:660 | // Register `core_idx` as watching constraint-store id `id`,
// src: src/util/stx_search_tree.h:661 | // growing `m_watch_list` on demand (ids are assigned densely from
// src: src/util/stx_search_tree.h:662 | // 0 by `constraint_store`, so a plain resize-then-index keeps this
// src: src/util/stx_search_tree.h:663 | // O(1) amortized, same as `vector::push_back`).
// src: src/util/stx_search_tree.h:664 | void watch(unsigned id, unsigned core_idx) {
// src: src/util/stx_search_tree.h:665 | if (id >= m_watch_list.size())
// src: src/util/stx_search_tree.h:666 | m_watch_list.resize(id + 1);
// src: src/util/stx_search_tree.h:667 | m_watch_list[id].push_back(core_idx);
// src: src/util/stx_search_tree.h:668 | }
ghost predicate CacheStateWellFormed(store: seq<int>, cores: seq<seq<int>>, watches: seq<int>, buckets: seq<seq<int>>, nlangs: int)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:619 | struct unsat_core_entry {
// src: src/util/stx_search_tree.h:620 | vector<unsigned> lits;   // over-approximate unsat core, as constraint-store ids
// src: src/util/stx_search_tree.h:621 | unsigned         watch;  // index into lits currently registered in m_watch_list
// src: src/util/stx_search_tree.h:622 | };
// src: src/util/stx_search_tree.h:623 | vector<unsat_core_entry>                          m_unsat_cores;
// src: src/util/stx_search_tree.h:624 | // constraint-store id -> indices (into m_unsat_cores) of cores
// src: src/util/stx_search_tree.h:625 | // currently watching it. Grown (via watch()) on demand as new ids
// src: src/util/stx_search_tree.h:626 | // are interned; an id past the current size simply has no cores
// src: src/util/stx_search_tree.h:627 | // watching it yet.
// src: src/util/stx_search_tree.h:628 | vector<vector<unsigned>>                          m_watch_list;
// src: src/util/stx_search_tree.h:660 | // Register `core_idx` as watching constraint-store id `id`,
// src: src/util/stx_search_tree.h:661 | // growing `m_watch_list` on demand (ids are assigned densely from
// src: src/util/stx_search_tree.h:662 | // 0 by `constraint_store`, so a plain resize-then-index keeps this
// src: src/util/stx_search_tree.h:663 | // O(1) amortized, same as `vector::push_back`).
// src: src/util/stx_search_tree.h:664 | void watch(unsigned id, unsigned core_idx) {
// src: src/util/stx_search_tree.h:665 | if (id >= m_watch_list.size())
// src: src/util/stx_search_tree.h:666 | m_watch_list.resize(id + 1);
// src: src/util/stx_search_tree.h:667 | m_watch_list[id].push_back(core_idx);
// src: src/util/stx_search_tree.h:668 | }
  Unique(store) && (forall v :: v in store ==> 0<=v<nlangs) && |watches|==|cores| && |buckets|<=|store| &&
// src: src/util/stx_search_tree.h:619 | struct unsat_core_entry {
// src: src/util/stx_search_tree.h:620 | vector<unsigned> lits;   // over-approximate unsat core, as constraint-store ids
// src: src/util/stx_search_tree.h:621 | unsigned         watch;  // index into lits currently registered in m_watch_list
// src: src/util/stx_search_tree.h:622 | };
// src: src/util/stx_search_tree.h:623 | vector<unsat_core_entry>                          m_unsat_cores;
// src: src/util/stx_search_tree.h:624 | // constraint-store id -> indices (into m_unsat_cores) of cores
// src: src/util/stx_search_tree.h:625 | // currently watching it. Grown (via watch()) on demand as new ids
// src: src/util/stx_search_tree.h:626 | // are interned; an id past the current size simply has no cores
// src: src/util/stx_search_tree.h:627 | // watching it yet.
// src: src/util/stx_search_tree.h:628 | vector<vector<unsigned>>                          m_watch_list;
// src: src/util/stx_search_tree.h:660 | // Register `core_idx` as watching constraint-store id `id`,
// src: src/util/stx_search_tree.h:661 | // growing `m_watch_list` on demand (ids are assigned densely from
// src: src/util/stx_search_tree.h:662 | // 0 by `constraint_store`, so a plain resize-then-index keeps this
// src: src/util/stx_search_tree.h:663 | // O(1) amortized, same as `vector::push_back`).
// src: src/util/stx_search_tree.h:664 | void watch(unsigned id, unsigned core_idx) {
// src: src/util/stx_search_tree.h:665 | if (id >= m_watch_list.size())
// src: src/util/stx_search_tree.h:666 | m_watch_list.resize(id + 1);
// src: src/util/stx_search_tree.h:667 | m_watch_list[id].push_back(core_idx);
// src: src/util/stx_search_tree.h:668 | }
  (forall c :: 0<=c<|cores| ==> |cores[c]|>0 && 0<=watches[c]<|cores[c]| && (forall id :: id in cores[c] ==> 0<=id<|store|) &&
// src: src/util/stx_search_tree.h:619 | struct unsat_core_entry {
// src: src/util/stx_search_tree.h:620 | vector<unsigned> lits;   // over-approximate unsat core, as constraint-store ids
// src: src/util/stx_search_tree.h:621 | unsigned         watch;  // index into lits currently registered in m_watch_list
// src: src/util/stx_search_tree.h:622 | };
// src: src/util/stx_search_tree.h:623 | vector<unsat_core_entry>                          m_unsat_cores;
// src: src/util/stx_search_tree.h:624 | // constraint-store id -> indices (into m_unsat_cores) of cores
// src: src/util/stx_search_tree.h:625 | // currently watching it. Grown (via watch()) on demand as new ids
// src: src/util/stx_search_tree.h:626 | // are interned; an id past the current size simply has no cores
// src: src/util/stx_search_tree.h:627 | // watching it yet.
// src: src/util/stx_search_tree.h:628 | vector<vector<unsigned>>                          m_watch_list;
// src: src/util/stx_search_tree.h:660 | // Register `core_idx` as watching constraint-store id `id`,
// src: src/util/stx_search_tree.h:661 | // growing `m_watch_list` on demand (ids are assigned densely from
// src: src/util/stx_search_tree.h:662 | // 0 by `constraint_store`, so a plain resize-then-index keeps this
// src: src/util/stx_search_tree.h:663 | // O(1) amortized, same as `vector::push_back`).
// src: src/util/stx_search_tree.h:664 | void watch(unsigned id, unsigned core_idx) {
// src: src/util/stx_search_tree.h:665 | if (id >= m_watch_list.size())
// src: src/util/stx_search_tree.h:666 | m_watch_list.resize(id + 1);
// src: src/util/stx_search_tree.h:667 | m_watch_list[id].push_back(core_idx);
// src: src/util/stx_search_tree.h:668 | }
    0<=I(cores[c],watches[c])<|buckets| && (forall b :: 0<=b<|buckets| ==> Count(buckets[b],c)==(if b==I(cores[c],watches[c]) then 1 else 0))) &&
// src: src/util/stx_search_tree.h:619 | struct unsat_core_entry {
// src: src/util/stx_search_tree.h:620 | vector<unsigned> lits;   // over-approximate unsat core, as constraint-store ids
// src: src/util/stx_search_tree.h:621 | unsigned         watch;  // index into lits currently registered in m_watch_list
// src: src/util/stx_search_tree.h:622 | };
// src: src/util/stx_search_tree.h:623 | vector<unsat_core_entry>                          m_unsat_cores;
// src: src/util/stx_search_tree.h:624 | // constraint-store id -> indices (into m_unsat_cores) of cores
// src: src/util/stx_search_tree.h:625 | // currently watching it. Grown (via watch()) on demand as new ids
// src: src/util/stx_search_tree.h:626 | // are interned; an id past the current size simply has no cores
// src: src/util/stx_search_tree.h:627 | // watching it yet.
// src: src/util/stx_search_tree.h:628 | vector<vector<unsigned>>                          m_watch_list;
// src: src/util/stx_search_tree.h:660 | // Register `core_idx` as watching constraint-store id `id`,
// src: src/util/stx_search_tree.h:661 | // growing `m_watch_list` on demand (ids are assigned densely from
// src: src/util/stx_search_tree.h:662 | // 0 by `constraint_store`, so a plain resize-then-index keeps this
// src: src/util/stx_search_tree.h:663 | // O(1) amortized, same as `vector::push_back`).
// src: src/util/stx_search_tree.h:664 | void watch(unsigned id, unsigned core_idx) {
// src: src/util/stx_search_tree.h:665 | if (id >= m_watch_list.size())
// src: src/util/stx_search_tree.h:666 | m_watch_list.resize(id + 1);
// src: src/util/stx_search_tree.h:667 | m_watch_list[id].push_back(core_idx);
// src: src/util/stx_search_tree.h:668 | }
  (forall b,c :: 0<=b<|buckets| && c in buckets[b] ==> 0<=c<|cores|)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:807 | 
// src: src/util/stx_search_tree.h:808 | // Insert: memoize this node's current state as an (over-
// src: src/util/stx_search_tree.h:809 | // approximate) unsat core, and register it in the watch list.
// src: src/util/stx_search_tree.h:810 | // Only called at closure points the caller has already determined
// src: src/util/stx_search_tree.h:811 | // are a pure function of the signature-contributing facets (see
// src: src/util/stx_search_tree.h:812 | // dfs()); cache_eligible() is re-checked here regardless, as a
// src: src/util/stx_search_tree.h:813 | // second, cheap safety net.
// src: src/util/stx_search_tree.h:814 | //
// src: src/util/stx_search_tree.h:815 | // The initial watch is picked arbitrarily (lits[0]): the "watch is
// src: src/util/stx_search_tree.h:816 | // absent" invariant need not hold yet - this very node's active set
// src: src/util/stx_search_tree.h:817 | // is exactly (a superset of) the core being inserted, so every
// src: src/util/stx_search_tree.h:818 | // literal is present right now. It self-repairs the first time
// src: src/util/stx_search_tree.h:819 | // cache_lookup() visits some other node containing lits[0]: if
// src: src/util/stx_search_tree.h:820 | // every other literal is also active there, the core fires
// src: src/util/stx_search_tree.h:821 | // immediately (correctly - that node is unsat too); otherwise
// src: src/util/stx_search_tree.h:822 | // try_rewatch() moves the watch to a literal that is genuinely
// src: src/util/stx_search_tree.h:823 | // absent there, restoring the invariant for future checks.
// src: src/util/stx_search_tree.h:824 | void cache_insert(node const& n) {
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
// src: src/util/stx_search_tree.h:830 | // Narrow the over-approximate active set down to just the
// src: src/util/stx_search_tree.h:831 | // facts that could have contributed to THIS conflict (see
// src: src/util/stx_search_tree.h:832 | // filter_by_conflict_dep()'s comment) before interning
// src: src/util/stx_search_tree.h:833 | // anything: a smaller recorded core matches (as a subset)
// src: src/util/stx_search_tree.h:834 | // more future nodes, so this only ever helps the cache's hit
// src: src/util/stx_search_tree.h:835 | // rate, never hurts its soundness.
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
// src: src/util/stx_search_tree.h:846 | }
ghost predicate AllCoresUnsat(store: seq<int>, cores: seq<seq<int>>, words: seq<seq<int>>, langs: seq<seq<int>>, any: bool, lengths: seq<int>)
// src: src/util/stx_search_tree.h:807 | 
// src: src/util/stx_search_tree.h:808 | // Insert: memoize this node's current state as an (over-
// src: src/util/stx_search_tree.h:809 | // approximate) unsat core, and register it in the watch list.
// src: src/util/stx_search_tree.h:810 | // Only called at closure points the caller has already determined
// src: src/util/stx_search_tree.h:811 | // are a pure function of the signature-contributing facets (see
// src: src/util/stx_search_tree.h:812 | // dfs()); cache_eligible() is re-checked here regardless, as a
// src: src/util/stx_search_tree.h:813 | // second, cheap safety net.
// src: src/util/stx_search_tree.h:814 | //
// src: src/util/stx_search_tree.h:815 | // The initial watch is picked arbitrarily (lits[0]): the "watch is
// src: src/util/stx_search_tree.h:816 | // absent" invariant need not hold yet - this very node's active set
// src: src/util/stx_search_tree.h:817 | // is exactly (a superset of) the core being inserted, so every
// src: src/util/stx_search_tree.h:818 | // literal is present right now. It self-repairs the first time
// src: src/util/stx_search_tree.h:819 | // cache_lookup() visits some other node containing lits[0]: if
// src: src/util/stx_search_tree.h:820 | // every other literal is also active there, the core fires
// src: src/util/stx_search_tree.h:821 | // immediately (correctly - that node is unsat too); otherwise
// src: src/util/stx_search_tree.h:822 | // try_rewatch() moves the watch to a literal that is genuinely
// src: src/util/stx_search_tree.h:823 | // absent there, restoring the invariant for future checks.
// src: src/util/stx_search_tree.h:824 | void cache_insert(node const& n) {
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
// src: src/util/stx_search_tree.h:830 | // Narrow the over-approximate active set down to just the
// src: src/util/stx_search_tree.h:831 | // facts that could have contributed to THIS conflict (see
// src: src/util/stx_search_tree.h:832 | // filter_by_conflict_dep()'s comment) before interning
// src: src/util/stx_search_tree.h:833 | // anything: a smaller recorded core matches (as a subset)
// src: src/util/stx_search_tree.h:834 | // more future nodes, so this only ever helps the cache's hit
// src: src/util/stx_search_tree.h:835 | // rate, never hurts its soundness.
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
// src: src/util/stx_search_tree.h:846 | }
{ forall c :: 0<=c<|cores| ==> !JointSatisfiable(Pick(store,cores[c]),words,langs,any,lengths,false,0) }
// src: src/util/stx_search_tree.h:807 | 
// src: src/util/stx_search_tree.h:808 | // Insert: memoize this node's current state as an (over-
// src: src/util/stx_search_tree.h:809 | // approximate) unsat core, and register it in the watch list.
// src: src/util/stx_search_tree.h:810 | // Only called at closure points the caller has already determined
// src: src/util/stx_search_tree.h:811 | // are a pure function of the signature-contributing facets (see
// src: src/util/stx_search_tree.h:812 | // dfs()); cache_eligible() is re-checked here regardless, as a
// src: src/util/stx_search_tree.h:813 | // second, cheap safety net.
// src: src/util/stx_search_tree.h:814 | //
// src: src/util/stx_search_tree.h:815 | // The initial watch is picked arbitrarily (lits[0]): the "watch is
// src: src/util/stx_search_tree.h:816 | // absent" invariant need not hold yet - this very node's active set
// src: src/util/stx_search_tree.h:817 | // is exactly (a superset of) the core being inserted, so every
// src: src/util/stx_search_tree.h:818 | // literal is present right now. It self-repairs the first time
// src: src/util/stx_search_tree.h:819 | // cache_lookup() visits some other node containing lits[0]: if
// src: src/util/stx_search_tree.h:820 | // every other literal is also active there, the core fires
// src: src/util/stx_search_tree.h:821 | // immediately (correctly - that node is unsat too); otherwise
// src: src/util/stx_search_tree.h:822 | // try_rewatch() moves the watch to a literal that is genuinely
// src: src/util/stx_search_tree.h:823 | // absent there, restoring the invariant for future checks.
// src: src/util/stx_search_tree.h:824 | void cache_insert(node const& n) {
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
// src: src/util/stx_search_tree.h:830 | // Narrow the over-approximate active set down to just the
// src: src/util/stx_search_tree.h:831 | // facts that could have contributed to THIS conflict (see
// src: src/util/stx_search_tree.h:832 | // filter_by_conflict_dep()'s comment) before interning
// src: src/util/stx_search_tree.h:833 | // anything: a smaller recorded core matches (as a subset)
// src: src/util/stx_search_tree.h:834 | // more future nodes, so this only ever helps the cache's hit
// src: src/util/stx_search_tree.h:835 | // rate, never hurts its soundness.
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
// src: src/util/stx_search_tree.h:846 | }
ghost predicate CacheInsertExact(enabled: bool, fc: seq<bool>, fs: seq<bool>, fw: seq<int>, fv: seq<int>, dh: seq<bool>, dw: seq<int>, di: seq<int>, ch: bool, cl: seq<int>, store: seq<int>, cores: seq<seq<int>>, watches: seq<int>, buckets: seq<seq<int>>, inserted: bool, so: seq<int>, cw: seq<int>, ci: seq<int>, wo: seq<int>, bw: seq<int>, bi: seq<int>)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:807 | 
// src: src/util/stx_search_tree.h:808 | // Insert: memoize this node's current state as an (over-
// src: src/util/stx_search_tree.h:809 | // approximate) unsat core, and register it in the watch list.
// src: src/util/stx_search_tree.h:810 | // Only called at closure points the caller has already determined
// src: src/util/stx_search_tree.h:811 | // are a pure function of the signature-contributing facets (see
// src: src/util/stx_search_tree.h:812 | // dfs()); cache_eligible() is re-checked here regardless, as a
// src: src/util/stx_search_tree.h:813 | // second, cheap safety net.
// src: src/util/stx_search_tree.h:814 | //
// src: src/util/stx_search_tree.h:815 | // The initial watch is picked arbitrarily (lits[0]): the "watch is
// src: src/util/stx_search_tree.h:816 | // absent" invariant need not hold yet - this very node's active set
// src: src/util/stx_search_tree.h:817 | // is exactly (a superset of) the core being inserted, so every
// src: src/util/stx_search_tree.h:818 | // literal is present right now. It self-repairs the first time
// src: src/util/stx_search_tree.h:819 | // cache_lookup() visits some other node containing lits[0]: if
// src: src/util/stx_search_tree.h:820 | // every other literal is also active there, the core fires
// src: src/util/stx_search_tree.h:821 | // immediately (correctly - that node is unsat too); otherwise
// src: src/util/stx_search_tree.h:822 | // try_rewatch() moves the watch to a literal that is genuinely
// src: src/util/stx_search_tree.h:823 | // absent there, restoring the invariant for future checks.
// src: src/util/stx_search_tree.h:824 | void cache_insert(node const& n) {
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
// src: src/util/stx_search_tree.h:830 | // Narrow the over-approximate active set down to just the
// src: src/util/stx_search_tree.h:831 | // facts that could have contributed to THIS conflict (see
// src: src/util/stx_search_tree.h:832 | // filter_by_conflict_dep()'s comment) before interning
// src: src/util/stx_search_tree.h:833 | // anything: a smaller recorded core matches (as a subset)
// src: src/util/stx_search_tree.h:834 | // more future nodes, so this only ever helps the cache's hit
// src: src/util/stx_search_tree.h:835 | // rate, never hurts its soundness.
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
// src: src/util/stx_search_tree.h:846 | }
  (so,Rows(cw,ci),wo,Rows(bw,bi),inserted)==CacheExpected(enabled,fc,fs,fw,fv,dh,dw,di,ch,cl,store,cores,watches,buckets) && Partition(cw,ci) && Partition(bw,bi)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:824 | void cache_insert(node const& n) {
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
// src: src/util/stx_search_tree.h:830 | // Narrow the over-approximate active set down to just the
// src: src/util/stx_search_tree.h:831 | // facts that could have contributed to THIS conflict (see
// src: src/util/stx_search_tree.h:832 | // filter_by_conflict_dep()'s comment) before interning
// src: src/util/stx_search_tree.h:833 | // anything: a smaller recorded core matches (as a subset)
// src: src/util/stx_search_tree.h:834 | // more future nodes, so this only ever helps the cache's hit
// src: src/util/stx_search_tree.h:835 | // rate, never hurts its soundness.
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
// src: src/util/stx_search_tree.h:846 | }
method CacheInsertEntry(enabled: bool, facetContrib: seq<bool>, facetSatisfied: seq<bool>, facetWidths: seq<int>, facetValues: seq<int>, factHasDep: seq<bool>, factDepWidths: seq<int>, factDepItems: seq<int>, conflictHasDep: bool, conflictLeaves: seq<int>, wordWidths: seq<int>, wordChars: seq<int>, langWidths: seq<int>, langWords: seq<int>, backgroundAny: bool, backgroundLengths: seq<int>, guessPresent: bool, guessLength: int, guessLeaf: int, proofPositions: seq<int>, store: seq<int>, coreWidths: seq<int>, coreIds: seq<int>, coreWatch: seq<int>, bucketWidths: seq<int>, bucketItems: seq<int>) returns (inserted: bool, storeOut: seq<int>, coreWidthsOut: seq<int>, coreIdsOut: seq<int>, coreWatchOut: seq<int>, bucketWidthsOut: seq<int>, bucketItemsOut: seq<int>)
// synth: specification, checked annotation, or structural delimiter
  requires |facetContrib|==|facetSatisfied|==|facetWidths| && Partition(facetWidths,facetValues) && (forall f :: 0<=f<|facetWidths| && !facetContrib[f] ==> facetWidths[f]==0)
// synth: specification, checked annotation, or structural delimiter
  requires |factHasDep|==|factDepWidths|==|facetValues| && Partition(factDepWidths,factDepItems) && (forall p :: 0<=p<|factHasDep| && !factHasDep[p] ==> factDepWidths[p]==0) && (!conflictHasDep ==> conflictLeaves==[])
// synth: specification, checked annotation, or structural delimiter
  requires Partition(wordWidths,wordChars) && Partition(langWidths,langWords) && (forall w :: w in langWords ==> 0<=w<|wordWidths|) && (forall v :: v in facetValues ==> 0<=v<|langWidths|)
// synth: specification, checked annotation, or structural delimiter
  requires (forall c :: c in wordChars ==> 0<=c<=196607) && (forall n :: n in backgroundLengths ==> n>=0)
// synth: specification, checked annotation, or structural delimiter
  requires Partition(coreWidths,coreIds) && Partition(bucketWidths,bucketItems) && CacheStateWellFormed(store,Rows(coreWidths,coreIds),coreWatch,Rows(bucketWidths,bucketItems),|langWidths|)
// synth: specification, checked annotation, or structural delimiter
  requires |facetContrib|<4294967296 && |store|+|facetValues|<4294967296 && |coreWidths|+1<4294967296 && (forall w :: w in facetWidths+factDepWidths+wordWidths+langWidths+coreWidths+bucketWidths ==> 0<=w<4294967296) && (forall x :: x in factDepItems+conflictLeaves+[guessLeaf] ==> 0<=x<4294967296)
// synth: specification, checked annotation, or structural delimiter
  requires !(enabled && Eligible(facetContrib,facetSatisfied,0) && |Filter(Collect(facetContrib,facetWidths,0,0),factHasDep,factDepWidths,factDepItems,conflictHasDep,conflictLeaves)|>0) || ClosingCertificate(facetContrib,facetWidths,facetValues,factHasDep,factDepWidths,factDepItems,conflictHasDep,conflictLeaves,Rows(wordWidths,wordChars),Rows(langWidths,langWords),backgroundAny,backgroundLengths,guessPresent,guessLength,guessLeaf,proofPositions)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
  inserted,storeOut,coreWidthsOut,coreIdsOut,coreWatchOut,bucketWidthsOut,bucketItemsOut := false,store,coreWidths,coreIds,coreWatch,bucketWidths,bucketItems;
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
  if !enabled || !Eligible(facetContrib,facetSatisfied,0) { return; }
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
  var ps := Collect(facetContrib,facetWidths,0,0);
// src: src/util/stx_search_tree.h:825 | if (!m_unsat_cache_enabled || !cache_eligible(n))
// src: src/util/stx_search_tree.h:826 | return;
// src: src/util/stx_search_tree.h:827 | vector<constraint_i const*> cs = compute_constraints(n);
// src: src/util/stx_search_tree.h:828 | if (cs.empty())
// src: src/util/stx_search_tree.h:829 | return;
  if |ps|==0 { return; }
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
  ps := Filter(ps,factHasDep,factDepWidths,factDepItems,conflictHasDep,conflictLeaves);
// src: src/util/stx_search_tree.h:836 | filter_by_conflict_dep(cs, n.conflict_dep());
// src: src/util/stx_search_tree.h:837 | if (cs.empty())
// src: src/util/stx_search_tree.h:838 | return;
  if |ps|==0 { return; }
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
  var interned := InternList(Pick(facetValues,ps),store);
// src: src/util/stx_search_tree.h:839 | vector<unsigned> ids;
// src: src/util/stx_search_tree.h:840 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:841 | ids.push_back(m_constraint_store.intern(*c));
  storeOut := interned.0;
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
  var cores := Rows(coreWidths,coreIds)+[interned.1];
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
  coreWidthsOut,coreIdsOut := Widths(cores),Flat(cores);
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
  coreWatchOut := coreWatch+[0];
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
  var buckets := WatchAdd(Rows(bucketWidths,bucketItems),I(interned.1,0),|coreWidths|);
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
  bucketWidthsOut,bucketItemsOut := Widths(buckets),Flat(buckets);
// src: src/util/stx_search_tree.h:842 | unsigned idx = m_unsat_cores.size();
// src: src/util/stx_search_tree.h:843 | unsigned watch_id = ids[0];
// src: src/util/stx_search_tree.h:844 | m_unsat_cores.push_back({ std::move(ids), 0 });
// src: src/util/stx_search_tree.h:845 | watch(watch_id, idx);
  inserted := true;
// synth: specification, checked annotation, or structural delimiter
}
