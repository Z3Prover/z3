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
{ seq(|rows|, i => |R(rows,i)|) }
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

// src: src/ast/seq/seq_power_facet.h:108 | bool find_power(expr* e, unsigned& idx) const {
// src: src/ast/seq/seq_power_facet.h:109 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.h:110 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.h:111 | continue;
// src: src/ast/seq/seq_power_facet.h:112 | if (m_pows[i].m_e.get() == e) {
// src: src/ast/seq/seq_power_facet.h:113 | idx = i;
// src: src/ast/seq/seq_power_facet.h:114 | return true;
// src: src/ast/seq/seq_power_facet.h:115 | }
// src: src/ast/seq/seq_power_facet.h:116 | }
// src: src/ast/seq/seq_power_facet.h:117 | return false;
// src: src/ast/seq/seq_power_facet.h:118 | }
function FindActive(keys: seq<int>, active: seq<bool>, tok: int, i: int): int
// synth: specification, checked annotation, or structural delimiter
  decreases |keys|-i
// src: src/ast/seq/seq_power_facet.h:108 | bool find_power(expr* e, unsigned& idx) const {
// src: src/ast/seq/seq_power_facet.h:109 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.h:110 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.h:111 | continue;
// src: src/ast/seq/seq_power_facet.h:112 | if (m_pows[i].m_e.get() == e) {
// src: src/ast/seq/seq_power_facet.h:113 | idx = i;
// src: src/ast/seq/seq_power_facet.h:114 | return true;
// src: src/ast/seq/seq_power_facet.h:115 | }
// src: src/ast/seq/seq_power_facet.h:116 | }
// src: src/ast/seq/seq_power_facet.h:117 | return false;
// src: src/ast/seq/seq_power_facet.h:118 | }
{ if 0 <= i < |keys| then (if B(active,i) && keys[i]==tok then i else FindActive(keys,active,tok,i+1)) else -1 }
// src: src/ast/seq/seq_power_facet.cpp:27 | void power_facet::remove(unsigned idx) {
// src: src/ast/seq/seq_power_facet.cpp:28 | SASSERT(idx < m_pows.size());
// src: src/ast/seq/seq_power_facet.cpp:29 | if (!m_pows[idx].m_active)
// src: src/ast/seq/seq_power_facet.cpp:30 | return;
// src: src/ast/seq/seq_power_facet.cpp:31 | m_trail.push(vector_field_trail<str_power, bool>(m_pows, idx, &str_power::m_active));
// src: src/ast/seq/seq_power_facet.cpp:32 | m_pows[idx].m_active = false;
function Deactivate(active: seq<bool>, idx: int): seq<bool>
// src: src/ast/seq/seq_power_facet.cpp:27 | void power_facet::remove(unsigned idx) {
// src: src/ast/seq/seq_power_facet.cpp:28 | SASSERT(idx < m_pows.size());
// src: src/ast/seq/seq_power_facet.cpp:29 | if (!m_pows[idx].m_active)
// src: src/ast/seq/seq_power_facet.cpp:30 | return;
// src: src/ast/seq/seq_power_facet.cpp:31 | m_trail.push(vector_field_trail<str_power, bool>(m_pows, idx, &str_power::m_active));
// src: src/ast/seq/seq_power_facet.cpp:32 | m_pows[idx].m_active = false;
{ seq(|active|, i => B(active,i) && i!=idx) }
// src: src/ast/seq/seq_eq_facet.cpp:37 | void subst_in(expr_ref_vector& ts, expr* var, expr_ref_vector const& repl) {
// src: src/ast/seq/seq_eq_facet.cpp:38 | expr_ref_vector orig(ts);
// src: src/ast/seq/seq_eq_facet.cpp:39 | ts.reset();
// src: src/ast/seq/seq_eq_facet.cpp:40 | for (unsigned i = 0; i < orig.size(); ++i) {
// src: src/ast/seq/seq_eq_facet.cpp:41 | if (orig.get(i) == var)
// src: src/ast/seq/seq_eq_facet.cpp:42 | ts.append(repl);
// src: src/ast/seq/seq_eq_facet.cpp:43 | else
// src: src/ast/seq/seq_eq_facet.cpp:44 | ts.push_back(orig.get(i));
// src: src/ast/seq/seq_eq_facet.cpp:45 | }
function Substitute(ts: seq<int>, tok: int, repl: seq<int>): seq<int>
// synth: specification, checked annotation, or structural delimiter
  decreases |ts|
// src: src/ast/seq/seq_eq_facet.cpp:37 | void subst_in(expr_ref_vector& ts, expr* var, expr_ref_vector const& repl) {
// src: src/ast/seq/seq_eq_facet.cpp:38 | expr_ref_vector orig(ts);
// src: src/ast/seq/seq_eq_facet.cpp:39 | ts.reset();
// src: src/ast/seq/seq_eq_facet.cpp:40 | for (unsigned i = 0; i < orig.size(); ++i) {
// src: src/ast/seq/seq_eq_facet.cpp:41 | if (orig.get(i) == var)
// src: src/ast/seq/seq_eq_facet.cpp:42 | ts.append(repl);
// src: src/ast/seq/seq_eq_facet.cpp:43 | else
// src: src/ast/seq/seq_eq_facet.cpp:44 | ts.push_back(orig.get(i));
// src: src/ast/seq/seq_eq_facet.cpp:45 | }
{ if |ts|==0 then [] else (if ts[0]==tok then repl else [ts[0]])+Substitute(ts[1..],tok,repl) }
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
function Register(repl: seq<int>, sp: seq<bool>, sw: seq<int>, si: seq<int>, se: seq<int>, state: (seq<int>,seq<seq<int>>,seq<bool>,seq<int>,seq<int>,seq<int>)): (seq<int>,seq<seq<int>>,seq<bool>,seq<int>,seq<int>,seq<int>)
// synth: specification, checked annotation, or structural delimiter
  decreases |repl|
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
  if |repl|==0 then state else
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
  var t := repl[0];
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
  var add := B(sp,t) && FindActive(state.0,state.2,t,0)<0;
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
  var ns := if add then (state.0+[t],state.1+[R(Rows(sw,si),t)],state.2+[true],state.3+[I(se,t)],state.4+[0],state.5+[0]) else state;
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
  Register(repl[1..],sp,sw,si,se,ns)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
function Rebase(rows: seq<seq<int>>, active: seq<bool>, tok: int, repl: seq<int>): seq<seq<int>>
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
{ seq(|rows|, i => if B(active,i) && tok in R(rows,i) then Substitute(R(rows,i),tok,repl) else R(rows,i)) }
// src: src/ast/seq/seq_power_facet.cpp:43 | void power_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker) {
// src: src/ast/seq/seq_power_facet.cpp:44 | unsigned idx;
// src: src/ast/seq/seq_power_facet.cpp:45 | if (find_power(var, idx))
// src: src/ast/seq/seq_power_facet.cpp:46 | remove(idx);
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
// src: src/ast/seq/seq_power_facet.cpp:61 | }
function PowerExpected(sp: seq<bool>, sw: seq<int>, si: seq<int>, se: seq<int>, keys: seq<int>, rows: seq<seq<int>>, active: seq<bool>, exps: seq<int>, deps: seq<int>, flags: seq<int>, tok: int, repl: seq<int>): (seq<int>,seq<seq<int>>,seq<bool>,seq<int>,seq<int>,seq<int>)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:43 | void power_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker) {
// src: src/ast/seq/seq_power_facet.cpp:44 | unsigned idx;
// src: src/ast/seq/seq_power_facet.cpp:45 | if (find_power(var, idx))
// src: src/ast/seq/seq_power_facet.cpp:46 | remove(idx);
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
// src: src/ast/seq/seq_power_facet.cpp:61 | }
  var state := Register(repl,sp,sw,si,se,(keys,rows,Deactivate(active,FindActive(keys,active,tok,0)),exps,deps,flags));
// src: src/ast/seq/seq_power_facet.cpp:43 | void power_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker) {
// src: src/ast/seq/seq_power_facet.cpp:44 | unsigned idx;
// src: src/ast/seq/seq_power_facet.cpp:45 | if (find_power(var, idx))
// src: src/ast/seq/seq_power_facet.cpp:46 | remove(idx);
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
// src: src/ast/seq/seq_power_facet.cpp:61 | }
  (state.0,Rebase(state.1,state.2,tok,repl),state.2,state.3,state.4,state.5)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
ghost predicate Edge(keys: seq<int>, rows: seq<seq<int>>, active: seq<bool>, a: int, b: int)
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
{ exists j :: 0 <= j < |keys| && B(active,j) && keys[j]==a && b in R(rows,j) }
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
ghost predicate CurrentBaseAcyclic(keys: seq<int>, rows: seq<seq<int>>, active: seq<bool>)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
  !(exists cycle: seq<int> :: |cycle|>1 && cycle[0]==cycle[|cycle|-1] && (forall j :: 0 <= j < |cycle|-1 ==> Edge(keys,rows,active,cycle[j],cycle[j+1])))
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
// src: src/ast/seq/seq_power_facet.h:103 | vector<str_power> const& powers() const { return m_pows; }
// src: src/ast/seq/seq_power_facet.h:104 | 
// src: src/ast/seq/seq_power_facet.h:105 | // Locate the pending obligation whose power term is `e`. Plugins use
// src: src/ast/seq/seq_power_facet.h:106 | // this to recover the base, exponent, and dependency of an opaque
// src: src/ast/seq/seq_power_facet.h:107 | // `seq.power` token inside an equation.
// src: src/ast/seq/seq_power_facet.h:108 | bool find_power(expr* e, unsigned& idx) const {
// src: src/ast/seq/seq_power_facet.h:109 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.h:110 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.h:111 | continue;
// src: src/ast/seq/seq_power_facet.h:112 | if (m_pows[i].m_e.get() == e) {
// src: src/ast/seq/seq_power_facet.h:113 | idx = i;
// src: src/ast/seq/seq_power_facet.h:114 | return true;
// src: src/ast/seq/seq_power_facet.h:115 | }
// src: src/ast/seq/seq_power_facet.h:116 | }
// src: src/ast/seq/seq_power_facet.h:117 | return false;
// src: src/ast/seq/seq_power_facet.h:118 | }
ghost predicate PowerStateWellFormed(sp: seq<bool>, se: seq<int>, keys: seq<int>, rows: seq<seq<int>>, active: seq<bool>, exps: seq<int>, deps: seq<int>, flags: seq<int>)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
// src: src/ast/seq/seq_power_facet.h:103 | vector<str_power> const& powers() const { return m_pows; }
// src: src/ast/seq/seq_power_facet.h:104 | 
// src: src/ast/seq/seq_power_facet.h:105 | // Locate the pending obligation whose power term is `e`. Plugins use
// src: src/ast/seq/seq_power_facet.h:106 | // this to recover the base, exponent, and dependency of an opaque
// src: src/ast/seq/seq_power_facet.h:107 | // `seq.power` token inside an equation.
// src: src/ast/seq/seq_power_facet.h:108 | bool find_power(expr* e, unsigned& idx) const {
// src: src/ast/seq/seq_power_facet.h:109 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.h:110 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.h:111 | continue;
// src: src/ast/seq/seq_power_facet.h:112 | if (m_pows[i].m_e.get() == e) {
// src: src/ast/seq/seq_power_facet.h:113 | idx = i;
// src: src/ast/seq/seq_power_facet.h:114 | return true;
// src: src/ast/seq/seq_power_facet.h:115 | }
// src: src/ast/seq/seq_power_facet.h:116 | }
// src: src/ast/seq/seq_power_facet.h:117 | return false;
// src: src/ast/seq/seq_power_facet.h:118 | }
  |se|==|sp| && |rows|==|keys|==|active|==|exps|==|deps|==|flags| &&
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
// src: src/ast/seq/seq_power_facet.h:103 | vector<str_power> const& powers() const { return m_pows; }
// src: src/ast/seq/seq_power_facet.h:104 | 
// src: src/ast/seq/seq_power_facet.h:105 | // Locate the pending obligation whose power term is `e`. Plugins use
// src: src/ast/seq/seq_power_facet.h:106 | // this to recover the base, exponent, and dependency of an opaque
// src: src/ast/seq/seq_power_facet.h:107 | // `seq.power` token inside an equation.
// src: src/ast/seq/seq_power_facet.h:108 | bool find_power(expr* e, unsigned& idx) const {
// src: src/ast/seq/seq_power_facet.h:109 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.h:110 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.h:111 | continue;
// src: src/ast/seq/seq_power_facet.h:112 | if (m_pows[i].m_e.get() == e) {
// src: src/ast/seq/seq_power_facet.h:113 | idx = i;
// src: src/ast/seq/seq_power_facet.h:114 | return true;
// src: src/ast/seq/seq_power_facet.h:115 | }
// src: src/ast/seq/seq_power_facet.h:116 | }
// src: src/ast/seq/seq_power_facet.h:117 | return false;
// src: src/ast/seq/seq_power_facet.h:118 | }
  (forall j :: 0 <= j < |keys| ==> 0 <= keys[j] < |sp| && B(sp,keys[j]) && exps[j]==I(se,keys[j]) && deps[j]>=0 && 0<=flags[j]<4 && (forall t :: t in rows[j] ==> 0<=t<|sp|)) &&
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
// src: src/ast/seq/seq_power_facet.h:103 | vector<str_power> const& powers() const { return m_pows; }
// src: src/ast/seq/seq_power_facet.h:104 | 
// src: src/ast/seq/seq_power_facet.h:105 | // Locate the pending obligation whose power term is `e`. Plugins use
// src: src/ast/seq/seq_power_facet.h:106 | // this to recover the base, exponent, and dependency of an opaque
// src: src/ast/seq/seq_power_facet.h:107 | // `seq.power` token inside an equation.
// src: src/ast/seq/seq_power_facet.h:108 | bool find_power(expr* e, unsigned& idx) const {
// src: src/ast/seq/seq_power_facet.h:109 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.h:110 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.h:111 | continue;
// src: src/ast/seq/seq_power_facet.h:112 | if (m_pows[i].m_e.get() == e) {
// src: src/ast/seq/seq_power_facet.h:113 | idx = i;
// src: src/ast/seq/seq_power_facet.h:114 | return true;
// src: src/ast/seq/seq_power_facet.h:115 | }
// src: src/ast/seq/seq_power_facet.h:116 | }
// src: src/ast/seq/seq_power_facet.h:117 | return false;
// src: src/ast/seq/seq_power_facet.h:118 | }
  (forall j,k :: 0<=j<k<|keys| && active[j] && active[k] ==> keys[j]!=keys[k])
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
ghost predicate Catalog(sp: seq<bool>, sw: seq<int>, si: seq<int>, se: seq<int>)
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
  |sw|==|se|==|sp| && Partition(sw,si) && (forall t :: t in si ==> 0<=t<|sp|) &&
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
  (forall j :: 0<=j<|sp| && !sp[j] ==> sw[j]==0) && CurrentBaseAcyclic(seq(|sp|,i=>i),Rows(sw,si),sp)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:43 | void power_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker) {
// src: src/ast/seq/seq_power_facet.cpp:44 | unsigned idx;
// src: src/ast/seq/seq_power_facet.cpp:45 | if (find_power(var, idx))
// src: src/ast/seq/seq_power_facet.cpp:46 | remove(idx);
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
// src: src/ast/seq/seq_power_facet.cpp:61 | }
ghost predicate PowerUpdateExact(sp: seq<bool>, sw: seq<int>, si: seq<int>, se: seq<int>, keys: seq<int>, rows: seq<seq<int>>, active: seq<bool>, exps: seq<int>, deps: seq<int>, flags: seq<int>, tok: int, repl: seq<int>, ko: seq<int>, wo: seq<int>, io: seq<int>, ao: seq<bool>, eo: seq<int>, depso: seq<int>, fo: seq<int>)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:43 | void power_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker) {
// src: src/ast/seq/seq_power_facet.cpp:44 | unsigned idx;
// src: src/ast/seq/seq_power_facet.cpp:45 | if (find_power(var, idx))
// src: src/ast/seq/seq_power_facet.cpp:46 | remove(idx);
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
// src: src/ast/seq/seq_power_facet.cpp:61 | }
  var expected := PowerExpected(sp,sw,si,se,keys,rows,active,exps,deps,flags,tok,repl);
// src: src/ast/seq/seq_power_facet.cpp:43 | void power_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker) {
// src: src/ast/seq/seq_power_facet.cpp:44 | unsigned idx;
// src: src/ast/seq/seq_power_facet.cpp:45 | if (find_power(var, idx))
// src: src/ast/seq/seq_power_facet.cpp:46 | remove(idx);
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
// src: src/ast/seq/seq_power_facet.cpp:61 | }
  (ko,Rows(wo,io),ao,eo,depso,fo)==expected && Partition(wo,io)
// synth: specification, checked annotation, or structural delimiter
}
// src: src/ast/seq/seq_power_facet.cpp:43 | void power_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker) {
// src: src/ast/seq/seq_power_facet.cpp:44 | unsigned idx;
// src: src/ast/seq/seq_power_facet.cpp:45 | if (find_power(var, idx))
// src: src/ast/seq/seq_power_facet.cpp:46 | remove(idx);
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
// src: src/ast/seq/seq_power_facet.cpp:61 | }
method PowerSubstitutionEntry(syntaxPower: seq<bool>, syntaxWidths: seq<int>, syntaxItems: seq<int>, syntaxExps: seq<int>, keys: seq<int>, widths: seq<int>, items: seq<int>, active: seq<bool>, exps: seq<int>, deps: seq<int>, flags: seq<int>, fromTok: int, repl: seq<int>, substDep: int) returns (keysOut: seq<int>, widthsOut: seq<int>, itemsOut: seq<int>, activeOut: seq<bool>, expsOut: seq<int>, depsOut: seq<int>, flagsOut: seq<int>)
// synth: specification, checked annotation, or structural delimiter
  requires Catalog(syntaxPower,syntaxWidths,syntaxItems,syntaxExps)
// synth: specification, checked annotation, or structural delimiter
  requires Partition(widths,items) && PowerStateWellFormed(syntaxPower,syntaxExps,keys,Rows(widths,items),active,exps,deps,flags)
// synth: specification, checked annotation, or structural delimiter
  requires 0<=fromTok<|syntaxPower| && (forall t :: t in repl ==> 0<=t<|syntaxPower|) && substDep>=0
// synth: specification, checked annotation, or structural delimiter
  requires |keys|+|repl|<4294967296 && (forall n :: n in widths+syntaxWidths ==> 0<=n<4294967296) && (forall r :: r in Rows(widths,items)+Rows(syntaxWidths,syntaxItems) ==> |Substitute(r,fromTok,repl)|<4294967296)
// synth: specification, checked annotation, or structural delimiter
  ensures Partition(widthsOut,itemsOut) && PowerStateWellFormed(syntaxPower,syntaxExps,keysOut,Rows(widthsOut,itemsOut),activeOut,expsOut,depsOut,flagsOut)
// synth: specification, checked annotation, or structural delimiter
  ensures PowerUpdateExact(syntaxPower,syntaxWidths,syntaxItems,syntaxExps,keys,Rows(widths,items),active,exps,deps,flags,fromTok,repl,keysOut,widthsOut,itemsOut,activeOut,expsOut,depsOut,flagsOut)
// synth: specification, checked annotation, or structural delimiter
  ensures CurrentBaseAcyclic(keys,Rows(widths,items),active) ==> CurrentBaseAcyclic(keysOut,Rows(widthsOut,itemsOut),activeOut)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/ast/seq/seq_power_facet.cpp:44 | unsigned idx;
// src: src/ast/seq/seq_power_facet.cpp:45 | if (find_power(var, idx))
// src: src/ast/seq/seq_power_facet.cpp:46 | remove(idx);
  var idx := FindActive(keys,active,fromTok,0);
// src: src/ast/seq/seq_power_facet.cpp:44 | unsigned idx;
// src: src/ast/seq/seq_power_facet.cpp:45 | if (find_power(var, idx))
// src: src/ast/seq/seq_power_facet.cpp:46 | remove(idx);
  var ko, bases, ao, eo, de, fl := keys, Rows(widths,items), Deactivate(active,idx), exps, deps, flags;
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
  var j := 0;
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
  while j < |repl|
// synth: specification, checked annotation, or structural delimiter
    invariant 0<=j<=|repl|
// synth: specification, checked annotation, or structural delimiter
    decreases |repl|-j
// synth: specification, checked annotation, or structural delimiter
  {
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
    var t := repl[j];
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
    if B(syntaxPower,t) && FindActive(ko,ao,t,0)<0 {
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
      ko := ko+[t];
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
      bases := bases+[R(Rows(syntaxWidths,syntaxItems),t)];
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
      ao := ao+[true];
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
      eo := eo+[I(syntaxExps,t)];
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
      de := de+[0];
// src: src/ast/seq/seq_power_facet.h:86 | void add_power(expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:87 | unsigned idx;
// src: src/ast/seq/seq_power_facet.h:88 | if (find_power(e, idx))
// src: src/ast/seq/seq_power_facet.h:89 | return;
// src: src/ast/seq/seq_power_facet.h:90 | m_pows.push_back(str_power(m, e, s, n, dep));
// src: src/ast/seq/seq_power_facet.h:91 | m_trail.push(push_back_trail<str_power>(m_pows));
// src: src/ast/seq/seq_power_facet.h:92 | }
// src: src/ast/seq/seq_power_facet.h:93 | // Register `e` if it is a `seq.power` term (`e = s^n`); no-op
// src: src/ast/seq/seq_power_facet.h:94 | // otherwise. Convenience wrapper for callers scanning terms.
// src: src/ast/seq/seq_power_facet.h:95 | bool add_power_if(expr* e, eq_tree::dep_tracker dep = nullptr) {
// src: src/ast/seq/seq_power_facet.h:96 | expr* s = nullptr, *n = nullptr;
// src: src/ast/seq/seq_power_facet.h:97 | if (!u.str.is_power(e, s, n))
// src: src/ast/seq/seq_power_facet.h:98 | return false;
// src: src/ast/seq/seq_power_facet.h:99 | add_power(e, s, n, dep);
// src: src/ast/seq/seq_power_facet.h:100 | return true;
// src: src/ast/seq/seq_power_facet.h:101 | }
// src: src/ast/seq/seq_power_facet.h:102 | 
// src: src/ast/seq/seq_power_facet.h:38 | struct str_power {
// src: src/ast/seq/seq_power_facet.h:39 | expr_ref             m_e;
// src: src/ast/seq/seq_power_facet.h:40 | expr_ref             m_s;
// src: src/ast/seq/seq_power_facet.h:41 | expr_ref             m_n;
// src: src/ast/seq/seq_power_facet.h:42 | eq_tree::dep_tracker  m_dep;
// src: src/ast/seq/seq_power_facet.h:43 | // Set once this obligation's length axioms have
// src: src/ast/seq/seq_power_facet.h:44 | // been asserted into `solver_facet`.
// src: src/ast/seq/seq_power_facet.h:45 | bool                 m_axiomatized = false;
// src: src/ast/seq/seq_power_facet.h:46 | 
// src: src/ast/seq/seq_power_facet.h:47 | // power_split has taken its residual `n > bound` branch: the obligation stays
// src: src/ast/seq/seq_power_facet.h:48 | // pending for the other rules, power_split does not re-enumerate it. Trailed.
// src: src/ast/seq/seq_power_facet.h:49 | bool                 m_split_exhausted = false;
// src: src/ast/seq/seq_power_facet.h:50 | 
// src: src/ast/seq/seq_power_facet.h:51 | // Append-only representation: removing an obligation just flips
// src: src/ast/seq/seq_power_facet.h:52 | // `m_active`, so stored indices remain valid across iterator
// src: src/ast/seq/seq_power_facet.h:53 | // resumptions. Consumers must skip inactive entries.
// src: src/ast/seq/seq_power_facet.h:54 | bool                 m_active = true;
// src: src/ast/seq/seq_power_facet.h:55 | 
// src: src/ast/seq/seq_power_facet.h:56 | str_power(ast_manager& m, expr* e, expr* s, expr* n, eq_tree::dep_tracker dep = nullptr) :
// src: src/ast/seq/seq_power_facet.h:57 | m_e(e, m), m_s(s, m), m_n(n, m), m_dep(dep) {}
// src: src/ast/seq/seq_power_facet.h:58 | bool active() const { return m_active; }
// src: src/ast/seq/seq_power_facet.h:59 | };
// src: src/ast/seq/seq_power_facet.h:60 | 
// src: src/ast/seq/seq_power_facet.h:61 | /**
      fl := fl+[0];
// synth: specification, checked annotation, or structural delimiter
    }
// src: src/ast/seq/seq_power_facet.cpp:47 | for (expr* t : repl)
// src: src/ast/seq/seq_power_facet.cpp:48 | add_power_if(t);
    j := j+1;
// synth: specification, checked annotation, or structural delimiter
  }
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
  bases := Rebase(bases,ao,fromTok,repl);
// src: src/ast/seq/seq_power_facet.cpp:49 | // rebase obligations whose base mentions var; the power token keeps its identity
// src: src/ast/seq/seq_power_facet.cpp:50 | for (unsigned i = 0; i < m_pows.size(); ++i) {
// src: src/ast/seq/seq_power_facet.cpp:51 | if (!m_pows[i].active())
// src: src/ast/seq/seq_power_facet.cpp:52 | continue;
// src: src/ast/seq/seq_power_facet.cpp:53 | expr_ref_vector base(m);
// src: src/ast/seq/seq_power_facet.cpp:54 | u.str.get_concat_units(m_pows[i].m_s.get(), base);
// src: src/ast/seq/seq_power_facet.cpp:55 | if (!base.contains(var))
// src: src/ast/seq/seq_power_facet.cpp:56 | continue;
// src: src/ast/seq/seq_power_facet.cpp:57 | subst_in(base, var, repl);
// src: src/ast/seq/seq_power_facet.cpp:58 | m_trail.push(vector_field_trail<str_power, expr_ref>(m_pows, i, &str_power::m_s));
// src: src/ast/seq/seq_power_facet.cpp:59 | m_pows[i].m_s = u.str.mk_concat(base, m_pows[i].m_e->get_sort());
// src: src/ast/seq/seq_power_facet.cpp:60 | }
  keysOut, widthsOut, itemsOut, activeOut, expsOut, depsOut, flagsOut := ko, Widths(bases), Flat(bases), ao, eo, de, fl;
// synth: specification, checked annotation, or structural delimiter
}
