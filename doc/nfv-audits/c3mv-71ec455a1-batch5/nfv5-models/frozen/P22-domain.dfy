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

// src: src/util/stx_search_tree.h:579 | struct ptr_hash {
// src: src/util/stx_search_tree.h:580 | unsigned operator()(constraint_i* c) const { return static_cast<unsigned>(c->hash()); }
// src: src/util/stx_search_tree.h:581 | };
// src: src/util/stx_search_tree.h:582 | struct ptr_eq {
// src: src/util/stx_search_tree.h:583 | bool operator()(constraint_i* a, constraint_i* b) const { return a == b || a->equals(*b); }
// src: src/util/stx_search_tree.h:584 | };
// src: src/util/stx_search_tree.h:585 | hashtable<constraint_i*, ptr_hash, ptr_eq> m_ids;
// src: src/util/stx_search_tree.h:586 | scoped_ptr_vector<constraint_i>            m_owned; // id -> owned canonical clone
// src: src/util/stx_search_tree.h:587 | public:
// src: src/util/stx_search_tree.h:588 | void clear() { m_ids.reset(); m_owned.reset(); }
// src: src/util/stx_search_tree.h:589 | void init(vector<constraint_i const*> const& cs) {
// src: src/util/stx_search_tree.h:590 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:591 | intern(*c);
// src: src/util/stx_search_tree.h:592 | }
// src: src/util/stx_search_tree.h:593 | bool find(constraint_i const& c, unsigned& id) const {
// src: src/util/stx_search_tree.h:594 | constraint_i* key = const_cast<constraint_i*>(&c);
// src: src/util/stx_search_tree.h:595 | constraint_i* found = nullptr;
// src: src/util/stx_search_tree.h:596 | if (!m_ids.find(key, found))
// src: src/util/stx_search_tree.h:597 | return false;
// src: src/util/stx_search_tree.h:598 | id = found->store_id();
// src: src/util/stx_search_tree.h:599 | return true;
function FindIntern(owned: seq<int>, values: seq<int>, hashes: seq<int>, query: int, i: int): int
// synth: specification, checked annotation, or structural delimiter
  decreases |owned|-i
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:579 | struct ptr_hash {
// src: src/util/stx_search_tree.h:580 | unsigned operator()(constraint_i* c) const { return static_cast<unsigned>(c->hash()); }
// src: src/util/stx_search_tree.h:581 | };
// src: src/util/stx_search_tree.h:582 | struct ptr_eq {
// src: src/util/stx_search_tree.h:583 | bool operator()(constraint_i* a, constraint_i* b) const { return a == b || a->equals(*b); }
// src: src/util/stx_search_tree.h:584 | };
// src: src/util/stx_search_tree.h:585 | hashtable<constraint_i*, ptr_hash, ptr_eq> m_ids;
// src: src/util/stx_search_tree.h:586 | scoped_ptr_vector<constraint_i>            m_owned; // id -> owned canonical clone
// src: src/util/stx_search_tree.h:587 | public:
// src: src/util/stx_search_tree.h:588 | void clear() { m_ids.reset(); m_owned.reset(); }
// src: src/util/stx_search_tree.h:589 | void init(vector<constraint_i const*> const& cs) {
// src: src/util/stx_search_tree.h:590 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:591 | intern(*c);
// src: src/util/stx_search_tree.h:592 | }
// src: src/util/stx_search_tree.h:593 | bool find(constraint_i const& c, unsigned& id) const {
// src: src/util/stx_search_tree.h:594 | constraint_i* key = const_cast<constraint_i*>(&c);
// src: src/util/stx_search_tree.h:595 | constraint_i* found = nullptr;
// src: src/util/stx_search_tree.h:596 | if (!m_ids.find(key, found))
// src: src/util/stx_search_tree.h:597 | return false;
// src: src/util/stx_search_tree.h:598 | id = found->store_id();
// src: src/util/stx_search_tree.h:599 | return true;
  if 0<=i<|owned| then (if I(hashes,owned[i])%4294967296==I(hashes,query)%4294967296 && I(values,owned[i])==I(values,query) then i else FindIntern(owned,values,hashes,query,i+1)) else -1
// synth: specification, checked annotation, or structural delimiter
}
// src: src/util/stx_search_tree.h:577 | // lookups keyed by a transient, facet-owned pointer match
// src: src/util/stx_search_tree.h:578 | // buckets keyed by this store's own permanent clones.
// src: src/util/stx_search_tree.h:579 | struct ptr_hash {
// src: src/util/stx_search_tree.h:580 | unsigned operator()(constraint_i* c) const { return static_cast<unsigned>(c->hash()); }
// src: src/util/stx_search_tree.h:581 | };
// src: src/util/stx_search_tree.h:582 | struct ptr_eq {
// src: src/util/stx_search_tree.h:583 | bool operator()(constraint_i* a, constraint_i* b) const { return a == b || a->equals(*b); }
// src: src/util/stx_search_tree.h:584 | };
// src: src/util/stx_search_tree.h:585 | hashtable<constraint_i*, ptr_hash, ptr_eq> m_ids;
// src: src/util/stx_search_tree.h:586 | scoped_ptr_vector<constraint_i>            m_owned; // id -> owned canonical clone
// src: src/util/stx_search_tree.h:587 | public:
// src: src/util/stx_search_tree.h:588 | void clear() { m_ids.reset(); m_owned.reset(); }
// src: src/util/stx_search_tree.h:589 | void init(vector<constraint_i const*> const& cs) {
// src: src/util/stx_search_tree.h:590 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:591 | intern(*c);
// src: src/util/stx_search_tree.h:592 | }
// src: src/util/stx_search_tree.h:593 | bool find(constraint_i const& c, unsigned& id) const {
// src: src/util/stx_search_tree.h:594 | constraint_i* key = const_cast<constraint_i*>(&c);
// src: src/util/stx_search_tree.h:595 | constraint_i* found = nullptr;
// src: src/util/stx_search_tree.h:596 | if (!m_ids.find(key, found))
// src: src/util/stx_search_tree.h:597 | return false;
// src: src/util/stx_search_tree.h:598 | id = found->store_id();
// src: src/util/stx_search_tree.h:599 | return true;
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
ghost predicate CanonicalStoreWellFormed(owned: seq<int>, values: seq<int>, hashes: seq<int>, ids: seq<int>)
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:577 | // lookups keyed by a transient, facet-owned pointer match
// src: src/util/stx_search_tree.h:578 | // buckets keyed by this store's own permanent clones.
// src: src/util/stx_search_tree.h:579 | struct ptr_hash {
// src: src/util/stx_search_tree.h:580 | unsigned operator()(constraint_i* c) const { return static_cast<unsigned>(c->hash()); }
// src: src/util/stx_search_tree.h:581 | };
// src: src/util/stx_search_tree.h:582 | struct ptr_eq {
// src: src/util/stx_search_tree.h:583 | bool operator()(constraint_i* a, constraint_i* b) const { return a == b || a->equals(*b); }
// src: src/util/stx_search_tree.h:584 | };
// src: src/util/stx_search_tree.h:585 | hashtable<constraint_i*, ptr_hash, ptr_eq> m_ids;
// src: src/util/stx_search_tree.h:586 | scoped_ptr_vector<constraint_i>            m_owned; // id -> owned canonical clone
// src: src/util/stx_search_tree.h:587 | public:
// src: src/util/stx_search_tree.h:588 | void clear() { m_ids.reset(); m_owned.reset(); }
// src: src/util/stx_search_tree.h:589 | void init(vector<constraint_i const*> const& cs) {
// src: src/util/stx_search_tree.h:590 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:591 | intern(*c);
// src: src/util/stx_search_tree.h:592 | }
// src: src/util/stx_search_tree.h:593 | bool find(constraint_i const& c, unsigned& id) const {
// src: src/util/stx_search_tree.h:594 | constraint_i* key = const_cast<constraint_i*>(&c);
// src: src/util/stx_search_tree.h:595 | constraint_i* found = nullptr;
// src: src/util/stx_search_tree.h:596 | if (!m_ids.find(key, found))
// src: src/util/stx_search_tree.h:597 | return false;
// src: src/util/stx_search_tree.h:598 | id = found->store_id();
// src: src/util/stx_search_tree.h:599 | return true;
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
  |values|==|hashes|==|ids| && Unique(owned) &&
// src: src/util/stx_search_tree.h:577 | // lookups keyed by a transient, facet-owned pointer match
// src: src/util/stx_search_tree.h:578 | // buckets keyed by this store's own permanent clones.
// src: src/util/stx_search_tree.h:579 | struct ptr_hash {
// src: src/util/stx_search_tree.h:580 | unsigned operator()(constraint_i* c) const { return static_cast<unsigned>(c->hash()); }
// src: src/util/stx_search_tree.h:581 | };
// src: src/util/stx_search_tree.h:582 | struct ptr_eq {
// src: src/util/stx_search_tree.h:583 | bool operator()(constraint_i* a, constraint_i* b) const { return a == b || a->equals(*b); }
// src: src/util/stx_search_tree.h:584 | };
// src: src/util/stx_search_tree.h:585 | hashtable<constraint_i*, ptr_hash, ptr_eq> m_ids;
// src: src/util/stx_search_tree.h:586 | scoped_ptr_vector<constraint_i>            m_owned; // id -> owned canonical clone
// src: src/util/stx_search_tree.h:587 | public:
// src: src/util/stx_search_tree.h:588 | void clear() { m_ids.reset(); m_owned.reset(); }
// src: src/util/stx_search_tree.h:589 | void init(vector<constraint_i const*> const& cs) {
// src: src/util/stx_search_tree.h:590 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:591 | intern(*c);
// src: src/util/stx_search_tree.h:592 | }
// src: src/util/stx_search_tree.h:593 | bool find(constraint_i const& c, unsigned& id) const {
// src: src/util/stx_search_tree.h:594 | constraint_i* key = const_cast<constraint_i*>(&c);
// src: src/util/stx_search_tree.h:595 | constraint_i* found = nullptr;
// src: src/util/stx_search_tree.h:596 | if (!m_ids.find(key, found))
// src: src/util/stx_search_tree.h:597 | return false;
// src: src/util/stx_search_tree.h:598 | id = found->store_id();
// src: src/util/stx_search_tree.h:599 | return true;
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
  (forall j :: 0<=j<|owned| ==> 0<=owned[j]<|values| && I(ids,owned[j])==j) &&
// src: src/util/stx_search_tree.h:577 | // lookups keyed by a transient, facet-owned pointer match
// src: src/util/stx_search_tree.h:578 | // buckets keyed by this store's own permanent clones.
// src: src/util/stx_search_tree.h:579 | struct ptr_hash {
// src: src/util/stx_search_tree.h:580 | unsigned operator()(constraint_i* c) const { return static_cast<unsigned>(c->hash()); }
// src: src/util/stx_search_tree.h:581 | };
// src: src/util/stx_search_tree.h:582 | struct ptr_eq {
// src: src/util/stx_search_tree.h:583 | bool operator()(constraint_i* a, constraint_i* b) const { return a == b || a->equals(*b); }
// src: src/util/stx_search_tree.h:584 | };
// src: src/util/stx_search_tree.h:585 | hashtable<constraint_i*, ptr_hash, ptr_eq> m_ids;
// src: src/util/stx_search_tree.h:586 | scoped_ptr_vector<constraint_i>            m_owned; // id -> owned canonical clone
// src: src/util/stx_search_tree.h:587 | public:
// src: src/util/stx_search_tree.h:588 | void clear() { m_ids.reset(); m_owned.reset(); }
// src: src/util/stx_search_tree.h:589 | void init(vector<constraint_i const*> const& cs) {
// src: src/util/stx_search_tree.h:590 | for (constraint_i const* c : cs)
// src: src/util/stx_search_tree.h:591 | intern(*c);
// src: src/util/stx_search_tree.h:592 | }
// src: src/util/stx_search_tree.h:593 | bool find(constraint_i const& c, unsigned& id) const {
// src: src/util/stx_search_tree.h:594 | constraint_i* key = const_cast<constraint_i*>(&c);
// src: src/util/stx_search_tree.h:595 | constraint_i* found = nullptr;
// src: src/util/stx_search_tree.h:596 | if (!m_ids.find(key, found))
// src: src/util/stx_search_tree.h:597 | return false;
// src: src/util/stx_search_tree.h:598 | id = found->store_id();
// src: src/util/stx_search_tree.h:599 | return true;
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
  (forall j,k :: 0<=j<k<|owned| ==> I(values,owned[j])!=I(values,owned[k]))
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
ghost predicate InternTransitionExact(query: int, owned: seq<int>, values: seq<int>, hashes: seq<int>, ids: seq<int>, id: int, oo: seq<int>, vo: seq<int>, ho: seq<int>, io: seq<int>)
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
  var found := FindIntern(owned,values,hashes,query,0);
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
  if found>=0 then id==I(ids,I(owned,found)) && (oo,vo,ho,io)==(owned,values,hashes,ids)
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
  else id==|owned| && (oo,vo,ho,io)==(owned+[|values|],values+[I(values,query)],hashes+[I(hashes,query)],ids+[|owned|])
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
ghost predicate CanonicalClassPreserved(query: int, owned: seq<int>, values: seq<int>, id: int, oo: seq<int>, vo: seq<int>)
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
  0<=id<|oo| && I(vo,I(oo,id))==I(values,query) &&
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
  (forall j :: 0<=j<|owned| ==> j<|oo| && oo[j]==owned[j] && I(vo,oo[j])==I(values,owned[j]))
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
method CanonicalInternEntry(query: int, owned: seq<int>, heapValues: seq<int>, heapHashes: seq<int>, heapIds: seq<int>) returns (id: int, ownedOut: seq<int>, valuesOut: seq<int>, hashesOut: seq<int>, idsOut: seq<int>)
// synth: specification, checked annotation, or structural delimiter
  requires CanonicalStoreWellFormed(owned,heapValues,heapHashes,heapIds) && 0<=query<|heapValues|
// synth: specification, checked annotation, or structural delimiter
  requires (forall j :: 0<=j<|heapHashes| ==> 0<=heapHashes[j]<18446744073709551616 && 0<=heapIds[j]<4294967296)
// synth: specification, checked annotation, or structural delimiter
  requires (forall j,k :: 0<=j<|heapValues| && 0<=k<|heapValues| && heapValues[j]==heapValues[k] ==> heapHashes[j]%4294967296==heapHashes[k]%4294967296) && |owned|+1<4294967296
// synth: specification, checked annotation, or structural delimiter
// synth: specification, checked annotation, or structural delimiter
// synth: specification, checked annotation, or structural delimiter
// synth: specification, checked annotation, or structural delimiter
{
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
  ownedOut,valuesOut,hashesOut,idsOut := owned,heapValues,heapHashes,heapIds;
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
  var found := FindIntern(owned,heapValues,heapHashes,query,0);
// src: src/util/stx_search_tree.h:602 | unsigned id;
// src: src/util/stx_search_tree.h:603 | if (find(c, id))
// src: src/util/stx_search_tree.h:604 | return id;
  if found>=0 { id := I(heapIds,I(owned,found)); return; }
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:122 | unsigned m_store_id = UINT_MAX; // index assigned by constraint_store::intern(), once interned
// src: src/util/stx_search_tree.h:123 | public:
// src: src/util/stx_search_tree.h:124 | virtual ~constraint_i() = default;
// src: src/util/stx_search_tree.h:125 | virtual uint64_t hash() const = 0;
// src: src/util/stx_search_tree.h:126 | virtual bool equals(constraint_i const& other) const = 0;
// src: src/util/stx_search_tree.h:127 | virtual constraint_i* clone() const = 0;
// src: src/util/stx_search_tree.h:128 | 
// src: src/util/stx_search_tree.h:129 | unsigned store_id() const { return m_store_id; }
// src: src/util/stx_search_tree.h:130 | void set_store_id(unsigned id) { m_store_id = id; }
// src: src/util/stx_search_tree.h:131 | 
// src: src/util/stx_search_tree.h:132 | // Opaque pointer to this live fact's justification object
  var clone := |heapValues|;
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:122 | unsigned m_store_id = UINT_MAX; // index assigned by constraint_store::intern(), once interned
// src: src/util/stx_search_tree.h:123 | public:
// src: src/util/stx_search_tree.h:124 | virtual ~constraint_i() = default;
// src: src/util/stx_search_tree.h:125 | virtual uint64_t hash() const = 0;
// src: src/util/stx_search_tree.h:126 | virtual bool equals(constraint_i const& other) const = 0;
// src: src/util/stx_search_tree.h:127 | virtual constraint_i* clone() const = 0;
// src: src/util/stx_search_tree.h:128 | 
// src: src/util/stx_search_tree.h:129 | unsigned store_id() const { return m_store_id; }
// src: src/util/stx_search_tree.h:130 | void set_store_id(unsigned id) { m_store_id = id; }
// src: src/util/stx_search_tree.h:131 | 
// src: src/util/stx_search_tree.h:132 | // Opaque pointer to this live fact's justification object
  valuesOut := heapValues+[heapValues[query]];
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:122 | unsigned m_store_id = UINT_MAX; // index assigned by constraint_store::intern(), once interned
// src: src/util/stx_search_tree.h:123 | public:
// src: src/util/stx_search_tree.h:124 | virtual ~constraint_i() = default;
// src: src/util/stx_search_tree.h:125 | virtual uint64_t hash() const = 0;
// src: src/util/stx_search_tree.h:126 | virtual bool equals(constraint_i const& other) const = 0;
// src: src/util/stx_search_tree.h:127 | virtual constraint_i* clone() const = 0;
// src: src/util/stx_search_tree.h:128 | 
// src: src/util/stx_search_tree.h:129 | unsigned store_id() const { return m_store_id; }
// src: src/util/stx_search_tree.h:130 | void set_store_id(unsigned id) { m_store_id = id; }
// src: src/util/stx_search_tree.h:131 | 
// src: src/util/stx_search_tree.h:132 | // Opaque pointer to this live fact's justification object
  hashesOut := heapHashes+[heapHashes[query]];
// src: src/util/stx_search_tree.h:605 | constraint_i* owned = c.clone();
// src: src/util/stx_search_tree.h:122 | unsigned m_store_id = UINT_MAX; // index assigned by constraint_store::intern(), once interned
// src: src/util/stx_search_tree.h:123 | public:
// src: src/util/stx_search_tree.h:124 | virtual ~constraint_i() = default;
// src: src/util/stx_search_tree.h:125 | virtual uint64_t hash() const = 0;
// src: src/util/stx_search_tree.h:126 | virtual bool equals(constraint_i const& other) const = 0;
// src: src/util/stx_search_tree.h:127 | virtual constraint_i* clone() const = 0;
// src: src/util/stx_search_tree.h:128 | 
// src: src/util/stx_search_tree.h:129 | unsigned store_id() const { return m_store_id; }
// src: src/util/stx_search_tree.h:130 | void set_store_id(unsigned id) { m_store_id = id; }
// src: src/util/stx_search_tree.h:131 | 
// src: src/util/stx_search_tree.h:132 | // Opaque pointer to this live fact's justification object
  idsOut := heapIds+[4294967295];
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
  id := |owned|;
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
  idsOut := idsOut[clone:=id];
// src: src/util/stx_search_tree.h:606 | id = m_owned.size();
// src: src/util/stx_search_tree.h:607 | owned->set_store_id(id);
// src: src/util/stx_search_tree.h:608 | m_owned.push_back(owned);
// src: src/util/stx_search_tree.h:609 | m_ids.insert(owned);
  ownedOut := owned+[clone];
// synth: specification, checked annotation, or structural delimiter
}

// Independent domain harness 1: first-intern
method ConcreteDomain1()
{
  var query: int := 0;
  var owned: seq<int> := [];
  var heapValues: seq<int> := [7];
  var heapHashes: seq<int> := [42];
  var heapIds: seq<int> := [4294967295];
  assert CanonicalStoreWellFormed(owned,heapValues,heapHashes,heapIds) && 0<=query<|heapValues|;
  assert (forall j :: 0<=j<|heapHashes| ==> 0<=heapHashes[j]<18446744073709551616 && 0<=heapIds[j]<4294967296);
  assert (forall j,k :: 0<=j<|heapValues| && 0<=k<|heapValues| && heapValues[j]==heapValues[k] ==> heapHashes[j]%4294967296==heapHashes[k]%4294967296) && |owned|+1<4294967296;
  var out0,out1,out2,out3,out4 := CanonicalInternEntry(query,owned,heapValues,heapHashes,heapIds);
}

// Independent domain harness 2: alias-hit
method ConcreteDomain2()
{
  var query: int := 1;
  var owned: seq<int> := [0];
  var heapValues: seq<int> := [7,7];
  var heapHashes: seq<int> := [42,42];
  var heapIds: seq<int> := [0,4294967295];
  assert CanonicalStoreWellFormed(owned,heapValues,heapHashes,heapIds) && 0<=query<|heapValues|;
  assert (forall j :: 0<=j<|heapHashes| ==> 0<=heapHashes[j]<18446744073709551616 && 0<=heapIds[j]<4294967296);
  assert (forall j,k :: 0<=j<|heapValues| && 0<=k<|heapValues| && heapValues[j]==heapValues[k] ==> heapHashes[j]%4294967296==heapHashes[k]%4294967296) && |owned|+1<4294967296;
  var out0,out1,out2,out3,out4 := CanonicalInternEntry(query,owned,heapValues,heapHashes,heapIds);
}

// Independent domain harness 3: hash-collision-miss
method ConcreteDomain3()
{
  var query: int := 1;
  var owned: seq<int> := [0];
  var heapValues: seq<int> := [7,8];
  var heapHashes: seq<int> := [4294967297,1];
  var heapIds: seq<int> := [0,4294967295];
  assert CanonicalStoreWellFormed(owned,heapValues,heapHashes,heapIds) && 0<=query<|heapValues|;
  assert (forall j :: 0<=j<|heapHashes| ==> 0<=heapHashes[j]<18446744073709551616 && 0<=heapIds[j]<4294967296);
  assert (forall j,k :: 0<=j<|heapValues| && 0<=k<|heapValues| && heapValues[j]==heapValues[k] ==> heapHashes[j]%4294967296==heapHashes[k]%4294967296) && |owned|+1<4294967296;
  var out0,out1,out2,out3,out4 := CanonicalInternEntry(query,owned,heapValues,heapHashes,heapIds);
}

// Independent domain harness 4: canonical-pointer-hit
method ConcreteDomain4()
{
  var query: int := 0;
  var owned: seq<int> := [0];
  var heapValues: seq<int> := [7];
  var heapHashes: seq<int> := [42];
  var heapIds: seq<int> := [0];
  assert CanonicalStoreWellFormed(owned,heapValues,heapHashes,heapIds) && 0<=query<|heapValues|;
  assert (forall j :: 0<=j<|heapHashes| ==> 0<=heapHashes[j]<18446744073709551616 && 0<=heapIds[j]<4294967296);
  assert (forall j,k :: 0<=j<|heapValues| && 0<=k<|heapValues| && heapValues[j]==heapValues[k] ==> heapHashes[j]%4294967296==heapHashes[k]%4294967296) && |owned|+1<4294967296;
  var out0,out1,out2,out3,out4 := CanonicalInternEntry(query,owned,heapValues,heapHashes,heapIds);
}
