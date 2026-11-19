// src: src/util/stx_search_tree.h:1054 | search_result dfs(unsigned depth, edge const* in_edge, bool& pure_out) {
method AggregationEntry(children: seq<int>, childPure: seq<bool>, eligible: bool) returns (result: int, pure: bool)
// synth: specification, invariant, or structural delimiter
  requires 0 < |children| < 4294967295 && |childPure| == |children|
// synth: specification, invariant, or structural delimiter
  requires forall i :: 0 <= i < |children| ==> 0 <= children[i] <= 3
// synth: specification, invariant, or structural delimiter
{
// src: src/util/stx_search_tree.h:1118 | bool saw_unknown = false;
  var saw_unknown := false;
// src: src/util/stx_search_tree.h:1119 | bool saw_depth_cutoff = false;
  var saw_depth_cutoff := false;
// src: src/util/stx_search_tree.h:1120 | bool all_children_pure = true; // AND-reduced across every UNSAT child
  var all_children_pure := true;
// src: src/util/stx_search_tree.h:1121 | result = search_result::unsat;
  result := 1;
// src: src/util/stx_search_tree.h:1126 | bool child_pure = false;
  pure := false;
// src: src/util/stx_search_tree.h:1122 | edge cur_edge = first_edge;
// src: src/util/stx_search_tree.h:1123 | bool have_branch = true;
  var i := 0;
// src: src/util/stx_search_tree.h:1124 | while (have_branch) {
  while i < |children|
// synth: specification, invariant, or structural delimiter
    invariant 0 <= i <= |children|
// synth: specification, invariant, or structural delimiter
    invariant result == 1
// synth: specification, invariant, or structural delimiter
    invariant forall j :: 0 <= j < i ==> children[j] != 0
// synth: specification, invariant, or structural delimiter
    invariant saw_unknown == (exists j :: 0 <= j < i && children[j] == 2)
// synth: specification, invariant, or structural delimiter
    invariant saw_depth_cutoff == (exists j :: 0 <= j < i && children[j] == 3)
// synth: specification, invariant, or structural delimiter
    invariant all_children_pure == (forall j :: 0 <= j < i ==> children[j] == 1 ==> childPure[j])
// synth: specification, invariant, or structural delimiter
    decreases |children| - i
// synth: specification, invariant, or structural delimiter
  {
// src: src/util/stx_search_tree.h:1125 | search_result cr;
// src: src/util/stx_search_tree.h:1129 | cr = dfs(depth + (cur_edge.is_progress() ? 0 : 1), &cur_edge, child_pure);
    var cr := children[i];
// src: src/util/stx_search_tree.h:1126 | bool child_pure = false;
// src: src/util/stx_search_tree.h:1129 | cr = dfs(depth + (cur_edge.is_progress() ? 0 : 1), &cur_edge, child_pure);
    var child_pure := childPure[i];
// src: src/util/stx_search_tree.h:1131 | if (cr == search_result::sat) {
    if cr == 0 {
// src: src/util/stx_search_tree.h:1132 | result = search_result::sat;
      result := 0;
// src: src/util/stx_search_tree.h:1133 | break;
      return;
// synth: specification, invariant, or structural delimiter
    }
// src: src/util/stx_search_tree.h:1135 | if (cr == search_result::unsat && !child_pure)
    if cr == 1 && !child_pure {
// src: src/util/stx_search_tree.h:1136 | all_children_pure = false;
      all_children_pure := false;
// synth: specification, invariant, or structural delimiter
    }
// src: src/util/stx_search_tree.h:1137 | if (cr == search_result::depth_cutoff)
    if cr == 3 {
// src: src/util/stx_search_tree.h:1138 | saw_depth_cutoff = true;
      saw_depth_cutoff := true;
// synth: specification, invariant, or structural delimiter
    }
// src: src/util/stx_search_tree.h:1139 | else if (cr == search_result::unknown)
    else if cr == 2 {
// src: src/util/stx_search_tree.h:1140 | saw_unknown = true;
      saw_unknown := true;
// synth: specification, invariant, or structural delimiter
    }
// src: src/util/stx_search_tree.h:1141 | have_branch = frame.m_iter && advance_iter(*frame.m_iter, cur_edge);
    i := i+1;
// synth: specification, invariant, or structural delimiter
  }
// src: src/util/stx_search_tree.h:1143 | if (result != search_result::sat) {
// src: src/util/stx_search_tree.h:1144 | result = saw_depth_cutoff ? search_result::depth_cutoff
// src: src/util/stx_search_tree.h:1145 | : saw_unknown       ? search_result::unknown
// src: src/util/stx_search_tree.h:1146 | :                     search_result::unsat;
  result := if saw_depth_cutoff then 3 else if saw_unknown then 2 else 1;
// src: src/util/stx_search_tree.h:1147 | if (result == search_result::unsat) {
  if result == 1 {
// src: src/util/stx_search_tree.h:1152 | pure_out = all_children_pure && cache_eligible(n);
    pure := all_children_pure && eligible;
// synth: specification, invariant, or structural delimiter
  }
// synth: specification, invariant, or structural delimiter
}
