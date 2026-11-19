// src: src/smt/theory_nseq.cpp:1090 | if (all_of(m_pending_assumptions, [&](literal lit) { return ctx.get_assignment(lit) == l_true; })) {
function AllTrue(pending: seq<int>): bool
// synth: specification, invariant, or structural delimiter
{
// src: src/smt/theory_nseq.cpp:1090 | if (all_of(m_pending_assumptions, [&](literal lit) { return ctx.get_assignment(lit) == l_true; })) {
  forall i :: 0 <= i < |pending| ==> pending[i] == 1
// synth: specification, invariant, or structural delimiter
}
// src: src/smt/theory_nseq.cpp:1063 | return true;
method PendingEntry(pending: seq<int>, coherent: bool, digitBranch: bool, unhandled: int, hoSatisfied: bool) returns (status: int, cleared: bool)
// synth: specification, invariant, or structural delimiter
  requires 0 < |pending| < 4294967295
// synth: specification, invariant, or structural delimiter
  requires forall i :: 0 <= i < |pending| ==> pending[i] == -1 || pending[i] == 1
// synth: specification, invariant, or structural delimiter
  requires 0 <= unhandled <= 4294967295
// synth: specification, invariant, or structural delimiter
  ensures (status == 0) == (AllTrue(pending) && coherent && !digitBranch && unhandled == 0 && hoSatisfied)
// synth: specification, invariant, or structural delimiter
  ensures (status == 3) == !AllTrue(pending)
// synth: specification, invariant, or structural delimiter
  ensures cleared == (!AllTrue(pending) || !coherent)
// synth: specification, invariant, or structural delimiter
{
// src: src/smt/theory_nseq.cpp:1088 | if (!m_pending_assumptions.empty()) {
  status, cleared := 3, false;
// src: src/smt/theory_nseq.cpp:1090 | if (all_of(m_pending_assumptions, [&](literal lit) { return ctx.get_assignment(lit) == l_true; })) {
  if AllTrue(pending) {
// src: src/smt/theory_nseq.cpp:1091 | if (check_stoi_coherence()) {
    if coherent {
// src: src/smt/theory_nseq.cpp:1092 | if (branch_stoi_digit())
      if digitBranch {
// src: src/smt/theory_nseq.cpp:1093 | return FC_CONTINUE;
        status := 1; return;
// synth: specification, invariant, or structural delimiter
      }
// src: src/smt/theory_nseq.cpp:1094 | return m_num_unhandled || !hf.is_satisfied() ? FC_GIVEUP : FC_DONE;
      status := if unhandled != 0 || !hoSatisfied then 2 else 0;
// src: src/smt/theory_nseq.cpp:1094 | return m_num_unhandled || !hf.is_satisfied() ? FC_GIVEUP : FC_DONE;
      return;
// synth: specification, invariant, or structural delimiter
    }
// src: src/smt/theory_nseq.cpp:1096 | m_pending_assumptions.reset();
    cleared := true;
// src: src/smt/theory_nseq.cpp:1097 | return FC_CONTINUE;
    status := 1; return;
// synth: specification, invariant, or structural delimiter
  }
// src: src/smt/theory_nseq.cpp:1103 | m_pending_assumptions.reset();
  cleared := true;
// src: src/smt/theory_nseq.cpp:1104 | }
  status := 3;
// synth: specification, invariant, or structural delimiter
}
