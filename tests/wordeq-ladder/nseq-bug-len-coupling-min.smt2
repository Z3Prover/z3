; nseq-bug-len-coupling-min  MINIMAL SOUNDNESS REPRODUCER (nseq returns spurious unsat)
; Companion to d5-two-var-square.smt2 (which triggers the same bug via a word equation).
; Membership: x.x in (Sigma* "a" Sigma*)  with  |x| = 1
; Expected: sat  (x="a" -> "aa" contains "a", and |x|=1)
;   z3 file.smt2                        -> sat    (correct)
;   z3 smt.string_solver=nseq file.smt2 -> unsat  (WRONG; c3-branch nseq solver only, master unaffected)
; Trigger = regex membership over a str.++ of variable terms + an EXACT length (str.len = k,
;   or a word equation that forces lengths). Inequalities (>=) or no length coupling are fine;
;   default / seq / z3str3 are all correct. Same class as the L2-04 length/Parikh coupling bug.

(set-logic QF_SLIA)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(set-info :category "crafted")
(set-info :source |Minimal reproducer for an nseq (smt.string_solver=nseq, c3 branch) spurious-unsat soundness bug, distilled from the lookaround membership benchmarks (resharp-node data/lookarounds.json, IPv6 exactly-one-"::" query). Companion to d5-two-var-square.smt2.|)
(declare-fun x () String)

; x.x must contain "a"  and  |x| = 1
(assert (str.in_re (str.++ x x)
  (re.++ (re.* re.allchar) (re.++ (str.to_re "a") (re.* re.allchar)))))
(assert (= (str.len x) 1))

(check-sat)
