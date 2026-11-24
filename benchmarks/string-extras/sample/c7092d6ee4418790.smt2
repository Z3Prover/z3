; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/str-in-re-consume-inter-star.smt2
; EXPECT: unsat
; Regression for CPC proof checking of the STR_IN_RE_CONSUME rewrite. The
; intersection (re.* alnum) & (re.allchar ++ "qx") has its re.* child first, which
; does not fully consume, so $str_re_consume_inter must still detect the conflict in
; the second child ("...qx" cannot follow the "tag:svc:qx:" prefix). Also exercises
; flattening of re.inter whose printed re.all terminator is an explicit operand.
(set-logic QF_S)
(declare-const resource String)
(assert (str.in_re resource (re.++ (str.to_re "tag:svc:qx:") (re.* re.allchar))))
(assert (str.in_re resource
  (re.++ (str.to_re "tag:svc:")
         (re.inter (re.* (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "-")))
                   (re.++ re.allchar (str.to_re "qx")))
         (str.to_re ":sector:tsk"))))
(check-sat)
