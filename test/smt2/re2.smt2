(declare-const a String)
(declare-const b String)
(declare-const r (RegEx String))
(declare-const r1 (RegEx String))
(declare-const r2 (RegEx String))

(simplify (str.in.re "" (re.* r)))
(simplify (str.in.re "" (re.+ r)))
(simplify (str.in.re "" (re.* (str.to.re "a"))))
