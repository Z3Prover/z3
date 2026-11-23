; Rewrite conjectures for addStrings_223_before.smt2.
; Orient each equality left-to-right; implications supply required guards.
; Named assertions state rules, not validity checks. Validate by negating
; each rule separately with fresh constants for its quantified variables.
; Validation with string_solver=seq and seq.regular=false: 12 negations
; were unsat. The four unrestricted decimal rules below timed out at 3s
; each and remain unproved conjectures; they are marked individually.
(set-logic ALL)

(define-fun digit () (RegEx String) (re.range "0" "9"))
(define-fun decimal () (RegEx String) (re.+ digit))
(define-fun positive-decimal () (RegEx String)
  (re.++ (re.* (str.to_re "0")) (re.range "1" "9") (re.* digit)))

; These abbreviations preserve the benchmark's signed parsing expressions.
(define-fun signed-value ((s String)) Int
  (ite (str.prefixof "-" s)
       (- (str.to_int (str.substr s 1 (- (str.len s) 1))))
       (str.to_int s)))
(define-fun signed-valid ((s String)) Bool
  (ite (str.prefixof "-" s)
       (and (not (= (- 1) (str.to_int (str.substr s 1 (- (str.len s) 1)))))
            (> (str.len s) 1))
       (not (= (- 1) (str.to_int s)))))

(assert (! (= (str.to_int "") (- 1))
  :named empty-to-int))

(assert (! (forall ((s String) (i Int))
  (= (str.len (str.at s i))
     (ite (and (<= 0 i) (< i (str.len s))) 1 0)))
  :named at-length))

; The starting position is beyond any str.at result, even out of bounds.
(assert (! (forall ((s String) (i Int) (n Int))
  (= (str.substr (str.at s i) 1 n) ""))
  :named at-tail-empty))

(assert (! (forall ((p String) (s String) (i Int))
  (=> (= (str.len p) 1)
      (= (str.prefixof p (str.at s i)) (= p (str.at s i)))))
  :named single-character-prefix-at))

(assert (! (forall ((s String) (k Int))
  (= (str.len (str.at s (- (str.len s) k)))
     (ite (and (> k 0) (>= (str.len s) k)) 1 0)))
  :named suffix-at-length))

; Includes the empty/out-of-bounds case and all non-ASCII-digit characters.
(assert (! (forall ((c String))
  (=> (<= (str.len c) 1)
      (= (str.to_int c)
         (ite (str.in_re c digit) (- (str.to_code c) 48) (- 1)))))
  :named single-character-to-int))

(assert (! (forall ((c String))
  (=> (<= (str.len c) 1)
      (= (not (= (str.to_int c) (- 1))) (str.in_re c digit))))
  :named single-character-decimal-valid))

; A lone minus parses as 1 here: negating str.to_int("") negates -1.
; Do not drop the minus branch without a digit-validity assumption.
(assert (! (forall ((c String))
  (=> (<= (str.len c) 1)
      (= (signed-value c) (ite (= c "-") 1 (str.to_int c)))))
  :named single-character-signed-value))

(assert (! (forall ((c String))
  (=> (<= (str.len c) 1)
      (= (signed-valid c) (str.in_re c digit))))
  :named single-character-signed-valid))

; Every per-position validity assertion therefore supplies this context.
(assert (! (forall ((c String))
  (=> (str.in_re c digit)
      (= (signed-value c) (- (str.to_code c) 48))))
  :named valid-digit-signed-value))

; Unproved: unrestricted decimal recognition.
(assert (! (forall ((s String))
  (= (not (= (str.to_int s) (- 1))) (str.in_re s decimal)))
  :named decimal-valid))

; Leading zeros are allowed; empty strings and all-zero strings are excluded.
; Unproved: unrestricted positive-decimal recognition.
(assert (! (forall ((s String))
  (= (> (str.to_int s) 0) (str.in_re s positive-decimal)))
  :named decimal-positive))

; Unproved: unrestricted signed-decimal recognition.
(assert (! (forall ((s String))
  (= (signed-valid s)
     (str.in_re s (re.union decimal (re.++ (str.to_re "-") decimal)))))
  :named signed-decimal-valid))

; Combine the benchmark's positivity and validity assertions before rewriting.
; Unproved: unrestricted valid signed-positive recognition.
(assert (! (forall ((s String))
  (= (and (signed-valid s) (> (signed-value s) 0))
     (str.in_re s positive-decimal)))
  :named valid-signed-decimal-positive))

; Arithmetic cleanup exposes k = 4, 3, 2, 1, 5 in the benchmark.
; The k = 5 conjunction subsumes the other four length assertions.
(assert (! (forall ((s String) (t String) (k Int))
  (= (>= (ite (< (str.len s) (str.len t)) (str.len s) (str.len t)) k)
     (and (>= (str.len s) k) (>= (str.len t) k))))
  :named minimum-length-bound))

(assert (! (forall ((s String))
  (= (not (= (str.len s) 0)) (not (= s ""))))
  :named nonempty-string))
