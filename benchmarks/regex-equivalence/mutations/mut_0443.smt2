;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11598.smt2
;; Mutations:  intersect_ascii_printable_only, intersect_no_upper2, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)

(declare-const x String)

;; R1: original
;; R2: mutated (intersect_ascii_printable_only, intersect_no_upper2, literal_char_inc)
(assert
  (str.in_re x
    (re.union (re.inter (re.++ (str.to_re "UploadFriendly is an easy to use Java Applet that will allow multiple file uploads on a web server in a web page") re.allchar (str.to_re " The control supports file filtering, limits and more") re.allchar (str.to_re " Samples available in the following languages: ASP, ASP") re.allchar (str.to_re "NET, PHP, Coldfusion and JSP\u{a}")) (re.comp (re.++ (str.to_re "UploadFriendly is an easy to use Java Applet that will allow multiple file uploads on a web server in a web pagf") re.allchar (str.to_re " The control supports file filtering, limits and more") re.allchar (re.inter (str.to_re " Samples available in the following languages: ASP, ASP") (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) re.allchar (re.inter (str.to_re "NET, PHP, Coldfusion and JSP\u{a}") (re.* (re.range " " "~")))))) (re.inter (re.comp (re.++ (str.to_re "UploadFriendly is an easy to use Java Applet that will allow multiple file uploads on a web server in a web page") re.allchar (str.to_re " The control supports file filtering, limits and more") re.allchar (str.to_re " Samples available in the following languages: ASP, ASP") re.allchar (str.to_re "NET, PHP, Coldfusion and JSP\u{a}"))) (re.++ (str.to_re "UploadFriendly is an easy to use Java Applet that will allow multiple file uploads on a web server in a web pagf") re.allchar (str.to_re " The control supports file filtering, limits and more") re.allchar (re.inter (str.to_re " Samples available in the following languages: ASP, ASP") (re.comp (re.++ re.all ((_ re.loop 2 2) (re.range "A" "Z")) re.all))) re.allchar (re.inter (str.to_re "NET, PHP, Coldfusion and JSP\u{a}") (re.* (re.range " " "~"))))))))

(check-sat)
(exit)
