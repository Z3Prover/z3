;; Mutation-Based Equivalence Benchmark
;; Source:     AutomatArk / instance11285.smt2
;; Mutations:  literal_char_inc, literal_char_dec, literal_char_inc
;; Status:     sat
;;
;; Original regex vs mutated regex
;; Equivalence check: unsat ⟺ L(R1) = L(R2)

(set-info :smt-lib-version 2.6)
(set-info :category "mutation")
(set-info :status sat)
(set-logic QF_S)


;; R1: original
;; R2: mutated (literal_char_inc, literal_char_dec, literal_char_inc)
(assert
  (not
    (=
      (re.++ (str.to_re "<") (re.opt (str.to_re "/")) (re.union (str.to_re "a") (str.to_re "abbr") (str.to_re "acronym") (str.to_re "address") (str.to_re "applet") (str.to_re "area") (str.to_re "b") (str.to_re "base") (str.to_re "basefont") (str.to_re "bdo") (str.to_re "big") (str.to_re "blockquote") (str.to_re "body") (str.to_re "br") (str.to_re "button") (str.to_re "caption") (str.to_re "center") (str.to_re "cite") (str.to_re "code") (str.to_re "col") (str.to_re "colgroup") (str.to_re "dd") (str.to_re "del") (str.to_re "dir") (str.to_re "div") (str.to_re "dfn") (str.to_re "dl") (str.to_re "dt") (str.to_re "em") (str.to_re "fieldset") (str.to_re "font") (str.to_re "form") (str.to_re "frame") (str.to_re "frameset") (re.++ (str.to_re "h") (re.range "1" "6")) (str.to_re "head") (str.to_re "hr") (str.to_re "html") (str.to_re "i") (str.to_re "iframe") (str.to_re "img") (str.to_re "input") (str.to_re "ins") (str.to_re "isindex") (str.to_re "kbd") (str.to_re "label") (str.to_re "legend") (str.to_re "li") (str.to_re "link") (str.to_re "map") (str.to_re "menu") (str.to_re "meta") (str.to_re "noframes") (str.to_re "noscript") (str.to_re "object") (str.to_re "ol") (str.to_re "optgroup") (str.to_re "option") (str.to_re "p") (str.to_re "param") (str.to_re "pre") (str.to_re "q") (str.to_re "s") (str.to_re "samp") (str.to_re "script") (str.to_re "select") (str.to_re "small") (str.to_re "span") (str.to_re "strike") (str.to_re "strong") (str.to_re "style") (str.to_re "sub") (str.to_re "sup") (str.to_re "table") (str.to_re "tbody") (str.to_re "td") (str.to_re "textarea") (str.to_re "tfoot") (str.to_re "th") (str.to_re "thead") (str.to_re "title") (str.to_re "tr") (str.to_re "tt") (str.to_re "u") (str.to_re "ul") (str.to_re "var") (str.to_re "xmp")) (re.* (re.union (re.* (re.union (re.++ (str.to_re "\u{22}") (re.* (re.comp (str.to_re "\u{22}"))) (str.to_re "\u{22}")) (re.++ (str.to_re "'") (re.* (re.comp (str.to_re "'"))) (str.to_re "'")))) (str.to_re "\u{22}") (str.to_re "'") (str.to_re ">"))) (str.to_re ">\u{a}"))
      (re.++ (str.to_re "<") (re.opt (str.to_re "/")) (re.union (str.to_re "a") (str.to_re "abbr") (str.to_re "acronym") (str.to_re "address") (str.to_re "applet") (str.to_re "area") (str.to_re "b") (str.to_re "base") (str.to_re "basefont") (str.to_re "bdo") (str.to_re "big") (str.to_re "blockquote") (str.to_re "body") (str.to_re "br") (str.to_re "buttoo") (str.to_re "caption") (str.to_re "center") (str.to_re "cite") (str.to_re "code") (str.to_re "col") (str.to_re "colgroup") (str.to_re "dd") (str.to_re "del") (str.to_re "dir") (str.to_re "div") (str.to_re "dfn") (str.to_re "dl") (str.to_re "dt") (str.to_re "em") (str.to_re "fieldset") (str.to_re "font") (str.to_re "form") (str.to_re "frame") (str.to_re "frameset") (re.++ (str.to_re "h") (re.range "1" "6")) (str.to_re "head") (str.to_re "hr") (str.to_re "html") (str.to_re "i") (str.to_re "iframe") (str.to_re "img") (str.to_re "input") (str.to_re "ins") (str.to_re "isindex") (str.to_re "kbd") (str.to_re "label") (str.to_re "legend") (str.to_re "li") (str.to_re "link") (str.to_re "map") (str.to_re "menu") (str.to_re "meta") (str.to_re "noframes") (str.to_re "noscript") (str.to_re "objecs") (str.to_re "ol") (str.to_re "optgroup") (str.to_re "option") (str.to_re "p") (str.to_re "param") (str.to_re "pre") (str.to_re "q") (str.to_re "s") (str.to_re "samp") (str.to_re "script") (str.to_re "select") (str.to_re "small") (str.to_re "span") (str.to_re "strike") (str.to_re "strong") (str.to_re "style") (str.to_re "sub") (str.to_re "sup") (str.to_re "table") (str.to_re "tbody") (str.to_re "td") (str.to_re "textarea") (str.to_re "tfoot") (str.to_re "th") (str.to_re "thead") (str.to_re "title") (str.to_re "tr") (str.to_re "tt") (str.to_re "u") (str.to_re "ul") (str.to_re "var") (str.to_re "xmp")) (re.* (re.union (re.* (re.union (re.++ (str.to_re "\u{22}") (re.* (re.comp (str.to_re "\u{22}"))) (str.to_re "\u{22}")) (re.++ (str.to_re "'") (re.* (re.comp (str.to_re "'"))) (str.to_re "'")))) (str.to_re "\u{22}") (str.to_re "(") (str.to_re ">"))) (str.to_re ">\u{a}")))))

(check-sat)
(exit)
