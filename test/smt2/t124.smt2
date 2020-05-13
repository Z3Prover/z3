
; Copyright (c) 2015 Microsoft Corporation

(set-option :print-success true)

(declare-datatypes (T) ((LispList nil (cons (car T) (cdr LispList)))))

(declare-const x (LispList Int))

(display (cons 10 nil))
