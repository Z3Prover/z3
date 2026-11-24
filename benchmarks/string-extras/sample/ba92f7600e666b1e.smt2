; origin: https://github.com/plfm-iis/trauc_benchmarks : add_binary/33.smt2
(declare-fun a () String)
(declare-fun b () String)


(assert ( >= ( + ( + ( + 0 1  ) ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 4)  )  )  ) ( - ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 4)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 4)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at a ( + ( str.len a  ) (- 4)  )  )  )  )  ) ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 4)  )  )  ) ( - ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 4)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 4)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at b ( + ( str.len b  ) (- 4)  )  )  )  )  ) 2  ))

(assert ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 4)  )  )  ) ( ite ( = (- 1) ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 4)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 4)  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to_int ( str.at b ( + ( str.len b  ) (- 4)  )  )  )  ) false true  )  ))

(assert ( >= ( + ( str.len b  ) ( - ( - ( - (- 1) 1  ) 1  ) 1  )  ) 0  ))

(assert ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 4)  )  )  ) ( ite ( = (- 1) ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 4)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 4)  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to_int ( str.at a ( + ( str.len a  ) (- 4)  )  )  )  ) false true  )  ))

(assert ( >= ( + ( str.len a  ) ( - ( - ( - (- 1) 1  ) 1  ) 1  )  ) 0  ))

(assert ( >= ( + ( str.len a  ) ( - ( - ( - (- 1) 1  ) 1  ) 1  )  ) 0  ))

(assert (not ( >= ( - ( + ( + ( + 0 1  ) ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 3)  )  )  ) ( - ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 3)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 3)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at a ( + ( str.len a  ) (- 3)  )  )  )  )  ) ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 3)  )  )  ) ( - ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 3)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 3)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at b ( + ( str.len b  ) (- 3)  )  )  )  )  ) 2  ) 2  )))

(assert ( >= ( + ( + ( + 0 1  ) ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 3)  )  )  ) ( - ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 3)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 3)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at a ( + ( str.len a  ) (- 3)  )  )  )  )  ) ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 3)  )  )  ) ( - ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 3)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 3)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at b ( + ( str.len b  ) (- 3)  )  )  )  )  ) 2  ))

(assert ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 3)  )  )  ) ( ite ( = (- 1) ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 3)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 3)  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to_int ( str.at b ( + ( str.len b  ) (- 3)  )  )  )  ) false true  )  ))

(assert ( >= ( + ( str.len b  ) ( - ( - (- 1) 1  ) 1  )  ) 0  ))

(assert ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 3)  )  )  ) ( ite ( = (- 1) ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 3)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 3)  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to_int ( str.at a ( + ( str.len a  ) (- 3)  )  )  )  ) false true  )  ))

(assert ( >= ( + ( str.len a  ) ( - ( - (- 1) 1  ) 1  )  ) 0  ))

(assert ( >= ( + ( str.len a  ) ( - ( - (- 1) 1  ) 1  )  ) 0  ))

(assert (not ( >= ( - ( + ( + ( + 0 1  ) ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 2)  )  )  ) ( - ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 2)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 2)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at a ( + ( str.len a  ) (- 2)  )  )  )  )  ) ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 2)  )  )  ) ( - ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 2)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 2)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at b ( + ( str.len b  ) (- 2)  )  )  )  )  ) 2  ) 2  )))

(assert ( >= ( + ( + ( + 0 1  ) ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 2)  )  )  ) ( - ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 2)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 2)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at a ( + ( str.len a  ) (- 2)  )  )  )  )  ) ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 2)  )  )  ) ( - ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 2)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 2)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at b ( + ( str.len b  ) (- 2)  )  )  )  )  ) 2  ))

(assert ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 2)  )  )  ) ( ite ( = (- 1) ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 2)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 2)  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to_int ( str.at b ( + ( str.len b  ) (- 2)  )  )  )  ) false true  )  ))

(assert ( >= ( + ( str.len b  ) ( - (- 1) 1  )  ) 0  ))

(assert ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 2)  )  )  ) ( ite ( = (- 1) ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 2)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 2)  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to_int ( str.at a ( + ( str.len a  ) (- 2)  )  )  )  ) false true  )  ))

(assert ( >= ( + ( str.len a  ) ( - (- 1) 1  )  ) 0  ))

(assert ( >= ( + ( str.len a  ) ( - (- 1) 1  )  ) 0  ))

(assert (not ( >= ( - ( + ( + 0 ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 1)  )  )  ) ( - ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 1)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 1)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at a ( + ( str.len a  ) (- 1)  )  )  )  )  ) ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 1)  )  )  ) ( - ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 1)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 1)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at b ( + ( str.len b  ) (- 1)  )  )  )  )  ) 2  ) 2  )))

(assert ( >= ( + ( + 0 ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 1)  )  )  ) ( - ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 1)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 1)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at a ( + ( str.len a  ) (- 1)  )  )  )  )  ) ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 1)  )  )  ) ( - ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 1)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 1)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at b ( + ( str.len b  ) (- 1)  )  )  )  )  ) 2  ))

(assert ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 1)  )  )  ) ( ite ( = (- 1) ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 1)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 1)  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to_int ( str.at b ( + ( str.len b  ) (- 1)  )  )  )  ) false true  )  ))

(assert ( >= ( + ( str.len b  ) (- 1)  ) 0  ))

(assert ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 1)  )  )  ) ( ite ( = (- 1) ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 1)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 1)  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to_int ( str.at a ( + ( str.len a  ) (- 1)  )  )  )  ) false true  )  ))

(assert ( >= ( + ( str.len a  ) (- 1)  ) 0  ))

(assert ( >= ( + ( str.len a  ) (- 1)  ) 0  ))
(assert ( >= ( - ( + ( + ( + 0 1  ) ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 4)  )  )  ) ( - ( str.to_int ( str.substr ( str.at a ( + ( str.len a  ) (- 4)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 4)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at a ( + ( str.len a  ) (- 4)  )  )  )  )  ) ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 4)  )  )  ) ( - ( str.to_int ( str.substr ( str.at b ( + ( str.len b  ) (- 4)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 4)  )  )  ) 1  )  )  )  ) ( str.to_int ( str.at b ( + ( str.len b  ) (- 4)  )  )  )  )  ) 2  ) 2  ))
(assert (str.in_re a (re.+ (re.range "0" "1"))))
(assert (str.in_re b (re.+ (re.range "0" "1"))))


(check-sat)



