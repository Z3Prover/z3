; origin: https://github.com/iscas-projects/SCB : mysql-connector-j/smt/method-com.mysql.cj.util.StringUtils__getBytesWrapped__390923487/7000.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3422 0)
(declare-sort var2248 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun String-init () String)
(define-fun length/-134980193 ((s String)) Int (str.len s))
(declare-fun <init>/543593434 (String Int) void)
(declare-fun append/-1166366385 (String Int) String)
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun var2248_getBytes/-1177224413 (String) (Array Int Int))
(declare-const null-String String)
(declare-const null-Int Int)
(declare-const var3646 String) ; Statement: r4 := @parameter0: java.lang.String 
(assert (not (= var3646 null-String)))
(declare-const var1730 Int) ; Statement: c2 := @parameter1: char 
(assert (not (= var1730 null-Int)))
(declare-const var1809 Int) ; Statement: c3 := @parameter2: char 
(assert (not (= var1809 null-Int)))
(declare-const var2709 String) ; Statement: r0 := @parameter3: java.lang.String 
(assert (not (= var2709 null-String)))
 ; Statement: if r0 != null goto $r1 = new java.lang.StringBuilder 
(assert (not (not (= var2709 null-String)))) ; Negate: Cond: r0 != null  
(define-const var465 String String-init) ; Statement: $r2 = new java.lang.StringBuilder 
(assert true)
(define-const var3023 Int (length/-134980193 var3646)) ; Statement: $i4 = virtualinvoke r4.<java.lang.String: int length()>() 
(define-const var385 Int (+ var3023 2)) ; Statement: $i5 = $i4 + 2 
(assert true)
;(assert (<init>/543593434 var465 var385)) ; Statement: specialinvoke $r2.<java.lang.StringBuilder: void <init>(int)>($i5) 

(declare-const var465!1 String)
(declare-const var385!1 Int)
(assert true)
;(assert (append/-1166366385 var465!1 var1730)) ; Statement: virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(c2) 
(declare-const var465!2 String)
(assert (str.prefixof var465!1 var465!2))
(assert true)
;(assert (append/672562846 var465!2 var3646)) ; Statement: virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r4) 
(declare-const var465!3 String)
(assert (= var465!3 (str.++ var465!2 var3646)))
(assert true)
;(assert (append/-1166366385 var465!3 var1809)) ; Statement: virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(c3) 
(declare-const var465!4 String)
(assert (str.prefixof var465!3 var465!4))
(assert true)
(define-const var1078 String (toString/-2075883882 var465!4)) ; Statement: $r3 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.String toString()>() 
(define-const var938 (Array Int Int) (var2248_getBytes/-1177224413 var1078)) ; Statement: r5 = staticinvoke <com.mysql.cj.util.StringUtils: byte[] getBytes(java.lang.String)>($r3) 
 ; Statement: goto [?= return r5] 
(assert true) ; Non Conditional
 ; Statement: return r5 
(check-sat)


; {String-init=([], java.lang.StringBuilder), length/-134980193=([java.lang.String], int), <init>/543593434=([java.lang.StringBuilder, int], void), append/-1166366385=([java.lang.StringBuilder, char], java.lang.StringBuilder), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), var2248_getBytes/-1177224413=([java.lang.String], byte[])}
; {var3646=r4, var3422=null_type, var1730=c2, var1809=c3, var2709=r0, var465=$r2, var3023=$i4, var385=$i5, var1078=$r3, var2248=com.mysql.cj.util.StringUtils, var938=r5}
; {r4=var3646, null_type=var3422, c2=var1730, c3=var1809, r0=var2709, $r2=var465, $i4=var3023, $i5=var385, $r3=var1078, com.mysql.cj.util.StringUtils=var2248, r5=var938}
;seq <java.lang.String: int length()>;	<java.lang.StringBuilder: void <init>(int)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(char)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(char)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.String: int length()>": 1,"<java.lang.StringBuilder: void <init>(int)>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(char)>": 2,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r4 := @parameter0: java.lang.String;	c2 := @parameter1: char;	c3 := @parameter2: char;	r0 := @parameter3: java.lang.String;	if r0 != null goto $r1 = new java.lang.StringBuilder;	$r2 = new java.lang.StringBuilder;	$i4 = virtualinvoke r4.<java.lang.String: int length()>();	$i5 = $i4 + 2;	specialinvoke $r2.<java.lang.StringBuilder: void <init>(int)>($i5);	virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(c2);	virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r4);	virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(c3);	$r3 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.String toString()>();	r5 = staticinvoke <com.mysql.cj.util.StringUtils: byte[] getBytes(java.lang.String)>($r3);	goto [?= return r5];	return r5
;block_num 3