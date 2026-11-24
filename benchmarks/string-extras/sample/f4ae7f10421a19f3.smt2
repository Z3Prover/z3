; origin: https://github.com/iscas-projects/SCB : jdk/smt/method-jdk.nashorn.internal.runtime.regexp.joni.MinMaxLen__distanceRangeToString__1412847221/11618.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-const null-Int Int)
(declare-const var2593 Int) ; Statement: i0 := @parameter0: int 
(assert (not (= var2593 null-Int)))
(declare-const var474 Int) ; Statement: i1 := @parameter1: int 
(assert (not (= var474 null-Int)))
 ; Statement: if i0 != 2147483647 goto $r0 = new java.lang.StringBuilder 
(assert (not (not (= var2593 2147483647)))) ; Negate: Cond: i0 != 2147483647  
(define-const var1285 String String-init) ; Statement: $r16 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var1285)) ; Statement: specialinvoke $r16.<java.lang.StringBuilder: void <init>()>() 
(declare-const var1285!1 String)
(assert (= var1285!1 ""))
(assert true)
(define-const var3242 String (append/672562846 var1285!1 "")) ; Statement: $r17 = virtualinvoke $r16.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("") 
(declare-const var1285!2 String)
(assert (= var1285!2 (str.++ var1285!1 "")))
(assert true)
(define-const var2575 String (append/672562846 var3242 "inf")) ; Statement: $r18 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("inf") 
(declare-const var3242!1 String)
(assert (= var3242!1 (str.++ var3242 "inf")))
(assert true)
(define-const var1991 String (toString/-2075883882 var2575)) ; Statement: r20 = virtualinvoke $r18.<java.lang.StringBuilder: java.lang.String toString()>() 
 ; Statement: goto [?= $r5 = new java.lang.StringBuilder] 
(assert true) ; Non Conditional
(define-const var2960 String String-init) ; Statement: $r5 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var2960)) ; Statement: specialinvoke $r5.<java.lang.StringBuilder: void <init>()>() 
(declare-const var2960!1 String)
(assert (= var2960!1 ""))
(assert true)
(define-const var1404 String (append/672562846 var2960!1 var1991)) ; Statement: $r6 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r20) 
(declare-const var2960!2 String)
(assert (= var2960!2 (str.++ var2960!1 var1991)))
(assert true)
(define-const var1790 String (append/672562846 var1404 "-")) ; Statement: $r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("-") 
(declare-const var1404!1 String)
(assert (= var1404!1 (str.++ var1404 "-")))
(assert true)
(define-const var35 String (toString/-2075883882 var1790)) ; Statement: $r19 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.String toString()>() 
 ; Statement: if i1 != 2147483647 goto $r8 = new java.lang.StringBuilder 
(assert (not (not (= var474 2147483647)))) ; Negate: Cond: i1 != 2147483647  
(define-const var1052 String String-init) ; Statement: $r13 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var1052)) ; Statement: specialinvoke $r13.<java.lang.StringBuilder: void <init>()>() 
(declare-const var1052!1 String)
(assert (= var1052!1 ""))
(assert true)
(define-const var1779 String (append/672562846 var1052!1 var35)) ; Statement: $r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r19) 
(declare-const var1052!2 String)
(assert (= var1052!2 (str.++ var1052!1 var35)))
(assert true)
(define-const var3278 String (append/672562846 var1779 "inf")) ; Statement: $r15 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("inf") 
(declare-const var1779!1 String)
(assert (= var1779!1 (str.++ var1779 "inf")))
(assert true)
(define-const var1784 String (toString/-2075883882 var3278)) ; Statement: r21 = virtualinvoke $r15.<java.lang.StringBuilder: java.lang.String toString()>() 
 ; Statement: goto [?= return r21] 
(assert true) ; Non Conditional
 ; Statement: return r21 
(check-sat)


; {String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String)}
; {var2593=i0, var474=i1, var1285=$r16, var3242=$r17, var2575=$r18, var1991=r20, var2960=$r5, var1404=$r6, var1790=$r7, var35=$r19, var1052=$r13, var1779=$r14, var3278=$r15, var1784=r21}
; {i0=var2593, i1=var474, $r16=var1285, $r17=var3242, $r18=var2575, r20=var1991, $r5=var2960, $r6=var1404, $r7=var1790, $r19=var35, $r13=var1052, $r14=var1779, $r15=var3278, r21=var1784}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>;	<java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>;	<java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 3,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 6,"<java.lang.StringBuilder: java.lang.String toString()>": 3}
;stmts i0 := @parameter0: int;	i1 := @parameter1: int;	if i0 != 2147483647 goto $r0 = new java.lang.StringBuilder;	$r16 = new java.lang.StringBuilder;	specialinvoke $r16.<java.lang.StringBuilder: void <init>()>();	$r17 = virtualinvoke $r16.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("");	$r18 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("inf");	r20 = virtualinvoke $r18.<java.lang.StringBuilder: java.lang.String toString()>();	goto [?= $r5 = new java.lang.StringBuilder];	$r5 = new java.lang.StringBuilder;	specialinvoke $r5.<java.lang.StringBuilder: void <init>()>();	$r6 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r20);	$r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("-");	$r19 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.String toString()>();	if i1 != 2147483647 goto $r8 = new java.lang.StringBuilder;	$r13 = new java.lang.StringBuilder;	specialinvoke $r13.<java.lang.StringBuilder: void <init>()>();	$r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r19);	$r15 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("inf");	r21 = virtualinvoke $r15.<java.lang.StringBuilder: java.lang.String toString()>();	goto [?= return r21];	return r21
;block_num 5