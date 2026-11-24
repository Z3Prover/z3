; origin: https://github.com/iscas-projects/SCB : jdk/smt/method-jdk.nashorn.internal.runtime.UnwarrantedOptimismException__getMessage__1569445498/12724.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var921 0)
(declare-sort var393 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun returnValue/-1623072993 (var921) var393)
(declare-fun append/-1031950772 (String var393) String)
(declare-fun hasInvalidProgramPoint/-1629247213 (var921) Bool)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-const null-var921 var921)
(declare-const null-var393 var393)
(declare-const var752 var921) ; Statement: r1 := @this: jdk.nashorn.internal.runtime.UnwarrantedOptimismException 
(assert (not (= var752 null-var921)))
(define-const var1337 String String-init) ; Statement: $r0 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var1337)) ; Statement: specialinvoke $r0.<java.lang.StringBuilder: void <init>()>() 
(declare-const var1337!1 String)
(assert (= var1337!1 ""))
(assert true)
(define-const var1646 String (append/672562846 var1337!1 "UNWARRANTED OPTIMISM: [returnValue=")) ; Statement: $r3 = virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("UNWARRANTED OPTIMISM: [returnValue=") 
(declare-const var1337!2 String)
(assert (= var1337!2 (str.++ var1337!1 "UNWARRANTED OPTIMISM: [returnValue=")))
(define-const var3534 var393 (returnValue/-1623072993 var752)) ; Statement: $r2 = r1.<jdk.nashorn.internal.runtime.UnwarrantedOptimismException: java.lang.Object returnValue> 
(assert true)
(define-const var1605 String (append/-1031950772 var1646 var3534)) ; Statement: $r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r2) 
(declare-const var1646!1 String)
(assert (str.prefixof var1646 var1646!1))
(assert true)
(define-const var2282 String (append/672562846 var1605 " (class=")) ; Statement: $r8 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(" (class=") 
(declare-const var1605!1 String)
(assert (= var1605!1 (str.++ var1605 " (class=")))
(define-const var2060 var393 (returnValue/-1623072993 var752)) ; Statement: $r5 = r1.<jdk.nashorn.internal.runtime.UnwarrantedOptimismException: java.lang.Object returnValue> 
 ; Statement: if $r5 != null goto $r6 = r1.<jdk.nashorn.internal.runtime.UnwarrantedOptimismException: java.lang.Object returnValue> 
(assert (not (not (= var2060 null-var393)))) ; Negate: Cond: $r5 != null  
(define-const var3828 String "null") ; Statement: $r16 = "null" 
 ; Statement: goto [?= $r12 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r16)] 
(assert true) ; Non Conditional
(assert true)
(define-const var3880 String (append/672562846 var2282 var3828)) ; Statement: $r12 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r16) 
(declare-const var2282!1 String)
(assert (= var2282!1 (str.++ var2282 var3828)))
(assert true)
(define-const var2231 Bool (hasInvalidProgramPoint/-1629247213 var752)) ; Statement: $z0 = virtualinvoke r1.<jdk.nashorn.internal.runtime.UnwarrantedOptimismException: boolean hasInvalidProgramPoint()>() 
 ; Statement: if $z0 == 0 goto $r9 = new java.lang.StringBuilder 
(assert (not (= (ite var2231 1 0) 0))) ; Negate: Cond: $z0 == 0  
(define-const var1761 String " <invalid program point>") ; Statement: $r17 = " <invalid program point>" 
 ; Statement: goto [?= $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r17)] 
(assert true) ; Non Conditional
(assert true)
(define-const var2650 String (append/672562846 var3880 var1761)) ; Statement: $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r17) 
(declare-const var3880!1 String)
(assert (= var3880!1 (str.++ var3880 var1761)))
(assert true)
(define-const var3734 String (append/672562846 var2650 ")]")) ; Statement: $r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(")]") 
(declare-const var2650!1 String)
(assert (= var2650!1 (str.++ var2650 ")]")))
(assert true)
(define-const var3376 String (toString/-2075883882 var3734)) ; Statement: $r15 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.String toString()>() 
 ; Statement: return $r15 
(check-sat)


; {String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), returnValue/-1623072993=([jdk.nashorn.internal.runtime.UnwarrantedOptimismException], java.lang.Object), append/-1031950772=([java.lang.StringBuilder, java.lang.Object], java.lang.StringBuilder), hasInvalidProgramPoint/-1629247213=([jdk.nashorn.internal.runtime.UnwarrantedOptimismException], boolean), toString/-2075883882=([java.lang.StringBuilder], java.lang.String)}
; {var921=jdk.nashorn.internal.runtime.UnwarrantedOptimismException, var752=r1, var1337=$r0, var1646=$r3, var393=java.lang.Object, var3534=$r2, var1605=$r4, var2282=$r8, var2060=$r5, var3828=$r16, var3880=$r12, var2231=$z0, var1761=$r17, var2650=$r13, var3734=$r14, var3376=$r15}
; {jdk.nashorn.internal.runtime.UnwarrantedOptimismException=var921, r1=var752, $r0=var1337, $r3=var1646, java.lang.Object=var393, $r2=var3534, $r4=var1605, $r8=var2282, $r5=var2060, $r16=var3828, $r12=var3880, $z0=var2231, $r17=var1761, $r13=var2650, $r14=var3734, $r15=var3376}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 5,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r1 := @this: jdk.nashorn.internal.runtime.UnwarrantedOptimismException;	$r0 = new java.lang.StringBuilder;	specialinvoke $r0.<java.lang.StringBuilder: void <init>()>();	$r3 = virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("UNWARRANTED OPTIMISM: [returnValue=");	$r2 = r1.<jdk.nashorn.internal.runtime.UnwarrantedOptimismException: java.lang.Object returnValue>;	$r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r2);	$r8 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(" (class=");	$r5 = r1.<jdk.nashorn.internal.runtime.UnwarrantedOptimismException: java.lang.Object returnValue>;	if $r5 != null goto $r6 = r1.<jdk.nashorn.internal.runtime.UnwarrantedOptimismException: java.lang.Object returnValue>;	$r16 = "null";	goto [?= $r12 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r16)];	$r12 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r16);	$z0 = virtualinvoke r1.<jdk.nashorn.internal.runtime.UnwarrantedOptimismException: boolean hasInvalidProgramPoint()>();	if $z0 == 0 goto $r9 = new java.lang.StringBuilder;	$r17 = " <invalid program point>";	goto [?= $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r17)];	$r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r17);	$r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(")]");	$r15 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.String toString()>();	return $r15
;block_num 5