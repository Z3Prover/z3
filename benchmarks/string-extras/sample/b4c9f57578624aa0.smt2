; origin: https://github.com/iscas-projects/SCB : okhttp/smt/method-okhttp3.internal.concurrent.TaskRunner__afterRun__801688394/1621.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var1860 0)
(declare-sort var2845 0)
(declare-sort var1168 0)
(declare-sort var1583 0)
(declare-sort var2096 0)
(declare-sort var3008 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun var1583_holdsLock/-145342167 (var2096) Bool)
(declare-fun cast-from-var1860-to-var2096 (var1860) var2096)
(declare-fun var3008-init () var3008)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun var1583_currentThread/-1037784612 () var1583)
(declare-fun getName/-942182377 (var1583) String)
(declare-fun append/-1031950772 (String var2096) String)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun <init>/582965326 (var3008 var2096) void)
(declare-fun cast-from-String-to-var2096 (String) var2096)
(declare-const null-var1860 var1860)
(declare-const null-var2845 var2845)
(declare-const null-Int Int)
(declare-const var1168-assertionsEnabled Bool)
(declare-const var1401 var1860) ; Statement: r0 := @this: okhttp3.internal.concurrent.TaskRunner 
(assert (not (= var1401 null-var1860)))
(declare-const var2881 var2845) ; Statement: r1 := @parameter0: okhttp3.internal.concurrent.Task 
(assert (not (= var2881 null-var2845)))
(declare-const var10 Int) ; Statement: l0 := @parameter1: long 
(assert (not (= var10 null-Int)))
(define-const var3317 Bool var1168-assertionsEnabled) ; Statement: $z0 = <okhttp3.internal.Util: boolean assertionsEnabled> 
 ; Statement: if $z0 == 0 goto $r2 = virtualinvoke r1.<okhttp3.internal.concurrent.Task: okhttp3.internal.concurrent.TaskQueue getQueue$okhttp()>() 
(assert (not (= (ite var3317 1 0) 0))) ; Negate: Cond: $z0 == 0  
(define-const var1412 Bool (var1583_holdsLock/-145342167 (cast-from-var1860-to-var2096 var1401))) ; Statement: $z2 = staticinvoke <java.lang.Thread: boolean holdsLock(java.lang.Object)>(r0) 
 ; Statement: if $z2 != 0 goto $r2 = virtualinvoke r1.<okhttp3.internal.concurrent.Task: okhttp3.internal.concurrent.TaskQueue getQueue$okhttp()>() 
(assert (not (not (= (ite var1412 1 0) 0)))) ; Negate: Cond: $z2 != 0  
(define-const var2476 var3008 var3008-init) ; Statement: $r9 = new java.lang.AssertionError 
(define-const var983 String String-init) ; Statement: $r10 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var983)) ; Statement: specialinvoke $r10.<java.lang.StringBuilder: void <init>()>() 
(declare-const var983!1 String)
(assert (= var983!1 ""))
(assert true)
(define-const var1954 String (append/672562846 var983!1 "Thread ")) ; Statement: $r13 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Thread ") 
(declare-const var983!2 String)
(assert (= var983!2 (str.++ var983!1 "Thread ")))
(define-const var1943 var1583 var1583_currentThread/-1037784612) ; Statement: $r11 = staticinvoke <java.lang.Thread: java.lang.Thread currentThread()>() 
(assert true)
(define-const var2372 String (getName/-942182377 var1943)) ; Statement: $r12 = virtualinvoke $r11.<java.lang.Thread: java.lang.String getName()>() 
(assert true)
(define-const var2150 String (append/672562846 var1954 var2372)) ; Statement: $r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r12) 
(declare-const var1954!1 String)
(assert (= var1954!1 (str.++ var1954 var2372)))
(assert true)
(define-const var681 String (append/672562846 var2150 " MUST hold lock on ")) ; Statement: $r15 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(" MUST hold lock on ") 
(declare-const var2150!1 String)
(assert (= var2150!1 (str.++ var2150 " MUST hold lock on ")))
(assert true)
(define-const var2696 String (append/-1031950772 var681 (cast-from-var1860-to-var2096 var1401))) ; Statement: $r16 = virtualinvoke $r15.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r0) 
(declare-const var681!1 String)
(assert (str.prefixof var681 var681!1))
(assert true)
(define-const var2461 String (toString/-2075883882 var2696)) ; Statement: $r17 = virtualinvoke $r16.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert true)
;(assert (<init>/582965326 var2476 (cast-from-String-to-var2096 var2461))) ; Statement: specialinvoke $r9.<java.lang.AssertionError: void <init>(java.lang.Object)>($r17) 

(declare-const var2476!1 var3008)
(declare-const var2461!1 String)
 ; Statement: throw $r9 
(check-sat)


; {var1583_holdsLock/-145342167=([java.lang.Object], boolean), cast-from-var1860-to-var2096=([okhttp3.internal.concurrent.TaskRunner], java.lang.Object), var3008-init=([], java.lang.AssertionError), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), var1583_currentThread/-1037784612=([], java.lang.Thread), getName/-942182377=([java.lang.Thread], java.lang.String), append/-1031950772=([java.lang.StringBuilder, java.lang.Object], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), <init>/582965326=([java.lang.AssertionError, java.lang.Object], void), cast-from-String-to-var2096=([java.lang.String], java.lang.Object)}
; {var1860=okhttp3.internal.concurrent.TaskRunner, var1401=r0, var2845=okhttp3.internal.concurrent.Task, var2881=r1, var10=l0, var1168=okhttp3.internal.Util, var3317=$z0, var1583=java.lang.Thread, var2096=java.lang.Object, var1412=$z2, var3008=java.lang.AssertionError, var2476=$r9, var983=$r10, var1954=$r13, var1943=$r11, var2372=$r12, var2150=$r14, var681=$r15, var2696=$r16, var2461=$r17}
; {okhttp3.internal.concurrent.TaskRunner=var1860, r0=var1401, okhttp3.internal.concurrent.Task=var2845, r1=var2881, l0=var10, okhttp3.internal.Util=var1168, $z0=var3317, java.lang.Thread=var1583, java.lang.Object=var2096, $z2=var1412, java.lang.AssertionError=var3008, $r9=var2476, $r10=var983, $r13=var1954, $r11=var1943, $r12=var2372, $r14=var2150, $r15=var681, $r16=var2696, $r17=var2461}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 3,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r0 := @this: okhttp3.internal.concurrent.TaskRunner;	r1 := @parameter0: okhttp3.internal.concurrent.Task;	l0 := @parameter1: long;	$z0 = <okhttp3.internal.Util: boolean assertionsEnabled>;	if $z0 == 0 goto $r2 = virtualinvoke r1.<okhttp3.internal.concurrent.Task: okhttp3.internal.concurrent.TaskQueue getQueue$okhttp()>();	$z2 = staticinvoke <java.lang.Thread: boolean holdsLock(java.lang.Object)>(r0);	if $z2 != 0 goto $r2 = virtualinvoke r1.<okhttp3.internal.concurrent.Task: okhttp3.internal.concurrent.TaskQueue getQueue$okhttp()>();	$r9 = new java.lang.AssertionError;	$r10 = new java.lang.StringBuilder;	specialinvoke $r10.<java.lang.StringBuilder: void <init>()>();	$r13 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Thread ");	$r11 = staticinvoke <java.lang.Thread: java.lang.Thread currentThread()>();	$r12 = virtualinvoke $r11.<java.lang.Thread: java.lang.String getName()>();	$r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r12);	$r15 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(" MUST hold lock on ");	$r16 = virtualinvoke $r15.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r0);	$r17 = virtualinvoke $r16.<java.lang.StringBuilder: java.lang.String toString()>();	specialinvoke $r9.<java.lang.AssertionError: void <init>(java.lang.Object)>($r17);	throw $r9
;block_num 3