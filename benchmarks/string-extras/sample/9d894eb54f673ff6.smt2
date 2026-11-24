; origin: https://github.com/iscas-projects/SCB : hibernate-core/smt/method-org.hibernate.proxy.AbstractLazyInitializer__permissiveInitialization__-2014907070/31445.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var2377 0)
(declare-sort var2522 0)
(declare-sort var2895 0)
(declare-sort var3051 0)
(declare-sort var196 0)
(declare-sort var3041 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun session/752502022 (var2377) var2522)
(declare-fun var2522_isOpenOrWaitingForAutoClose/1945643444 (var2522) Bool)
(declare-fun var2895-init () var2895)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun entityName/752502022 (var2377) String)
(declare-fun id/752502022 (var2377) var3051)
(declare-fun append/-1031950772 (String var196) String)
(declare-fun cast-from-var3051-to-var196 (var3051) var196)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun <init>/1436286819 (var2895 String) void)
(declare-fun cast-from-var2895-to-var3041 (var2895) var3041)
(declare-const null-var2377 var2377)
(declare-const null-var2522 var2522)
(declare-const var3966 var2377) ; Statement: r0 := @this: org.hibernate.proxy.AbstractLazyInitializer 
(assert (not (= var3966 null-var2377)))
(define-const var1465 var2522 (session/752502022 var3966)) ; Statement: $r1 = r0.<org.hibernate.proxy.AbstractLazyInitializer: org.hibernate.engine.spi.SharedSessionContractImplementor session> 
 ; Statement: if $r1 != null goto $r2 = r0.<org.hibernate.proxy.AbstractLazyInitializer: org.hibernate.engine.spi.SharedSessionContractImplementor session> 
(assert (not (= var1465 null-var2522))) ; Cond: $r1 != null 
(define-const var2932 var2522 (session/752502022 var3966)) ; Statement: $r2 = r0.<org.hibernate.proxy.AbstractLazyInitializer: org.hibernate.engine.spi.SharedSessionContractImplementor session> 
(define-const var2199 Bool (var2522_isOpenOrWaitingForAutoClose/1945643444 var2932)) ; Statement: $z0 = interfaceinvoke $r2.<org.hibernate.engine.spi.SharedSessionContractImplementor: boolean isOpenOrWaitingForAutoClose()>() 
 ; Statement: if $z0 == 0 goto $r68 = new org.hibernate.LazyInitializationException 
(assert (= (ite var2199 1 0) 0)) ; Cond: $z0 == 0 
(define-const var1401 var2895 var2895-init) ; Statement: $r68 = new org.hibernate.LazyInitializationException 
(define-const var1425 String String-init) ; Statement: $r67 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var1425)) ; Statement: specialinvoke $r67.<java.lang.StringBuilder: void <init>()>() 
(declare-const var1425!1 String)
(assert (= var1425!1 ""))
(assert true)
(define-const var2446 String (append/672562846 var1425!1 "could not initialize proxy [")) ; Statement: $r6 = virtualinvoke $r67.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("could not initialize proxy [") 
(declare-const var1425!2 String)
(assert (= var1425!2 (str.++ var1425!1 "could not initialize proxy [")))
(define-const var3073 String (entityName/752502022 var3966)) ; Statement: $r5 = r0.<org.hibernate.proxy.AbstractLazyInitializer: java.lang.String entityName> 
(assert true)
(define-const var2357 String (append/672562846 var2446 var3073)) ; Statement: $r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r5) 
(declare-const var2446!1 String)
(assert (= var2446!1 (str.++ var2446 var3073)))
(assert true)
(define-const var3395 String (append/672562846 var2357 "#")) ; Statement: $r9 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("#") 
(declare-const var2357!1 String)
(assert (= var2357!1 (str.++ var2357 "#")))
(define-const var172 var3051 (id/752502022 var3966)) ; Statement: $r8 = r0.<org.hibernate.proxy.AbstractLazyInitializer: java.io.Serializable id> 
(assert true)
(define-const var1995 String (append/-1031950772 var3395 (cast-from-var3051-to-var196 var172))) ; Statement: $r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r8) 
(declare-const var3395!1 String)
(assert (str.prefixof var3395 var3395!1))
(assert true)
(define-const var3084 String (append/672562846 var1995 "] - Session was closed or disced")) ; Statement: $r11 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("] - Session was closed or disced") 
(declare-const var1995!1 String)
(assert (= var1995!1 (str.++ var1995 "] - Session was closed or disced")))
(assert true)
(define-const var529 String (toString/-2075883882 var3084)) ; Statement: $r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert true)
;(assert (<init>/1436286819 var1401 var529)) ; Statement: specialinvoke $r68.<org.hibernate.LazyInitializationException: void <init>(java.lang.String)>($r12) 

(declare-const var1401!1 var2895)
(declare-const var529!1 String)
(define-const var1809 var3041 (cast-from-var2895-to-var3041 var1401!1)) ; Statement: $r71 = (java.lang.Throwable) $r68 
 ; Statement: throw $r71 
(check-sat)


; {session/752502022=([org.hibernate.proxy.AbstractLazyInitializer], org.hibernate.engine.spi.SharedSessionContractImplementor), var2522_isOpenOrWaitingForAutoClose/1945643444=([org.hibernate.engine.spi.SharedSessionContractImplementor], boolean), var2895-init=([], org.hibernate.LazyInitializationException), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), entityName/752502022=([org.hibernate.proxy.AbstractLazyInitializer], java.lang.String), id/752502022=([org.hibernate.proxy.AbstractLazyInitializer], java.io.Serializable), append/-1031950772=([java.lang.StringBuilder, java.lang.Object], java.lang.StringBuilder), cast-from-var3051-to-var196=([java.io.Serializable], java.lang.Object), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), <init>/1436286819=([org.hibernate.LazyInitializationException, java.lang.String], void), cast-from-var2895-to-var3041=([org.hibernate.LazyInitializationException], java.lang.Throwable)}
; {var2377=org.hibernate.proxy.AbstractLazyInitializer, var3966=r0, var2522=org.hibernate.engine.spi.SharedSessionContractImplementor, var1465=$r1, var2932=$r2, var2199=$z0, var2895=org.hibernate.LazyInitializationException, var1401=$r68, var1425=$r67, var2446=$r6, var3073=$r5, var2357=$r7, var3395=$r9, var3051=java.io.Serializable, var172=$r8, var196=java.lang.Object, var1995=$r10, var3084=$r11, var529=$r12, var3041=java.lang.Throwable, var1809=$r71}
; {org.hibernate.proxy.AbstractLazyInitializer=var2377, r0=var3966, org.hibernate.engine.spi.SharedSessionContractImplementor=var2522, $r1=var1465, $r2=var2932, $z0=var2199, org.hibernate.LazyInitializationException=var2895, $r68=var1401, $r67=var1425, $r6=var2446, $r5=var3073, $r7=var2357, $r9=var3395, java.io.Serializable=var3051, $r8=var172, java.lang.Object=var196, $r10=var1995, $r11=var3084, $r12=var529, java.lang.Throwable=var3041, $r71=var1809}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 4,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r0 := @this: org.hibernate.proxy.AbstractLazyInitializer;	$r1 = r0.<org.hibernate.proxy.AbstractLazyInitializer: org.hibernate.engine.spi.SharedSessionContractImplementor session>;	if $r1 != null goto $r2 = r0.<org.hibernate.proxy.AbstractLazyInitializer: org.hibernate.engine.spi.SharedSessionContractImplementor session>;	$r2 = r0.<org.hibernate.proxy.AbstractLazyInitializer: org.hibernate.engine.spi.SharedSessionContractImplementor session>;	$z0 = interfaceinvoke $r2.<org.hibernate.engine.spi.SharedSessionContractImplementor: boolean isOpenOrWaitingForAutoClose()>();	if $z0 == 0 goto $r68 = new org.hibernate.LazyInitializationException;	$r68 = new org.hibernate.LazyInitializationException;	$r67 = new java.lang.StringBuilder;	specialinvoke $r67.<java.lang.StringBuilder: void <init>()>();	$r6 = virtualinvoke $r67.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("could not initialize proxy [");	$r5 = r0.<org.hibernate.proxy.AbstractLazyInitializer: java.lang.String entityName>;	$r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r5);	$r9 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("#");	$r8 = r0.<org.hibernate.proxy.AbstractLazyInitializer: java.io.Serializable id>;	$r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r8);	$r11 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("] - Session was closed or disced");	$r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.String toString()>();	specialinvoke $r68.<org.hibernate.LazyInitializationException: void <init>(java.lang.String)>($r12);	$r71 = (java.lang.Throwable) $r68;	throw $r71
;block_num 3