; origin: https://github.com/iscas-projects/SCB : hibernate-core/smt/method-org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy__《init》__-543736088/14446.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var723 0)
(declare-sort var2165 0)
(declare-sort var1277 0)
(declare-sort var2841 0)
(declare-sort var3308 0)
(declare-sort var734 0)
(declare-sort var3362 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun <init>/-279557996 (var2841) void)
(declare-fun cast-from-var723-to-var2841 (var723) var2841)
(declare-fun lockable/-934989852 (var723) var2165)
(declare-fun lockMode/-934989852 (var723) var1277)
(declare-fun lessThan/186053417 (var1277 var1277) Bool)
(declare-fun var3308-init () var3308)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun append/-1031950772 (String var2841) String)
(declare-fun cast-from-var1277-to-var2841 (var1277) var2841)
(declare-fun var734_getEntityName/-1914780628 (var734) String)
(declare-fun cast-from-var2165-to-var734 (var2165) var734)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun <init>/-790357943 (var3308 String) void)
(declare-fun cast-from-var3308-to-var3362 (var3308) var3362)
(declare-const null-var723 var723)
(declare-const null-var2165 var2165)
(declare-const null-var1277 var1277)
(declare-const var1277-OPTIMISTIC_FORCE_INCREMENT var1277)
(declare-const var2346 var723) ; Statement: r0 := @this: org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy 
(assert (not (= var2346 null-var723)))
(declare-const var3051 var2165) ; Statement: r1 := @parameter0: org.hibernate.persister.entity.Lockable 
(assert (not (= var3051 null-var2165)))
(declare-const var3145 var1277) ; Statement: r2 := @parameter1: org.hibernate.LockMode 
(assert (not (= var3145 null-var1277)))
(assert true)
;(assert (<init>/-279557996 (cast-from-var723-to-var2841 var2346))) ; Statement: specialinvoke r0.<java.lang.Object: void <init>()>() 

(declare-const var2346!1 var723)
(declare-const var2346!2 var723)
(assert (not (= var2346!2 null-var723)))
(assert (= (lockable/-934989852 var2346!2) var3051)) ; Statement: r0.<org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy: org.hibernate.persister.entity.Lockable lockable> = r1 
(declare-const var2346!3 var723)
(assert (not (= var2346!3 null-var723)))
(assert (= (lockMode/-934989852 var2346!3) var3145)) ; Statement: r0.<org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy: org.hibernate.LockMode lockMode> = r2 
(define-const var547 var1277 var1277-OPTIMISTIC_FORCE_INCREMENT) ; Statement: $r3 = <org.hibernate.LockMode: org.hibernate.LockMode OPTIMISTIC_FORCE_INCREMENT> 
(assert true)
(define-const var3366 Bool (lessThan/186053417 var3145 var547)) ; Statement: $z0 = virtualinvoke r2.<org.hibernate.LockMode: boolean lessThan(org.hibernate.LockMode)>($r3) 
 ; Statement: if $z0 == 0 goto return 
(assert (not (= (ite var3366 1 0) 0))) ; Negate: Cond: $z0 == 0  
(define-const var3931 var3308 var3308-init) ; Statement: $r14 = new org.hibernate.HibernateException 
(define-const var1300 String String-init) ; Statement: $r13 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var1300)) ; Statement: specialinvoke $r13.<java.lang.StringBuilder: void <init>()>() 
(declare-const var1300!1 String)
(assert (= var1300!1 ""))
(assert true)
(define-const var843 String (append/672562846 var1300!1 "[")) ; Statement: $r6 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("[") 
(declare-const var1300!2 String)
(assert (= var1300!2 (str.++ var1300!1 "[")))
(assert true)
(define-const var1138 String (append/-1031950772 var843 (cast-from-var1277-to-var2841 var3145))) ; Statement: $r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r2) 
(declare-const var843!1 String)
(assert (str.prefixof var843 var843!1))
(assert true)
(define-const var1880 String (append/672562846 var1138 "] not valid for [")) ; Statement: $r9 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("] not valid for [") 
(declare-const var1138!1 String)
(assert (= var1138!1 (str.++ var1138 "] not valid for [")))
(define-const var1847 String (var734_getEntityName/-1914780628 (cast-from-var2165-to-var734 var3051))) ; Statement: $r8 = interfaceinvoke r1.<org.hibernate.persister.entity.Lockable: java.lang.String getEntityName()>() 
(assert true)
(define-const var2594 String (append/672562846 var1880 var1847)) ; Statement: $r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r8) 
(declare-const var1880!1 String)
(assert (= var1880!1 (str.++ var1880 var1847)))
(assert true)
(define-const var1758 String (append/672562846 var2594 "]")) ; Statement: $r11 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("]") 
(declare-const var2594!1 String)
(assert (= var2594!1 (str.++ var2594 "]")))
(assert true)
(define-const var1228 String (toString/-2075883882 var1758)) ; Statement: $r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert true)
;(assert (<init>/-790357943 var3931 var1228)) ; Statement: specialinvoke $r14.<org.hibernate.HibernateException: void <init>(java.lang.String)>($r12) 

(declare-const var3931!1 var3308)
(declare-const var1228!1 String)
(define-const var2707 var3362 (cast-from-var3308-to-var3362 var3931!1)) ; Statement: $r15 = (java.lang.Throwable) $r14 
 ; Statement: throw $r15 
(check-sat)


; {<init>/-279557996=([java.lang.Object], void), cast-from-var723-to-var2841=([org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy], java.lang.Object), lockable/-934989852=([org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy], org.hibernate.persister.entity.Lockable), lockMode/-934989852=([org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy], org.hibernate.LockMode), lessThan/186053417=([org.hibernate.LockMode, org.hibernate.LockMode], boolean), var3308-init=([], org.hibernate.HibernateException), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), append/-1031950772=([java.lang.StringBuilder, java.lang.Object], java.lang.StringBuilder), cast-from-var1277-to-var2841=([org.hibernate.LockMode], java.lang.Object), var734_getEntityName/-1914780628=([org.hibernate.persister.entity.EntityPersister], java.lang.String), cast-from-var2165-to-var734=([org.hibernate.persister.entity.Lockable], org.hibernate.persister.entity.EntityPersister), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), <init>/-790357943=([org.hibernate.HibernateException, java.lang.String], void), cast-from-var3308-to-var3362=([org.hibernate.HibernateException], java.lang.Throwable)}
; {var723=org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy, var2346=r0, var2165=org.hibernate.persister.entity.Lockable, var3051=r1, var1277=org.hibernate.LockMode, var3145=r2, var2841=java.lang.Object, var547=$r3, var3366=$z0, var3308=org.hibernate.HibernateException, var3931=$r14, var1300=$r13, var843=$r6, var1138=$r7, var1880=$r9, var734=org.hibernate.persister.entity.EntityPersister, var1847=$r8, var2594=$r10, var1758=$r11, var1228=$r12, var3362=java.lang.Throwable, var2707=$r15}
; {org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy=var723, r0=var2346, org.hibernate.persister.entity.Lockable=var2165, r1=var3051, org.hibernate.LockMode=var1277, r2=var3145, java.lang.Object=var2841, $r3=var547, $z0=var3366, org.hibernate.HibernateException=var3308, $r14=var3931, $r13=var1300, $r6=var843, $r7=var1138, $r9=var1880, org.hibernate.persister.entity.EntityPersister=var734, $r8=var1847, $r10=var2594, $r11=var1758, $r12=var1228, java.lang.Throwable=var3362, $r15=var2707}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 4,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r0 := @this: org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy;	r1 := @parameter0: org.hibernate.persister.entity.Lockable;	r2 := @parameter1: org.hibernate.LockMode;	specialinvoke r0.<java.lang.Object: void <init>()>();	r0.<org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy: org.hibernate.persister.entity.Lockable lockable> = r1;	r0.<org.hibernate.dialect.lock.OptimisticForceIncrementLockingStrategy: org.hibernate.LockMode lockMode> = r2;	$r3 = <org.hibernate.LockMode: org.hibernate.LockMode OPTIMISTIC_FORCE_INCREMENT>;	$z0 = virtualinvoke r2.<org.hibernate.LockMode: boolean lessThan(org.hibernate.LockMode)>($r3);	if $z0 == 0 goto return;	$r14 = new org.hibernate.HibernateException;	$r13 = new java.lang.StringBuilder;	specialinvoke $r13.<java.lang.StringBuilder: void <init>()>();	$r6 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("[");	$r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r2);	$r9 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("] not valid for [");	$r8 = interfaceinvoke r1.<org.hibernate.persister.entity.Lockable: java.lang.String getEntityName()>();	$r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r8);	$r11 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("]");	$r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.String toString()>();	specialinvoke $r14.<org.hibernate.HibernateException: void <init>(java.lang.String)>($r12);	$r15 = (java.lang.Throwable) $r14;	throw $r15
;block_num 2