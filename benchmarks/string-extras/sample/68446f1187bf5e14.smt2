; origin: https://github.com/iscas-projects/SCB : hibernate-core/smt/method-org.hibernate.dialect.lock.OptimisticLockingStrategy__《init》__1503000268/14447.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3539 0)
(declare-sort var1957 0)
(declare-sort var2109 0)
(declare-sort var3081 0)
(declare-sort var1802 0)
(declare-sort var3981 0)
(declare-sort var3216 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun <init>/-279557996 (var3081) void)
(declare-fun cast-from-var3539-to-var3081 (var3539) var3081)
(declare-fun lockable/-1546105400 (var3539) var1957)
(declare-fun lockMode/-1546105400 (var3539) var2109)
(declare-fun lessThan/186053417 (var2109 var2109) Bool)
(declare-fun var1802-init () var1802)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun append/-1031950772 (String var3081) String)
(declare-fun cast-from-var2109-to-var3081 (var2109) var3081)
(declare-fun var3981_getEntityName/-1914780628 (var3981) String)
(declare-fun cast-from-var1957-to-var3981 (var1957) var3981)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun <init>/-790357943 (var1802 String) void)
(declare-fun cast-from-var1802-to-var3216 (var1802) var3216)
(declare-const null-var3539 var3539)
(declare-const null-var1957 var1957)
(declare-const null-var2109 var2109)
(declare-const var2109-OPTIMISTIC var2109)
(declare-const var122 var3539) ; Statement: r0 := @this: org.hibernate.dialect.lock.OptimisticLockingStrategy 
(assert (not (= var122 null-var3539)))
(declare-const var3841 var1957) ; Statement: r1 := @parameter0: org.hibernate.persister.entity.Lockable 
(assert (not (= var3841 null-var1957)))
(declare-const var226 var2109) ; Statement: r2 := @parameter1: org.hibernate.LockMode 
(assert (not (= var226 null-var2109)))
(assert true)
;(assert (<init>/-279557996 (cast-from-var3539-to-var3081 var122))) ; Statement: specialinvoke r0.<java.lang.Object: void <init>()>() 

(declare-const var122!1 var3539)
(declare-const var122!2 var3539)
(assert (not (= var122!2 null-var3539)))
(assert (= (lockable/-1546105400 var122!2) var3841)) ; Statement: r0.<org.hibernate.dialect.lock.OptimisticLockingStrategy: org.hibernate.persister.entity.Lockable lockable> = r1 
(declare-const var122!3 var3539)
(assert (not (= var122!3 null-var3539)))
(assert (= (lockMode/-1546105400 var122!3) var226)) ; Statement: r0.<org.hibernate.dialect.lock.OptimisticLockingStrategy: org.hibernate.LockMode lockMode> = r2 
(define-const var3257 var2109 var2109-OPTIMISTIC) ; Statement: $r3 = <org.hibernate.LockMode: org.hibernate.LockMode OPTIMISTIC> 
(assert true)
(define-const var2114 Bool (lessThan/186053417 var226 var3257)) ; Statement: $z0 = virtualinvoke r2.<org.hibernate.LockMode: boolean lessThan(org.hibernate.LockMode)>($r3) 
 ; Statement: if $z0 == 0 goto return 
(assert (not (= (ite var2114 1 0) 0))) ; Negate: Cond: $z0 == 0  
(define-const var1270 var1802 var1802-init) ; Statement: $r14 = new org.hibernate.HibernateException 
(define-const var1575 String String-init) ; Statement: $r13 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var1575)) ; Statement: specialinvoke $r13.<java.lang.StringBuilder: void <init>()>() 
(declare-const var1575!1 String)
(assert (= var1575!1 ""))
(assert true)
(define-const var770 String (append/672562846 var1575!1 "[")) ; Statement: $r6 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("[") 
(declare-const var1575!2 String)
(assert (= var1575!2 (str.++ var1575!1 "[")))
(assert true)
(define-const var2130 String (append/-1031950772 var770 (cast-from-var2109-to-var3081 var226))) ; Statement: $r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r2) 
(declare-const var770!1 String)
(assert (str.prefixof var770 var770!1))
(assert true)
(define-const var477 String (append/672562846 var2130 "] not valid for [")) ; Statement: $r9 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("] not valid for [") 
(declare-const var2130!1 String)
(assert (= var2130!1 (str.++ var2130 "] not valid for [")))
(define-const var3617 String (var3981_getEntityName/-1914780628 (cast-from-var1957-to-var3981 var3841))) ; Statement: $r8 = interfaceinvoke r1.<org.hibernate.persister.entity.Lockable: java.lang.String getEntityName()>() 
(assert true)
(define-const var2954 String (append/672562846 var477 var3617)) ; Statement: $r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r8) 
(declare-const var477!1 String)
(assert (= var477!1 (str.++ var477 var3617)))
(assert true)
(define-const var3472 String (append/672562846 var2954 "]")) ; Statement: $r11 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("]") 
(declare-const var2954!1 String)
(assert (= var2954!1 (str.++ var2954 "]")))
(assert true)
(define-const var1480 String (toString/-2075883882 var3472)) ; Statement: $r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert true)
;(assert (<init>/-790357943 var1270 var1480)) ; Statement: specialinvoke $r14.<org.hibernate.HibernateException: void <init>(java.lang.String)>($r12) 

(declare-const var1270!1 var1802)
(declare-const var1480!1 String)
(define-const var3249 var3216 (cast-from-var1802-to-var3216 var1270!1)) ; Statement: $r15 = (java.lang.Throwable) $r14 
 ; Statement: throw $r15 
(check-sat)


; {<init>/-279557996=([java.lang.Object], void), cast-from-var3539-to-var3081=([org.hibernate.dialect.lock.OptimisticLockingStrategy], java.lang.Object), lockable/-1546105400=([org.hibernate.dialect.lock.OptimisticLockingStrategy], org.hibernate.persister.entity.Lockable), lockMode/-1546105400=([org.hibernate.dialect.lock.OptimisticLockingStrategy], org.hibernate.LockMode), lessThan/186053417=([org.hibernate.LockMode, org.hibernate.LockMode], boolean), var1802-init=([], org.hibernate.HibernateException), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), append/-1031950772=([java.lang.StringBuilder, java.lang.Object], java.lang.StringBuilder), cast-from-var2109-to-var3081=([org.hibernate.LockMode], java.lang.Object), var3981_getEntityName/-1914780628=([org.hibernate.persister.entity.EntityPersister], java.lang.String), cast-from-var1957-to-var3981=([org.hibernate.persister.entity.Lockable], org.hibernate.persister.entity.EntityPersister), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), <init>/-790357943=([org.hibernate.HibernateException, java.lang.String], void), cast-from-var1802-to-var3216=([org.hibernate.HibernateException], java.lang.Throwable)}
; {var3539=org.hibernate.dialect.lock.OptimisticLockingStrategy, var122=r0, var1957=org.hibernate.persister.entity.Lockable, var3841=r1, var2109=org.hibernate.LockMode, var226=r2, var3081=java.lang.Object, var3257=$r3, var2114=$z0, var1802=org.hibernate.HibernateException, var1270=$r14, var1575=$r13, var770=$r6, var2130=$r7, var477=$r9, var3981=org.hibernate.persister.entity.EntityPersister, var3617=$r8, var2954=$r10, var3472=$r11, var1480=$r12, var3216=java.lang.Throwable, var3249=$r15}
; {org.hibernate.dialect.lock.OptimisticLockingStrategy=var3539, r0=var122, org.hibernate.persister.entity.Lockable=var1957, r1=var3841, org.hibernate.LockMode=var2109, r2=var226, java.lang.Object=var3081, $r3=var3257, $z0=var2114, org.hibernate.HibernateException=var1802, $r14=var1270, $r13=var1575, $r6=var770, $r7=var2130, $r9=var477, org.hibernate.persister.entity.EntityPersister=var3981, $r8=var3617, $r10=var2954, $r11=var3472, $r12=var1480, java.lang.Throwable=var3216, $r15=var3249}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 4,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r0 := @this: org.hibernate.dialect.lock.OptimisticLockingStrategy;	r1 := @parameter0: org.hibernate.persister.entity.Lockable;	r2 := @parameter1: org.hibernate.LockMode;	specialinvoke r0.<java.lang.Object: void <init>()>();	r0.<org.hibernate.dialect.lock.OptimisticLockingStrategy: org.hibernate.persister.entity.Lockable lockable> = r1;	r0.<org.hibernate.dialect.lock.OptimisticLockingStrategy: org.hibernate.LockMode lockMode> = r2;	$r3 = <org.hibernate.LockMode: org.hibernate.LockMode OPTIMISTIC>;	$z0 = virtualinvoke r2.<org.hibernate.LockMode: boolean lessThan(org.hibernate.LockMode)>($r3);	if $z0 == 0 goto return;	$r14 = new org.hibernate.HibernateException;	$r13 = new java.lang.StringBuilder;	specialinvoke $r13.<java.lang.StringBuilder: void <init>()>();	$r6 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("[");	$r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r2);	$r9 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("] not valid for [");	$r8 = interfaceinvoke r1.<org.hibernate.persister.entity.Lockable: java.lang.String getEntityName()>();	$r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r8);	$r11 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("]");	$r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.String toString()>();	specialinvoke $r14.<org.hibernate.HibernateException: void <init>(java.lang.String)>($r12);	$r15 = (java.lang.Throwable) $r14;	throw $r15
;block_num 2