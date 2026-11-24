; origin: https://github.com/iscas-projects/SCB : hibernate-core/smt/method-org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject__《init》__344421997/5221.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var1922 0)
(declare-sort var756 0)
(declare-sort var3653 0)
(declare-sort var3963 0)
(declare-sort var1045 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun <init>/-279557996 (var3653) void)
(declare-fun cast-from-var1922-to-var3653 (var1922) var3653)
(declare-fun beforeTables/83599698 (var1922) Bool)
(declare-fun var3963-init () var3963)
(declare-fun cast-from-var3963-to-var756 (var3963) var756)
(declare-fun <init>/451842749 (var3963) void)
(declare-fun dialectScopes/83599698 (var1922) var756)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun getAndIncrement/-721914959 (var1045) Int)
(define-fun append/-1001720160 ((s String) (tail Int)) String (str.++ s (str.from_int tail)))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun exportIdentifier/83599698 (var1922) String)
(declare-const null-var1922 var1922)
(declare-const null-Bool Bool)
(declare-const null-var756 var756)
(declare-const var1922-counter var1045)
(declare-const var2943 var1922) ; Statement: r0 := @this: org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject 
(assert (not (= var2943 null-var1922)))
(declare-const var1548 Bool) ; Statement: z0 := @parameter0: boolean 
(assert (not (= var1548 null-Bool)))
(declare-const var150 var756) ; Statement: r1 := @parameter1: java.util.Set 
(assert (not (= var150 null-var756)))
(assert true)
;(assert (<init>/-279557996 (cast-from-var1922-to-var3653 var2943))) ; Statement: specialinvoke r0.<java.lang.Object: void <init>()>() 

(declare-const var2943!1 var1922)
(declare-const var2943!2 var1922)
(assert (not (= var2943!2 null-var1922)))
(assert (= (beforeTables/83599698 var2943!2) var1548)) ; Statement: r0.<org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject: boolean beforeTables> = z0 
 ; Statement: if r1 != null goto $r7 = r1 
(assert (not (not (= var150 null-var756)))) ; Negate: Cond: r1 != null  
(define-const var1914 var3963 var3963-init) ; Statement: $r8 = new java.util.HashSet 
(define-const var3687 var756 (cast-from-var3963-to-var756 var1914)) ; Statement: $r7 = $r8 
(assert true)
;(assert (<init>/451842749 var1914)) ; Statement: specialinvoke $r8.<java.util.HashSet: void <init>()>() 

(declare-const var1914!1 var3963)
 ; Statement: goto [?= r0.<org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject: java.util.Set dialectScopes> = $r7] 
(assert true) ; Non Conditional
(declare-const var2943!3 var1922)
(assert (not (= var2943!3 null-var1922)))
(assert (= (dialectScopes/83599698 var2943!3) var3687)) ; Statement: r0.<org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject: java.util.Set dialectScopes> = $r7 
(define-const var3191 String String-init) ; Statement: $r9 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var3191)) ; Statement: specialinvoke $r9.<java.lang.StringBuilder: void <init>()>() 
(declare-const var3191!1 String)
(assert (= var3191!1 ""))
(assert true)
(define-const var570 String (append/672562846 var3191!1 "auxiliary-object-.")) ; Statement: $r4 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("auxiliary-object-.") 
(declare-const var3191!2 String)
(assert (= var3191!2 (str.++ var3191!1 "auxiliary-object-.")))
(define-const var690 var1045 var1922-counter) ; Statement: $r3 = <org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject: java.util.concurrent.atomic.AtomicInteger counter> 
(assert true)
(define-const var473 Int (getAndIncrement/-721914959 var690)) ; Statement: $i0 = virtualinvoke $r3.<java.util.concurrent.atomic.AtomicInteger: int getAndIncrement()>() 
(assert true)
(define-const var220 String (append/-1001720160 var570 var473)) ; Statement: $r5 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i0) 
(declare-const var570!1 String)
(assert (str.prefixof var570 var570!1))
(assert true)
(define-const var1638 String (toString/-2075883882 var220)) ; Statement: $r6 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.String toString()>() 
(declare-const var2943!4 var1922)
(assert (not (= var2943!4 null-var1922)))
(assert (= (exportIdentifier/83599698 var2943!4) var1638)) ; Statement: r0.<org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject: java.lang.String exportIdentifier> = $r6 
 ; Statement: return 
(check-sat)


; {<init>/-279557996=([java.lang.Object], void), cast-from-var1922-to-var3653=([org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject], java.lang.Object), beforeTables/83599698=([org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject], boolean), var3963-init=([], java.util.HashSet), cast-from-var3963-to-var756=([java.util.HashSet], java.util.Set), <init>/451842749=([java.util.HashSet], void), dialectScopes/83599698=([org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject], java.util.Set), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), getAndIncrement/-721914959=([java.util.concurrent.atomic.AtomicInteger], int), append/-1001720160=([java.lang.StringBuilder, int], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), exportIdentifier/83599698=([org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject], java.lang.String)}
; {var1922=org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject, var2943=r0, var1548=z0, var756=java.util.Set, var150=r1, var3653=java.lang.Object, var3963=java.util.HashSet, var1914=$r8, var3687=$r7, var3191=$r9, var570=$r4, var1045=java.util.concurrent.atomic.AtomicInteger, var690=$r3, var473=$i0, var220=$r5, var1638=$r6}
; {org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject=var1922, r0=var2943, z0=var1548, java.util.Set=var756, r1=var150, java.lang.Object=var3653, java.util.HashSet=var3963, $r8=var1914, $r7=var3687, $r9=var3191, $r4=var570, java.util.concurrent.atomic.AtomicInteger=var1045, $r3=var690, $i0=var473, $r5=var220, $r6=var1638}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(int)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(int)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r0 := @this: org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject;	z0 := @parameter0: boolean;	r1 := @parameter1: java.util.Set;	specialinvoke r0.<java.lang.Object: void <init>()>();	r0.<org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject: boolean beforeTables> = z0;	if r1 != null goto $r7 = r1;	$r8 = new java.util.HashSet;	$r7 = $r8;	specialinvoke $r8.<java.util.HashSet: void <init>()>();	goto [?= r0.<org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject: java.util.Set dialectScopes> = $r7];	r0.<org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject: java.util.Set dialectScopes> = $r7;	$r9 = new java.lang.StringBuilder;	specialinvoke $r9.<java.lang.StringBuilder: void <init>()>();	$r4 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("auxiliary-object-.");	$r3 = <org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject: java.util.concurrent.atomic.AtomicInteger counter>;	$i0 = virtualinvoke $r3.<java.util.concurrent.atomic.AtomicInteger: int getAndIncrement()>();	$r5 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i0);	$r6 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.String toString()>();	r0.<org.hibernate.boot.model.relational.AbstractAuxiliaryDatabaseObject: java.lang.String exportIdentifier> = $r6;	return
;block_num 3