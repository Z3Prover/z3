; origin: https://github.com/iscas-projects/SCB : hibernate-core/smt/method-org.hibernate.dialect.function.PositionSubstringFunction__render__985240504/14163.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var1029 0)
(declare-sort var753 0)
(declare-sort var3610 0)
(declare-sort var2319 0)
(declare-sort var2075 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun var3610_size/-959786421 (var3610) Int)
(declare-fun var3610_get/-1216255739 (var3610 Int) var2075)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun append/-1031950772 (String var2075) String)
(declare-fun append/-1166366385 (String Int) String)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-const null-var1029 var1029)
(declare-const null-var753 var753)
(declare-const null-var3610 var3610)
(declare-const null-var2319 var2319)
(declare-const var315 var1029) ; Statement: r12 := @this: org.hibernate.dialect.function.PositionSubstringFunction 
(assert (not (= var315 null-var1029)))
(declare-const var3548 var753) ; Statement: r13 := @parameter0: org.hibernate.type.Type 
(assert (not (= var3548 null-var753)))
(declare-const var818 var3610) ; Statement: r0 := @parameter1: java.util.List 
(assert (not (= var818 null-var3610)))
(declare-const var3379 var2319) ; Statement: r14 := @parameter2: org.hibernate.engine.spi.SessionFactoryImplementor 
(assert (not (= var3379 null-var2319)))
(define-const var520 Int (var3610_size/-959786421 var818)) ; Statement: $i0 = interfaceinvoke r0.<java.util.List: int size()>() 
 ; Statement: if $i0 <= 2 goto $z3 = 0 
(assert (not (<= var520 2))) ; Negate: Cond: $i0 <= 2  
(define-const var2366 Bool (ite (= 1 1) true false)) ; Statement: $z3 = 1 
(define-const var501 Bool (ite (= 1 1) true false)) ; Statement: $z2 = 1 
 ; Statement: goto [?= z0 = $z2] 
(assert true) ; Non Conditional
(define-const var33 Bool var501) ; Statement: z0 = $z2 
(define-const var1436 var2075 (var3610_get/-1216255739 var818 0)) ; Statement: $r10 = interfaceinvoke r0.<java.util.List: java.lang.Object get(int)>(0) 
(define-const var656 var2075 (var3610_get/-1216255739 var818 1)) ; Statement: $r11 = interfaceinvoke r0.<java.util.List: java.lang.Object get(int)>(1) 
 ; Statement: if $z3 == 0 goto $r15 = null 
(assert (not (= (ite var2366 1 0) 0))) ; Negate: Cond: $z3 == 0  
(define-const var1936 var2075 (var3610_get/-1216255739 var818 2)) ; Statement: $r15 = interfaceinvoke r0.<java.util.List: java.lang.Object get(int)>(2) 
 ; Statement: goto [?= r1 = $r15] 
(assert true) ; Non Conditional
(define-const var1970 var2075 var1936) ; Statement: r1 = $r15 
(define-const var2001 String String-init) ; Statement: $r2 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var2001)) ; Statement: specialinvoke $r2.<java.lang.StringBuilder: void <init>()>() 
(declare-const var2001!1 String)
(assert (= var2001!1 ""))
 ; Statement: if z0 == 0 goto $r3 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("position(") 
(assert (= (ite var33 1 0) 0)) ; Cond: z0 == 0 
(assert true)
(define-const var294 String (append/672562846 var2001!1 "position(")) ; Statement: $r3 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("position(") 
(declare-const var2001!2 String)
(assert (= var2001!2 (str.++ var2001!1 "position(")))
(assert true)
(define-const var973 String (append/-1031950772 var294 var1436)) ; Statement: $r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r10) 
(declare-const var294!1 String)
(assert (str.prefixof var294 var294!1))
(assert true)
;(assert (append/672562846 var973 " in ")) ; Statement: virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(" in ") 
(declare-const var973!1 String)
(assert (= var973!1 (str.++ var973 " in ")))
 ; Statement: if z0 == 0 goto virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r11) 
(assert (= (ite var33 1 0) 0)) ; Cond: z0 == 0 
(assert true)
;(assert (append/-1031950772 var2001!2 var656)) ; Statement: virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r11) 
(declare-const var2001!3 String)
(assert (str.prefixof var2001!2 var2001!3))
 ; Statement: if z0 == 0 goto virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(41) 
(assert (= (ite var33 1 0) 0)) ; Cond: z0 == 0 
(assert true)
;(assert (append/-1166366385 var2001!3 41)) ; Statement: virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(41) 
(declare-const var2001!4 String)
(assert (str.prefixof var2001!3 var2001!4))
 ; Statement: if z0 == 0 goto $r5 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert (= (ite var33 1 0) 0)) ; Cond: z0 == 0 
(assert true)
(define-const var3032 String (toString/-2075883882 var2001!4)) ; Statement: $r5 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.String toString()>() 
 ; Statement: return $r5 
(check-sat)


; {var3610_size/-959786421=([java.util.List], int), var3610_get/-1216255739=([java.util.List, int], java.lang.Object), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), append/-1031950772=([java.lang.StringBuilder, java.lang.Object], java.lang.StringBuilder), append/-1166366385=([java.lang.StringBuilder, char], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String)}
; {var1029=org.hibernate.dialect.function.PositionSubstringFunction, var315=r12, var753=org.hibernate.type.Type, var3548=r13, var3610=java.util.List, var818=r0, var2319=org.hibernate.engine.spi.SessionFactoryImplementor, var3379=r14, var520=$i0, var2366=$z3, var501=$z2, var33=z0, var2075=java.lang.Object, var1436=$r10, var656=$r11, var1936=$r15, var1970=r1, var2001=$r2, var294=$r3, var973=$r4, var3032=$r5}
; {org.hibernate.dialect.function.PositionSubstringFunction=var1029, r12=var315, org.hibernate.type.Type=var753, r13=var3548, java.util.List=var3610, r0=var818, org.hibernate.engine.spi.SessionFactoryImplementor=var2319, r14=var3379, $i0=var520, $z3=var2366, $z2=var501, z0=var33, java.lang.Object=var2075, $r10=var1436, $r11=var656, $r15=var1936, r1=var1970, $r2=var2001, $r3=var294, $r4=var973, $r5=var3032}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(char)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 2,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>": 2,"<java.lang.StringBuilder: java.lang.StringBuilder append(char)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r12 := @this: org.hibernate.dialect.function.PositionSubstringFunction;	r13 := @parameter0: org.hibernate.type.Type;	r0 := @parameter1: java.util.List;	r14 := @parameter2: org.hibernate.engine.spi.SessionFactoryImplementor;	$i0 = interfaceinvoke r0.<java.util.List: int size()>();	if $i0 <= 2 goto $z3 = 0;	$z3 = 1;	$z2 = 1;	goto [?= z0 = $z2];	z0 = $z2;	$r10 = interfaceinvoke r0.<java.util.List: java.lang.Object get(int)>(0);	$r11 = interfaceinvoke r0.<java.util.List: java.lang.Object get(int)>(1);	if $z3 == 0 goto $r15 = null;	$r15 = interfaceinvoke r0.<java.util.List: java.lang.Object get(int)>(2);	goto [?= r1 = $r15];	r1 = $r15;	$r2 = new java.lang.StringBuilder;	specialinvoke $r2.<java.lang.StringBuilder: void <init>()>();	if z0 == 0 goto $r3 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("position(");	$r3 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("position(");	$r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r10);	virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(" in ");	if z0 == 0 goto virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r11);	virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r11);	if z0 == 0 goto virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(41);	virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(41);	if z0 == 0 goto $r5 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.String toString()>();	$r5 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.String toString()>();	return $r5
;block_num 9