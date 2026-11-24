; origin: https://github.com/iscas-projects/SCB : lombok/smt/method-lombok.launch.ShadowClassLoader__isPartOfShadowSuffix__-364801487/477-deviant-0.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var1503 0)
(declare-sort var1556 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(define-fun startsWith/-1785782452 ((s String) (prefix String)) Bool (str.prefixof prefix s))
(define-fun substring/850833817 ((s String) (begin Int)) String (str.substr s begin (- (str.len s) begin)))
(declare-fun var1503_urlDecode/-772833716 (String) String)
(define-fun length/-134980193 ((s String)) Int (str.len s))
(declare-const null-var1503 var1503)
(declare-const null-String String)
(declare-const var2523 var1503) ; Statement: r1 := @this: lombok.launch.ShadowClassLoader 
(assert (not (= var2523 null-var1503)))
(declare-const var2827 String) ; Statement: r5 := @parameter0: java.lang.String 
(assert (not (= var2827 null-String)))
(declare-const var2477 String) ; Statement: r4 := @parameter1: java.lang.String 
(assert (not (= var2477 null-String)))
(declare-const var563 String) ; Statement: r2 := @parameter2: java.lang.String 
(assert (not (= var563 null-String)))
 ; Statement: if r5 != null goto $z0 = virtualinvoke r5.<java.lang.String: boolean startsWith(java.lang.String)>("file:/") 
(assert (not (= var2827 null-String))) ; Cond: r5 != null 
(assert true)
(define-const var3530 Bool (startsWith/-1785782452 var2827 "file:/")) ; Statement: $z0 = virtualinvoke r5.<java.lang.String: boolean startsWith(java.lang.String)>("file:/") 
 ; Statement: if $z0 == 0 goto $z1 = virtualinvoke r5.<java.lang.String: boolean startsWith(java.lang.String)>("jar:") 
(assert (not (= (ite var3530 1 0) 0))) ; Negate: Cond: $z0 == 0  
(assert (not (and true (and (>= 5 0) (>= (str.len var2827) 5)))))
(check-sat)


; {startsWith/-1785782452=([java.lang.String, java.lang.String], boolean), substring/850833817=([java.lang.String, int], java.lang.String), var1503_urlDecode/-772833716=([java.lang.String], java.lang.String), length/-134980193=([java.lang.String], int)}
; {var1503=lombok.launch.ShadowClassLoader, var2523=r1, var2827=r5, var1556=null_type, var2477=r4, var563=r2, var3530=$z0, var292=$r3, var1478=r6, var2580=$i1, var3043=$i0}
; {lombok.launch.ShadowClassLoader=var1503, r1=var2523, r5=var2827, null_type=var1556, r4=var2477, r2=var563, $z0=var3530, $r3=var292, r6=var1478, $i1=var2580, $i0=var3043}
;seq <java.lang.String: boolean startsWith(java.lang.String)>;	<java.lang.String: java.lang.String substring(int)>;	<java.lang.String: int length()>;	<java.lang.String: int length()>
;cnt {"<java.lang.String: boolean startsWith(java.lang.String)>": 1,"<java.lang.String: java.lang.String substring(int)>": 1,"<java.lang.String: int length()>": 2}
;stmts r1 := @this: lombok.launch.ShadowClassLoader;	r5 := @parameter0: java.lang.String;	r4 := @parameter1: java.lang.String;	r2 := @parameter2: java.lang.String;	if r5 != null goto $z0 = virtualinvoke r5.<java.lang.String: boolean startsWith(java.lang.String)>("file:/");	$z0 = virtualinvoke r5.<java.lang.String: boolean startsWith(java.lang.String)>("file:/");	if $z0 == 0 goto $z1 = virtualinvoke r5.<java.lang.String: boolean startsWith(java.lang.String)>("jar:");	$r3 = virtualinvoke r5.<java.lang.String: java.lang.String substring(int)>(5);	r6 = staticinvoke <lombok.launch.ShadowClassLoader: java.lang.String urlDecode(java.lang.String)>($r3);	$i1 = virtualinvoke r6.<java.lang.String: int length()>();	$i0 = virtualinvoke r4.<java.lang.String: int length()>();	if $i1 <= $i0 goto return 0;	return 0
;block_num 4