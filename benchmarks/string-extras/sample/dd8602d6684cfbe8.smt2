; origin: https://github.com/iscas-projects/SCB : mybatis/smt/method-org.apache.ibatis.javassist.tools.reflect.ClassMetaobject__invoke__964602083/9134.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3608 0)
(declare-sort var936 0)
(declare-sort var3472 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun getClass/1258963082 (var3608) ClassObject)
(declare-fun getMethods/-297347657 (ClassObject) (Array Int var936))
(declare-fun getLength-Arr-var936-1 ((Array Int var936)) Int)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(define-fun append/-1001720160 ((s String) (tail Int)) String (str.++ s (str.from_int tail)))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun var3472-init () var3472)
(declare-fun <init>/-432682954 (var3472 String) void)
(declare-const null-var3608 var3608)
(declare-const null-Int Int)
(declare-const null-__Array__Int__var3608__ (Array Int var3608))
(declare-const var2742 var3608) ; Statement: r0 := @parameter0: java.lang.Object 
(assert (not (= var2742 null-var3608)))
(declare-const var3737 Int) ; Statement: i1 := @parameter1: int 
(assert (not (= var3737 null-Int)))
(declare-const var2425 (Array Int var3608)) ; Statement: r10 := @parameter2: java.lang.Object[] 
(assert (not (= var2425 null-__Array__Int__var3608__)))
(assert true)
(define-const var2103 ClassObject (getClass/1258963082 var2742)) ; Statement: $r1 = virtualinvoke r0.<java.lang.Object: java.lang.Class getClass()>() 
(assert true)
(define-const var1277 (Array Int var936) (getMethods/-297347657 var2103)) ; Statement: r2 = virtualinvoke $r1.<java.lang.Class: java.lang.reflect.Method[] getMethods()>() 
(define-const var1054 Int (getLength-Arr-var936-1 var1277)) ; Statement: i0 = lengthof r2 
(define-const var2570 String String-init) ; Statement: $r3 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var2570)) ; Statement: specialinvoke $r3.<java.lang.StringBuilder: void <init>()>() 
(declare-const var2570!1 String)
(assert (= var2570!1 ""))
(assert true)
(define-const var2875 String (append/672562846 var2570!1 "_m_")) ; Statement: $r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("_m_") 
(declare-const var2570!2 String)
(assert (= var2570!2 (str.++ var2570!1 "_m_")))
(assert true)
(define-const var209 String (append/-1001720160 var2875 var3737)) ; Statement: $r5 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>(i1) 
(declare-const var2875!1 String)
(assert (str.prefixof var2875 var2875!1))
(assert true)
(define-const var3672 String (toString/-2075883882 var209)) ; Statement: r6 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.String toString()>() 
(define-const var1508 Int 0) ; Statement: i2 = 0 
(assert true) ; Non Conditional
 ; Statement: if i2 >= i0 goto $r7 = new org.apache.ibatis.javassist.tools.reflect.CannotInvokeException 
(assert (>= var1508 var1054)) ; Cond: i2 >= i0 
(define-const var1388 var3472 var3472-init) ; Statement: $r7 = new org.apache.ibatis.javassist.tools.reflect.CannotInvokeException 
(assert true)
;(assert (<init>/-432682954 var1388 "cannot find a method")) ; Statement: specialinvoke $r7.<org.apache.ibatis.javassist.tools.reflect.CannotInvokeException: void <init>(java.lang.String)>("cannot find a method") 

(declare-const var1388!1 var3472)
(declare-const var3483 String)
 ; Statement: throw $r7 
(check-sat)


; {getClass/1258963082=([java.lang.Object], java.lang.Class), getMethods/-297347657=([java.lang.Class], java.lang.reflect.Method[]), getLength-Arr-var936-1=([java.lang.reflect.Method[]], int), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), append/-1001720160=([java.lang.StringBuilder, int], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), var3472-init=([], org.apache.ibatis.javassist.tools.reflect.CannotInvokeException), <init>/-432682954=([org.apache.ibatis.javassist.tools.reflect.CannotInvokeException, java.lang.String], void)}
; {var3608=java.lang.Object, var2742=r0, var3737=i1, var2425=r10, var2103=$r1, var936=java.lang.reflect.Method, var1277=r2, var1054=i0, var2570=$r3, var2875=$r4, var209=$r5, var3672=r6, var1508=i2, var3472=org.apache.ibatis.javassist.tools.reflect.CannotInvokeException, var1388=$r7, var3483="cannot find a method"}
; {java.lang.Object=var3608, r0=var2742, i1=var3737, r10=var2425, $r1=var2103, java.lang.reflect.Method=var936, r2=var1277, i0=var1054, $r3=var2570, $r4=var2875, $r5=var209, r6=var3672, i2=var1508, org.apache.ibatis.javassist.tools.reflect.CannotInvokeException=var3472, $r7=var1388, "cannot find a method"=var3483}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(int)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(int)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r0 := @parameter0: java.lang.Object;	i1 := @parameter1: int;	r10 := @parameter2: java.lang.Object[];	$r1 = virtualinvoke r0.<java.lang.Object: java.lang.Class getClass()>();	r2 = virtualinvoke $r1.<java.lang.Class: java.lang.reflect.Method[] getMethods()>();	i0 = lengthof r2;	$r3 = new java.lang.StringBuilder;	specialinvoke $r3.<java.lang.StringBuilder: void <init>()>();	$r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("_m_");	$r5 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>(i1);	r6 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.String toString()>();	i2 = 0;	if i2 >= i0 goto $r7 = new org.apache.ibatis.javassist.tools.reflect.CannotInvokeException;	$r7 = new org.apache.ibatis.javassist.tools.reflect.CannotInvokeException;	specialinvoke $r7.<org.apache.ibatis.javassist.tools.reflect.CannotInvokeException: void <init>(java.lang.String)>("cannot find a method");	throw $r7
;block_num 3