; origin: https://github.com/iscas-projects/SCB : closure-compiler/smt/method-com.google.javascript.jscomp.jarjar.com.google.common.io.Files$FileByteSink__toString__789858016/48002.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var2737 0)
(declare-sort var3845 0)
(declare-sort var2818 0)
(declare-sort var3329 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun file/-1323983552 (var2737) var3845)
(declare-fun append/-1031950772 (String var2818) String)
(declare-fun cast-from-var3845-to-var2818 (var3845) var2818)
(declare-fun modes/-1323983552 (var2737) var3329)
(declare-fun cast-from-var3329-to-var2818 (var3329) var2818)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-const null-var2737 var2737)
(declare-const var3600 var2737) ; Statement: r1 := @this: com.google.javascript.jscomp.jarjar.com.google.common.io.Files$FileByteSink 
(assert (not (= var3600 null-var2737)))
(define-const var3243 String String-init) ; Statement: $r0 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var3243)) ; Statement: specialinvoke $r0.<java.lang.StringBuilder: void <init>()>() 
(declare-const var3243!1 String)
(assert (= var3243!1 ""))
(assert true)
(define-const var3373 String (append/672562846 var3243!1 "Files.asByteSink(")) ; Statement: $r3 = virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Files.asByteSink(") 
(declare-const var3243!2 String)
(assert (= var3243!2 (str.++ var3243!1 "Files.asByteSink(")))
(define-const var874 var3845 (file/-1323983552 var3600)) ; Statement: $r2 = r1.<com.google.javascript.jscomp.jarjar.com.google.common.io.Files$FileByteSink: java.io.File file> 
(assert true)
(define-const var1010 String (append/-1031950772 var3373 (cast-from-var3845-to-var2818 var874))) ; Statement: $r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r2) 
(declare-const var3373!1 String)
(assert (str.prefixof var3373 var3373!1))
(assert true)
(define-const var3079 String (append/672562846 var1010 ", ")) ; Statement: $r6 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", ") 
(declare-const var1010!1 String)
(assert (= var1010!1 (str.++ var1010 ", ")))
(define-const var2719 var3329 (modes/-1323983552 var3600)) ; Statement: $r5 = r1.<com.google.javascript.jscomp.jarjar.com.google.common.io.Files$FileByteSink: com.google.javascript.jscomp.jarjar.com.google.common.collect.ImmutableSet modes> 
(assert true)
(define-const var1970 String (append/-1031950772 var3079 (cast-from-var3329-to-var2818 var2719))) ; Statement: $r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r5) 
(declare-const var3079!1 String)
(assert (str.prefixof var3079 var3079!1))
(assert true)
(define-const var3894 String (append/672562846 var1970 ")")) ; Statement: $r8 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(")") 
(declare-const var1970!1 String)
(assert (= var1970!1 (str.++ var1970 ")")))
(assert true)
(define-const var596 String (toString/-2075883882 var3894)) ; Statement: $r9 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.String toString()>() 
 ; Statement: return $r9 
(check-sat)


; {String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), file/-1323983552=([com.google.javascript.jscomp.jarjar.com.google.common.io.Files$FileByteSink], java.io.File), append/-1031950772=([java.lang.StringBuilder, java.lang.Object], java.lang.StringBuilder), cast-from-var3845-to-var2818=([java.io.File], java.lang.Object), modes/-1323983552=([com.google.javascript.jscomp.jarjar.com.google.common.io.Files$FileByteSink], com.google.javascript.jscomp.jarjar.com.google.common.collect.ImmutableSet), cast-from-var3329-to-var2818=([com.google.javascript.jscomp.jarjar.com.google.common.collect.ImmutableSet], java.lang.Object), toString/-2075883882=([java.lang.StringBuilder], java.lang.String)}
; {var2737=com.google.javascript.jscomp.jarjar.com.google.common.io.Files$FileByteSink, var3600=r1, var3243=$r0, var3373=$r3, var3845=java.io.File, var874=$r2, var2818=java.lang.Object, var1010=$r4, var3079=$r6, var3329=com.google.javascript.jscomp.jarjar.com.google.common.collect.ImmutableSet, var2719=$r5, var1970=$r7, var3894=$r8, var596=$r9}
; {com.google.javascript.jscomp.jarjar.com.google.common.io.Files$FileByteSink=var2737, r1=var3600, $r0=var3243, $r3=var3373, java.io.File=var3845, $r2=var874, java.lang.Object=var2818, $r4=var1010, $r6=var3079, com.google.javascript.jscomp.jarjar.com.google.common.collect.ImmutableSet=var3329, $r5=var2719, $r7=var1970, $r8=var3894, $r9=var596}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 3,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>": 2,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r1 := @this: com.google.javascript.jscomp.jarjar.com.google.common.io.Files$FileByteSink;	$r0 = new java.lang.StringBuilder;	specialinvoke $r0.<java.lang.StringBuilder: void <init>()>();	$r3 = virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Files.asByteSink(");	$r2 = r1.<com.google.javascript.jscomp.jarjar.com.google.common.io.Files$FileByteSink: java.io.File file>;	$r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r2);	$r6 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", ");	$r5 = r1.<com.google.javascript.jscomp.jarjar.com.google.common.io.Files$FileByteSink: com.google.javascript.jscomp.jarjar.com.google.common.collect.ImmutableSet modes>;	$r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>($r5);	$r8 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(")");	$r9 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.String toString()>();	return $r9
;block_num 1