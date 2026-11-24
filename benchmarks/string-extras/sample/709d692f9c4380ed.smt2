; origin: https://github.com/iscas-projects/SCB : closure-compiler/smt/method-com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc__callEjbc__-971089414/17631.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var683 0)
(declare-sort var3918 0)
(declare-sort var3062 0)
(declare-sort var2053 0)
(declare-sort var2627 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun iasHomeDir/1631179044 (var683) var3918)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(declare-fun toString/180451120 (var3918) String)
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun String_join/-1520935655 (String (Array Int String)) String)
(define-fun cast-from-String-to-String ((arg String)) String arg)
(define-fun cast-from-__Array__Int__String__-to-__Array__Int__String__ ((arg (Array Int String))) (Array Int String) arg)
(declare-fun log/2105092484 (var683 String) void)
(declare-fun var2053_getStackTrace/-253691410 (var2627) String)
(declare-fun cast-from-var3062-to-var2627 (var3062) var2627)
(declare-const null-var683 var683)
(declare-const null-__Array__Int__String__ (Array Int String))
(declare-const null-var3918 var3918)
(declare-const var3918-separator String)
(declare-const null-var3062 var3062)
(declare-const var2502 var683) ; Statement: r0 := @this: com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc 
(assert (not (= var2502 null-var683)))
(declare-const var811 (Array Int String)) ; Statement: r14 := @parameter0: java.lang.String[] 
(assert (not (= var811 null-__Array__Int__String__)))
(define-const var82 var3918 (iasHomeDir/1631179044 var2502)) ; Statement: $r1 = r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc: java.io.File iasHomeDir> 
 ; Statement: if $r1 != null goto $r2 = new java.lang.StringBuilder 
(assert (not (= var82 null-var3918))) ; Cond: $r1 != null 
(define-const var1657 String String-init) ; Statement: $r2 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var1657)) ; Statement: specialinvoke $r2.<java.lang.StringBuilder: void <init>()>() 
(declare-const var1657!1 String)
(assert (= var1657!1 ""))
(define-const var3282 var3918 (iasHomeDir/1631179044 var2502)) ; Statement: $r3 = r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc: java.io.File iasHomeDir> 
(assert true)
(define-const var1686 String (toString/180451120 var3282)) ; Statement: $r4 = virtualinvoke $r3.<java.io.File: java.lang.String toString()>() 
(assert true)
(define-const var3266 String (append/672562846 var1657!1 var1686)) ; Statement: $r6 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r4) 
(declare-const var1657!2 String)
(assert (= var1657!2 (str.++ var1657!1 var1686)))
(define-const var3108 String var3918-separator) ; Statement: $r5 = <java.io.File: java.lang.String separator> 
(assert true)
(define-const var3680 String (append/672562846 var3266 var3108)) ; Statement: $r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r5) 
(declare-const var3266!1 String)
(assert (= var3266!1 (str.++ var3266 var3108)))
(assert true)
(define-const var7 String (append/672562846 var3680 "bin")) ; Statement: $r9 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("bin") 
(declare-const var3680!1 String)
(assert (= var3680!1 (str.++ var3680 "bin")))
(define-const var1972 String var3918-separator) ; Statement: $r8 = <java.io.File: java.lang.String separator> 
(assert true)
(define-const var545 String (append/672562846 var7 var1972)) ; Statement: $r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r8) 
(declare-const var7!1 String)
(assert (= var7!1 (str.++ var7 var1972)))
(assert true)
(define-const var2697 String (toString/-2075883882 var545)) ; Statement: r34 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert true) ; Non Conditional
(define-const var1589 String String-init) ; Statement: $r11 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var1589)) ; Statement: specialinvoke $r11.<java.lang.StringBuilder: void <init>()>() 
(declare-const var1589!1 String)
(assert (= var1589!1 ""))
(assert true)
(define-const var3053 String (append/672562846 var1589!1 var2697)) ; Statement: $r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r34) 
(declare-const var1589!2 String)
(assert (= var1589!2 (str.++ var1589!1 var2697)))
(assert true)
(define-const var3229 String (append/672562846 var3053 "ejbc ")) ; Statement: $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("ejbc ") 
(declare-const var3053!1 String)
(assert (= var3053!1 (str.++ var3053 "ejbc ")))
(assert true)
(define-const var3642 String (toString/-2075883882 var3229)) ; Statement: $r28 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.String toString()>() 
(define-const var2180 String (String_join/-1520935655 (cast-from-String-to-String " ") (cast-from-__Array__Int__String__-to-__Array__Int__String__ var811))) ; Statement: $r29 = staticinvoke <java.lang.String: java.lang.String join(java.lang.CharSequence,java.lang.CharSequence[])>(" ", r14) 
(define-const var2937 String String-init) ; Statement: $r15 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var2937)) ; Statement: specialinvoke $r15.<java.lang.StringBuilder: void <init>()>() 
(declare-const var2937!1 String)
(assert (= var2937!1 ""))
(assert true)
(define-const var2223 String (append/672562846 var2937!1 var3642)) ; Statement: $r16 = virtualinvoke $r15.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r28) 
(declare-const var2937!2 String)
(assert (= var2937!2 (str.++ var2937!1 var3642)))
(assert true)
(define-const var1713 String (append/672562846 var2223 var2180)) ; Statement: $r17 = virtualinvoke $r16.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r29) 
(declare-const var2223!1 String)
(assert (= var2223!1 (str.++ var2223 var2180)))
(assert true)
(define-const var3166 String (toString/-2075883882 var1713)) ; Statement: $r18 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert true)
;(assert (log/2105092484 var2502 var3166)) ; Statement: specialinvoke r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc: void log(java.lang.String)>($r18) 

(declare-const var2502!1 var683)
(declare-const var3166!1 String)
(assert true) ; Handling Exception: java.lang.Throwable 
(declare-const var882 var3062) ; Statement: $r32 := @caughtexception 
(assert (not (= var882 null-var3062)))
(assert true)
;(assert (log/2105092484 var2502!1 "An IOException has occurred while trying to execute ejbc.")) ; Statement: specialinvoke r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc: void log(java.lang.String)>("An IOException has occurred while trying to execute ejbc.") 

(declare-const var2502!2 var683)
(declare-const var3387 String)
(define-const var2927 String (var2053_getStackTrace/-253691410 (cast-from-var3062-to-var2627 var882))) ; Statement: $r33 = staticinvoke <com.google.javascript.jscomp.jarjar.org.apache.tools.ant.util.StringUtils: java.lang.String getStackTrace(java.lang.Throwable)>($r32) 
(assert true)
;(assert (log/2105092484 var2502!2 var2927)) ; Statement: specialinvoke r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc: void log(java.lang.String)>($r33) 

(declare-const var2502!3 var683)
(declare-const var2927!1 String)
 ; Statement: goto [?= return] 
(assert true) ; Non Conditional
 ; Statement: return 
(check-sat)


; {iasHomeDir/1631179044=([com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc], java.io.File), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), toString/180451120=([java.io.File], java.lang.String), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), String_join/-1520935655=([java.lang.CharSequence, java.lang.CharSequence[]], java.lang.String), cast-from-String-to-String=([java.lang.String], java.lang.CharSequence), cast-from-__Array__Int__String__-to-__Array__Int__String__=([java.lang.String[]], java.lang.CharSequence[]), log/2105092484=([com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc, java.lang.String], void), var2053_getStackTrace/-253691410=([java.lang.Throwable], java.lang.String), cast-from-var3062-to-var2627=([java.io.IOException], java.lang.Throwable)}
; {var683=com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc, var2502=r0, var811=r14, var3918=java.io.File, var82=$r1, var1657=$r2, var3282=$r3, var1686=$r4, var3266=$r6, var3108=$r5, var3680=$r7, var7=$r9, var1972=$r8, var545=$r10, var2697=r34, var1589=$r11, var3053=$r12, var3229=$r13, var3642=$r28, var2180=$r29, var2937=$r15, var2223=$r16, var1713=$r17, var3166=$r18, var3062=java.io.IOException, var882=$r32, var3387="An IOException has occurred while trying to execute ejbc.", var2053=com.google.javascript.jscomp.jarjar.org.apache.tools.ant.util.StringUtils, var2627=java.lang.Throwable, var2927=$r33}
; {com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc=var683, r0=var2502, r14=var811, java.io.File=var3918, $r1=var82, $r2=var1657, $r3=var3282, $r4=var1686, $r6=var3266, $r5=var3108, $r7=var3680, $r9=var7, $r8=var1972, $r10=var545, r34=var2697, $r11=var1589, $r12=var3053, $r13=var3229, $r28=var3642, $r29=var2180, $r15=var2937, $r16=var2223, $r17=var1713, $r18=var3166, java.io.IOException=var3062, $r32=var882, "An IOException has occurred while trying to execute ejbc."=var3387, com.google.javascript.jscomp.jarjar.org.apache.tools.ant.util.StringUtils=var2053, java.lang.Throwable=var2627, $r33=var2927}
;seq <java.lang.StringBuilder: void <init>()>;	<java.io.File: java.lang.String toString()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>;	<java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>;	<java.lang.String: java.lang.String join(java.lang.CharSequence,java.lang.CharSequence[])>;	<java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 3,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 8,"<java.lang.StringBuilder: java.lang.String toString()>": 3,"<java.lang.String: java.lang.String join(java.lang.CharSequence,java.lang.CharSequence[])>": 1}
;stmts r0 := @this: com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc;	r14 := @parameter0: java.lang.String[];	$r1 = r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc: java.io.File iasHomeDir>;	if $r1 != null goto $r2 = new java.lang.StringBuilder;	$r2 = new java.lang.StringBuilder;	specialinvoke $r2.<java.lang.StringBuilder: void <init>()>();	$r3 = r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc: java.io.File iasHomeDir>;	$r4 = virtualinvoke $r3.<java.io.File: java.lang.String toString()>();	$r6 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r4);	$r5 = <java.io.File: java.lang.String separator>;	$r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r5);	$r9 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("bin");	$r8 = <java.io.File: java.lang.String separator>;	$r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r8);	r34 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.String toString()>();	$r11 = new java.lang.StringBuilder;	specialinvoke $r11.<java.lang.StringBuilder: void <init>()>();	$r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r34);	$r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("ejbc ");	$r28 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.String toString()>();	$r29 = staticinvoke <java.lang.String: java.lang.String join(java.lang.CharSequence,java.lang.CharSequence[])>(" ", r14);	$r15 = new java.lang.StringBuilder;	specialinvoke $r15.<java.lang.StringBuilder: void <init>()>();	$r16 = virtualinvoke $r15.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r28);	$r17 = virtualinvoke $r16.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r29);	$r18 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.String toString()>();	specialinvoke r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc: void log(java.lang.String)>($r18);	$r32 := @caughtexception;	specialinvoke r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc: void log(java.lang.String)>("An IOException has occurred while trying to execute ejbc.");	$r33 = staticinvoke <com.google.javascript.jscomp.jarjar.org.apache.tools.ant.util.StringUtils: java.lang.String getStackTrace(java.lang.Throwable)>($r32);	specialinvoke r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.ejb.IPlanetEjbc: void log(java.lang.String)>($r33);	goto [?= return];	return
;block_num 5