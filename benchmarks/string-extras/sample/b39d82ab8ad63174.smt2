; origin: https://github.com/iscas-projects/SCB : closure-compiler/smt/method-com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler__mapJspToBaseName__-169318027/16770-deviant-1.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var2432 0)
(declare-sort var140 0)
(declare-sort var461 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun stripExtension/245859216 (var2432 var140) String)
(declare-fun getLength-Arr-String-1 ((Array Int String)) Int)
(declare-fun String-init () String)
(define-fun length/-134980193 ((s String)) Int (str.len s))
(declare-fun <init>/543593434 (String Int) void)
(define-fun charAt/698050440 ((s String) (index Int)) Int (str.to_code (str.at s index)))
(declare-fun var461_isJavaIdentifierStart/-1368251299 (Int) Bool)
(declare-fun var2432_mangleChar/-58234055 (Int) String)
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(define-fun substring/850833817 ((s String) (begin Int)) String (str.substr s begin (- (str.len s) begin)))
(declare-fun toCharArray/415275702 (String) (Array Int Int))
(declare-fun getLength-Arr-Int-1 ((Array Int Int)) Int)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-const null-var2432 var2432)
(declare-const null-var140 var140)
(declare-const var2432-keywords (Array Int String))
(declare-const var2753 var2432) ; Statement: r0 := @this: com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler 
(assert (not (= var2753 null-var2432)))
(declare-const var1867 var140) ; Statement: r1 := @parameter0: java.io.File 
(assert (not (= var1867 null-var140)))
(assert true)
(define-const var2850 String (stripExtension/245859216 var2753 var1867)) ; Statement: r11 = specialinvoke r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler: java.lang.String stripExtension(java.io.File)>(r1) 
(define-const var2196 (Array Int String) var2432-keywords) ; Statement: r12 = <com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler: java.lang.String[] keywords> 
(define-const var2621 Int (getLength-Arr-String-1 var2196)) ; Statement: i4 = lengthof r12 
(define-const var2558 Int 0) ; Statement: i5 = 0 
(assert true) ; Non Conditional
 ; Statement: if i5 >= i4 goto $r2 = new java.lang.StringBuilder 
(assert (>= var2558 var2621)) ; Cond: i5 >= i4 
(define-const var3420 String String-init) ; Statement: $r2 = new java.lang.StringBuilder 
(assert true)
(define-const var1549 Int (length/-134980193 var2850)) ; Statement: $i0 = virtualinvoke r11.<java.lang.String: int length()>() 
(assert true)
;(assert (<init>/543593434 var3420 var1549)) ; Statement: specialinvoke $r2.<java.lang.StringBuilder: void <init>(int)>($i0) 

(declare-const var3420!1 String)
(declare-const var1549!1 Int)
(assert (and true (and (> (str.len var2850) 0) (<= 0 0))))
(define-const var567 Int (charAt/698050440 var2850 0)) ; Statement: $c3 = virtualinvoke r11.<java.lang.String: char charAt(int)>(0) 
(define-const var1423 Bool (var461_isJavaIdentifierStart/-1368251299 var567)) ; Statement: $z0 = staticinvoke <java.lang.Character: boolean isJavaIdentifierStart(char)>($c3) 
 ; Statement: if $z0 == 0 goto $r3 = staticinvoke <com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler: java.lang.String mangleChar(char)>($c3) 
(assert (= (ite var1423 1 0) 0)) ; Cond: $z0 == 0 
(define-const var1189 String (var2432_mangleChar/-58234055 var567)) ; Statement: $r3 = staticinvoke <com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler: java.lang.String mangleChar(char)>($c3) 
(assert true)
;(assert (append/672562846 var3420!1 var1189)) ; Statement: virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r3) 
(declare-const var3420!2 String)
(assert (= var3420!2 (str.++ var3420!1 var1189)))
(assert true) ; Non Conditional
(assert (not (and true (and (>= 1 0) (>= (str.len var2850) 1)))))
(check-sat)


; {stripExtension/245859216=([com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler, java.io.File], java.lang.String), getLength-Arr-String-1=([java.lang.String[]], int), String-init=([], java.lang.StringBuilder), length/-134980193=([java.lang.String], int), <init>/543593434=([java.lang.StringBuilder, int], void), charAt/698050440=([java.lang.String, int], char), var461_isJavaIdentifierStart/-1368251299=([char], boolean), var2432_mangleChar/-58234055=([char], java.lang.String), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), substring/850833817=([java.lang.String, int], java.lang.String), toCharArray/415275702=([java.lang.String], char[]), getLength-Arr-Int-1=([char[]], int), toString/-2075883882=([java.lang.StringBuilder], java.lang.String)}
; {var2432=com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler, var2753=r0, var140=java.io.File, var1867=r1, var2850=r11, var2196=r12, var2621=i4, var2558=i5, var3420=$r2, var1549=$i0, var567=$c3, var461=java.lang.Character, var1423=$z0, var1189=$r3, var1128=$r4, var931=$r7, var347=$i2, var3201=i6, var1566=$r5}
; {com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler=var2432, r0=var2753, java.io.File=var140, r1=var1867, r11=var2850, r12=var2196, i4=var2621, i5=var2558, $r2=var3420, $i0=var1549, $c3=var567, java.lang.Character=var461, $z0=var1423, $r3=var1189, $r4=var1128, $r7=var931, $i2=var347, i6=var3201, $r5=var1566}
;seq <java.lang.String: int length()>;	<java.lang.StringBuilder: void <init>(int)>;	<java.lang.String: char charAt(int)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.String: java.lang.String substring(int)>;	<java.lang.String: char[] toCharArray()>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.String: int length()>": 1,"<java.lang.StringBuilder: void <init>(int)>": 1,"<java.lang.String: char charAt(int)>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 1,"<java.lang.String: java.lang.String substring(int)>": 1,"<java.lang.String: char[] toCharArray()>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r0 := @this: com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler;	r1 := @parameter0: java.io.File;	r11 = specialinvoke r0.<com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler: java.lang.String stripExtension(java.io.File)>(r1);	r12 = <com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler: java.lang.String[] keywords>;	i4 = lengthof r12;	i5 = 0;	if i5 >= i4 goto $r2 = new java.lang.StringBuilder;	$r2 = new java.lang.StringBuilder;	$i0 = virtualinvoke r11.<java.lang.String: int length()>();	specialinvoke $r2.<java.lang.StringBuilder: void <init>(int)>($i0);	$c3 = virtualinvoke r11.<java.lang.String: char charAt(int)>(0);	$z0 = staticinvoke <java.lang.Character: boolean isJavaIdentifierStart(char)>($c3);	if $z0 == 0 goto $r3 = staticinvoke <com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler: java.lang.String mangleChar(char)>($c3);	$r3 = staticinvoke <com.google.javascript.jscomp.jarjar.org.apache.tools.ant.taskdefs.optional.jsp.JspNameMangler: java.lang.String mangleChar(char)>($c3);	virtualinvoke $r2.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r3);	$r4 = virtualinvoke r11.<java.lang.String: java.lang.String substring(int)>(1);	$r7 = virtualinvoke $r4.<java.lang.String: char[] toCharArray()>();	$i2 = lengthof $r7;	i6 = 0;	if i6 >= $i2 goto $r5 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.String toString()>();	$r5 = virtualinvoke $r2.<java.lang.StringBuilder: java.lang.String toString()>();	return $r5
;block_num 7