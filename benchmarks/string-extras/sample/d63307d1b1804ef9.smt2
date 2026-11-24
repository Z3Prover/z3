; origin: https://github.com/iscas-projects/SCB : freemarker/smt/method-freemarker.core.ParseException__renderMessageAndDescription__1113934958/3497-deviant-0.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3575 0)
(declare-sort var3232 0)
(declare-sort var2933 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun getOrRenderDescription/860543450 (var3575) String)
(declare-fun isInJBossToolsMode/-1356736118 (var3575) Bool)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun templateName/-61493021 (var3575) String)
(declare-fun lineNumber/-61493021 (var3575) Int)
(declare-fun columnNumber/-61493021 (var3575) Int)
(declare-fun var3232_formatLocationForSimpleParsingError/-282828407 (String Int Int) String)
(define-fun toString/-2075883882 ((s String)) String s)
(define-fun length/-134980193 ((s String)) Int (str.len s))
(define-fun substring/850833817 ((s String) (begin Int)) String (str.substr s begin (- (str.len s) begin)))
(declare-const null-var3575 var3575)
(declare-const null-var2933 var2933)
(declare-const var383 var3575) ; Statement: r0 := @this: freemarker.core.ParseException 
(assert (not (= var383 null-var3575)))
(assert true)
(define-const var3217 String (getOrRenderDescription/860543450 var383)) ; Statement: r17 = specialinvoke r0.<freemarker.core.ParseException: java.lang.String getOrRenderDescription()>() 
(assert true)
(define-const var2717 Bool (isInJBossToolsMode/-1356736118 var383)) ; Statement: $z0 = specialinvoke r0.<freemarker.core.ParseException: boolean isInJBossToolsMode()>() 
 ; Statement: if $z0 != 0 goto $r1 = new java.lang.StringBuilder 
(assert (not (not (= (ite var2717 1 0) 0)))) ; Negate: Cond: $z0 != 0  
(define-const var2543 String String-init) ; Statement: $r8 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var2543)) ; Statement: specialinvoke $r8.<java.lang.StringBuilder: void <init>()>() 
(declare-const var2543!1 String)
(assert (= var2543!1 ""))
(assert true)
(define-const var3285 String (append/672562846 var2543!1 "Syntax error ")) ; Statement: $r11 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Syntax error ") 
(declare-const var2543!2 String)
(assert (= var2543!2 (str.++ var2543!1 "Syntax error ")))
(define-const var3049 String (templateName/-61493021 var383)) ; Statement: $r9 = r0.<freemarker.core.ParseException: java.lang.String templateName> 
(define-const var2885 Int (lineNumber/-61493021 var383)) ; Statement: $i3 = r0.<freemarker.core.ParseException: int lineNumber> 
(define-const var3659 Int (columnNumber/-61493021 var383)) ; Statement: $i2 = r0.<freemarker.core.ParseException: int columnNumber> 
(define-const var1436 String (var3232_formatLocationForSimpleParsingError/-282828407 var3049 var2885 var3659)) ; Statement: $r10 = staticinvoke <freemarker.core._MessageUtil: java.lang.String formatLocationForSimpleParsingError(java.lang.String,int,int)>($r9, $i3, $i2) 
(assert true)
(define-const var1207 String (append/672562846 var3285 var1436)) ; Statement: $r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r10) 
(declare-const var3285!1 String)
(assert (= var3285!1 (str.++ var3285 var1436)))
(assert true)
(define-const var1058 String (append/672562846 var1207 ":\n")) ; Statement: $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(":\n") 
(declare-const var1207!1 String)
(assert (= var1207!1 (str.++ var1207 ":\n")))
(assert true)
(define-const var564 String (toString/-2075883882 var1058)) ; Statement: r18 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.String toString()>() 
 ; Statement: goto [?= $r5 = new java.lang.StringBuilder] 
(assert true) ; Non Conditional
(define-const var3683 String String-init) ; Statement: $r5 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var3683)) ; Statement: specialinvoke $r5.<java.lang.StringBuilder: void <init>()>() 
(declare-const var3683!1 String)
(assert (= var3683!1 ""))
(assert true)
(define-const var2886 String (append/672562846 var3683!1 var564)) ; Statement: $r6 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r18) 
(declare-const var3683!2 String)
(assert (= var3683!2 (str.++ var3683!1 var564)))
(assert true)
(define-const var1600 String (append/672562846 var2886 var3217)) ; Statement: $r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r17) 
(declare-const var2886!1 String)
(assert (= var2886!1 (str.++ var2886 var3217)))
(assert true)
(define-const var1801 String (toString/-2075883882 var1600)) ; Statement: $r14 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert true)
(define-const var1853 Int (length/-134980193 var564)) ; Statement: $i1 = virtualinvoke r18.<java.lang.String: int length()>() 
(assert (not (and true (and (>= var1853 0) (>= (str.len var1801) var1853)))))
(check-sat)


; {getOrRenderDescription/860543450=([freemarker.core.ParseException], java.lang.String), isInJBossToolsMode/-1356736118=([freemarker.core.ParseException], boolean), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), templateName/-61493021=([freemarker.core.ParseException], java.lang.String), lineNumber/-61493021=([freemarker.core.ParseException], int), columnNumber/-61493021=([freemarker.core.ParseException], int), var3232_formatLocationForSimpleParsingError/-282828407=([java.lang.String, int, int], java.lang.String), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), length/-134980193=([java.lang.String], int), substring/850833817=([java.lang.String, int], java.lang.String)}
; {var3575=freemarker.core.ParseException, var383=r0, var3217=r17, var2717=$z0, var2543=$r8, var3285=$r11, var3049=$r9, var2885=$i3, var3659=$i2, var3232=freemarker.core._MessageUtil, var1436=$r10, var1207=$r12, var1058=$r13, var564=r18, var3683=$r5, var2886=$r6, var1600=$r7, var1801=$r14, var1853=$i1, var3687=$r15, var2933=java.lang.Throwable, var1328=$r16}
; {freemarker.core.ParseException=var3575, r0=var383, r17=var3217, $z0=var2717, $r8=var2543, $r11=var3285, $r9=var3049, $i3=var2885, $i2=var3659, freemarker.core._MessageUtil=var3232, $r10=var1436, $r12=var1207, $r13=var1058, r18=var564, $r5=var3683, $r6=var2886, $r7=var1600, $r14=var1801, $i1=var1853, $r15=var3687, java.lang.Throwable=var2933, $r16=var1328}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>;	<java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>;	<java.lang.String: int length()>;	<java.lang.String: java.lang.String substring(int)>
;cnt {"<java.lang.StringBuilder: void <init>()>": 2,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 5,"<java.lang.StringBuilder: java.lang.String toString()>": 2,"<java.lang.String: int length()>": 1,"<java.lang.String: java.lang.String substring(int)>": 1}
;stmts r0 := @this: freemarker.core.ParseException;	r17 = specialinvoke r0.<freemarker.core.ParseException: java.lang.String getOrRenderDescription()>();	$z0 = specialinvoke r0.<freemarker.core.ParseException: boolean isInJBossToolsMode()>();	if $z0 != 0 goto $r1 = new java.lang.StringBuilder;	$r8 = new java.lang.StringBuilder;	specialinvoke $r8.<java.lang.StringBuilder: void <init>()>();	$r11 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Syntax error ");	$r9 = r0.<freemarker.core.ParseException: java.lang.String templateName>;	$i3 = r0.<freemarker.core.ParseException: int lineNumber>;	$i2 = r0.<freemarker.core.ParseException: int columnNumber>;	$r10 = staticinvoke <freemarker.core._MessageUtil: java.lang.String formatLocationForSimpleParsingError(java.lang.String,int,int)>($r9, $i3, $i2);	$r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r10);	$r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(":\n");	r18 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.String toString()>();	goto [?= $r5 = new java.lang.StringBuilder];	$r5 = new java.lang.StringBuilder;	specialinvoke $r5.<java.lang.StringBuilder: void <init>()>();	$r6 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r18);	$r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r17);	$r14 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.String toString()>();	$i1 = virtualinvoke r18.<java.lang.String: int length()>();	$r15 = virtualinvoke $r14.<java.lang.String: java.lang.String substring(int)>($i1);	entermonitor r0;	$r16 := @caughtexception;	exitmonitor r0;	throw $r16
;block_num 6