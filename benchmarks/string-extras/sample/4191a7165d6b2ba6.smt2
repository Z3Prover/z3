; origin: https://github.com/iscas-projects/SCB : freemarker/smt/method-freemarker.template.TemplateException__renderMessages__-1806343646/7638-deviant-0.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var449 0)
(declare-sort var1570 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun getDescription/996028399 (var449) String)
(define-fun length/-134980193 ((s String)) Int (str.len s))
(declare-fun messageWithoutStackTop/1424937385 (var449) String)
(declare-fun getFTLInstructionStackTopFew/-1875609904 (var449) String)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun message/1424937385 (var449) String)
(define-fun substring/-1240304868 ((s String) (begin Int) (end Int)) String (str.substr s begin (- end begin)))
(declare-const null-var449 var449)
(declare-const null-String String)
(declare-const var3816 var449) ; Statement: r0 := @this: freemarker.template.TemplateException 
(assert (not (= var3816 null-var449)))
(assert true)
(define-const var1997 String (getDescription/996028399 var3816)) ; Statement: r1 = specialinvoke r0.<freemarker.template.TemplateException: java.lang.String getDescription()>() 
 ; Statement: if r1 == null goto $r2 = virtualinvoke r0.<freemarker.template.TemplateException: java.lang.Throwable getCause()>() 
(assert (not (= var1997 null-String))) ; Negate: Cond: r1 == null  
(assert true)
(define-const var2400 Int (length/-134980193 var1997)) ; Statement: $i1 = virtualinvoke r1.<java.lang.String: int length()>() 
 ; Statement: if $i1 == 0 goto $r2 = virtualinvoke r0.<freemarker.template.TemplateException: java.lang.Throwable getCause()>() 
(assert (not (= var2400 0))) ; Negate: Cond: $i1 == 0  
(declare-const var3816!1 var449)
(assert (not (= var3816!1 null-var449)))
(assert (= (messageWithoutStackTop/1424937385 var3816!1) var1997)) ; Statement: r0.<freemarker.template.TemplateException: java.lang.String messageWithoutStackTop> = r1 
 ; Statement: goto [?= $r29 = specialinvoke r0.<freemarker.template.TemplateException: java.lang.String getFTLInstructionStackTopFew()>()] 
(assert true) ; Non Conditional
(assert true)
(define-const var3226 String (getFTLInstructionStackTopFew/-1875609904 var3816!1)) ; Statement: $r29 = specialinvoke r0.<freemarker.template.TemplateException: java.lang.String getFTLInstructionStackTopFew()>() 
 ; Statement: if $r29 == null goto $r3 = r0.<freemarker.template.TemplateException: java.lang.String messageWithoutStackTop> 
(assert (not (= var3226 null-String))) ; Negate: Cond: $r29 == null  
(define-const var968 String String-init) ; Statement: $r4 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var968)) ; Statement: specialinvoke $r4.<java.lang.StringBuilder: void <init>()>() 
(declare-const var968!1 String)
(assert (= var968!1 ""))
(define-const var3113 String (messageWithoutStackTop/1424937385 var3816!1)) ; Statement: $r5 = r0.<freemarker.template.TemplateException: java.lang.String messageWithoutStackTop> 
(assert true)
(define-const var3683 String (append/672562846 var968!1 var3113)) ; Statement: $r6 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r5) 
(declare-const var968!2 String)
(assert (= var968!2 (str.++ var968!1 var3113)))
(assert true)
(define-const var3300 String (append/672562846 var3683 "\n\n")) ; Statement: $r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("\n\n") 
(declare-const var3683!1 String)
(assert (= var3683!1 (str.++ var3683 "\n\n")))
(assert true)
(define-const var180 String (append/672562846 var3300 "----")) ; Statement: $r8 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("----") 
(declare-const var3300!1 String)
(assert (= var3300!1 (str.++ var3300 "----")))
(assert true)
(define-const var166 String (append/672562846 var180 "\n")) ; Statement: $r9 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("\n") 
(declare-const var180!1 String)
(assert (= var180!1 (str.++ var180 "\n")))
(assert true)
(define-const var38 String (append/672562846 var166 "FTL stack trace (\u0022~\u0022 means nesting-related):")) ; Statement: $r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("FTL stack trace (\"~\" means nesting-related):") 
(declare-const var166!1 String)
(assert (= var166!1 (str.++ var166 "FTL stack trace (\u0022~\u0022 means nesting-related):")))
(assert true)
(define-const var3503 String (append/672562846 var38 "\n")) ; Statement: $r11 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("\n") 
(declare-const var38!1 String)
(assert (= var38!1 (str.++ var38 "\n")))
(assert true)
(define-const var686 String (append/672562846 var3503 var3226)) ; Statement: $r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r29) 
(declare-const var3503!1 String)
(assert (= var3503!1 (str.++ var3503 var3226)))
(assert true)
(define-const var3866 String (append/672562846 var686 "----")) ; Statement: $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("----") 
(declare-const var686!1 String)
(assert (= var686!1 (str.++ var686 "----")))
(assert true)
(define-const var2520 String (toString/-2075883882 var3866)) ; Statement: $r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.String toString()>() 
(declare-const var3816!2 var449)
(assert (not (= var3816!2 null-var449)))
(assert (= (message/1424937385 var3816!2) var2520)) ; Statement: r0.<freemarker.template.TemplateException: java.lang.String message> = $r14 
(define-const var1355 String (message/1424937385 var3816!2)) ; Statement: $r16 = r0.<freemarker.template.TemplateException: java.lang.String message> 
(define-const var476 String (messageWithoutStackTop/1424937385 var3816!2)) ; Statement: $r15 = r0.<freemarker.template.TemplateException: java.lang.String messageWithoutStackTop> 
(assert true)
(define-const var3463 Int (length/-134980193 var476)) ; Statement: $i0 = virtualinvoke $r15.<java.lang.String: int length()>() 
(assert (not (and true (and (>= 0 0) (>= (str.len var1355) var3463) (>= var3463 0)))))
(check-sat)


; {getDescription/996028399=([freemarker.template.TemplateException], java.lang.String), length/-134980193=([java.lang.String], int), messageWithoutStackTop/1424937385=([freemarker.template.TemplateException], java.lang.String), getFTLInstructionStackTopFew/-1875609904=([freemarker.template.TemplateException], java.lang.String), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), message/1424937385=([freemarker.template.TemplateException], java.lang.String), substring/-1240304868=([java.lang.String, int, int], java.lang.String)}
; {var449=freemarker.template.TemplateException, var3816=r0, var1997=r1, var1570=null_type, var2400=$i1, var3226=$r29, var968=$r4, var3113=$r5, var3683=$r6, var3300=$r7, var180=$r8, var166=$r9, var38=$r10, var3503=$r11, var686=$r12, var3866=$r13, var2520=$r14, var1355=$r16, var476=$r15, var3463=$i0, var1062=$r17}
; {freemarker.template.TemplateException=var449, r0=var3816, r1=var1997, null_type=var1570, $i1=var2400, $r29=var3226, $r4=var968, $r5=var3113, $r6=var3683, $r7=var3300, $r8=var180, $r9=var166, $r10=var38, $r11=var3503, $r12=var686, $r13=var3866, $r14=var2520, $r16=var1355, $r15=var476, $i0=var3463, $r17=var1062}
;seq <java.lang.String: int length()>;	<java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>;	<java.lang.String: int length()>;	<java.lang.String: java.lang.String substring(int,int)>
;cnt {"<java.lang.String: int length()>": 2,"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 8,"<java.lang.StringBuilder: java.lang.String toString()>": 1,"<java.lang.String: java.lang.String substring(int,int)>": 1}
;stmts r0 := @this: freemarker.template.TemplateException;	r1 = specialinvoke r0.<freemarker.template.TemplateException: java.lang.String getDescription()>();	if r1 == null goto $r2 = virtualinvoke r0.<freemarker.template.TemplateException: java.lang.Throwable getCause()>();	$i1 = virtualinvoke r1.<java.lang.String: int length()>();	if $i1 == 0 goto $r2 = virtualinvoke r0.<freemarker.template.TemplateException: java.lang.Throwable getCause()>();	r0.<freemarker.template.TemplateException: java.lang.String messageWithoutStackTop> = r1;	goto [?= $r29 = specialinvoke r0.<freemarker.template.TemplateException: java.lang.String getFTLInstructionStackTopFew()>()];	$r29 = specialinvoke r0.<freemarker.template.TemplateException: java.lang.String getFTLInstructionStackTopFew()>();	if $r29 == null goto $r3 = r0.<freemarker.template.TemplateException: java.lang.String messageWithoutStackTop>;	$r4 = new java.lang.StringBuilder;	specialinvoke $r4.<java.lang.StringBuilder: void <init>()>();	$r5 = r0.<freemarker.template.TemplateException: java.lang.String messageWithoutStackTop>;	$r6 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r5);	$r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("\n\n");	$r8 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("----");	$r9 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("\n");	$r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("FTL stack trace (\"~\" means nesting-related):");	$r11 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("\n");	$r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r29);	$r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("----");	$r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.String toString()>();	r0.<freemarker.template.TemplateException: java.lang.String message> = $r14;	$r16 = r0.<freemarker.template.TemplateException: java.lang.String message>;	$r15 = r0.<freemarker.template.TemplateException: java.lang.String messageWithoutStackTop>;	$i0 = virtualinvoke $r15.<java.lang.String: int length()>();	$r17 = virtualinvoke $r16.<java.lang.String: java.lang.String substring(int,int)>(0, $i0);	r0.<freemarker.template.TemplateException: java.lang.String messageWithoutStackTop> = $r17;	goto [?= return];	return
;block_num 6