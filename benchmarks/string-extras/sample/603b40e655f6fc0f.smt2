; origin: https://github.com/iscas-projects/SCB : jdk/smt/method-jdk.internal.org.objectweb.asm.util.ASMifier__visitAnnotation__1201071458/3181.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var1832 0)
(declare-sort var3684 0)
(declare-sort var2220 0)
(declare-sort var896 0)
(declare-sort var1366 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun buf/-10557480 (var2220) String)
(declare-fun cast-from-var1832-to-var2220 (var1832) var2220)
(declare-fun setLength/163251007 (String Int) void)
(define-fun append/1560614132 ((s String) (tail String)) String (str.++ s tail))
(declare-fun name/1045876480 (var1832) String)
(declare-fun appendConstant/2119113448 (var1832 var896) void)
(declare-fun cast-from-String-to-var896 (String) var896)
(declare-fun append/-1166642301 (String Bool) String)
(declare-fun text/-10557480 (var2220) var1366)
(define-fun toString/-222306083 ((s String)) String s)
(declare-fun var1366_add/328494887 (var1366 var896) Bool)
(declare-fun createASMifier/-631099411 (var1832 String Int) var1832)
(declare-fun getText/-142638630 (var2220) var1366)
(declare-fun cast-from-var1366-to-var896 (var1366) var896)
(declare-const null-var1832 var1832)
(declare-const null-String String)
(declare-const null-Bool Bool)
(declare-const var2109 var1832) ; Statement: r0 := @this: jdk.internal.org.objectweb.asm.util.ASMifier 
(assert (not (= var2109 null-var1832)))
(declare-const var3826 String) ; Statement: r7 := @parameter0: java.lang.String 
(assert (not (= var3826 null-String)))
(declare-const var417 Bool) ; Statement: z0 := @parameter1: boolean 
(assert (not (= var417 null-Bool)))
(define-const var3926 String (buf/-10557480 (cast-from-var1832-to-var2220 var2109))) ; Statement: $r1 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.lang.StringBuffer buf> 
(assert true)
;(assert (setLength/163251007 var3926 0)) ; Statement: virtualinvoke $r1.<java.lang.StringBuffer: void setLength(int)>(0) 

(declare-const var3926!1 String)
(declare-const var747 Int)
(define-const var2547 String (buf/-10557480 (cast-from-var1832-to-var2220 var2109))) ; Statement: $r2 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.lang.StringBuffer buf> 
(assert true)
(define-const var1258 String (append/1560614132 var2547 "{\n")) ; Statement: $r3 = virtualinvoke $r2.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("{\n") 
(declare-const var2547!1 String)
(assert (str.prefixof var2547 var2547!1))
(assert true)
(define-const var2428 String (append/1560614132 var1258 "av0 = ")) ; Statement: $r5 = virtualinvoke $r3.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("av0 = ") 
(declare-const var1258!1 String)
(assert (str.prefixof var1258 var1258!1))
(define-const var1827 String (name/1045876480 var2109)) ; Statement: $r4 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.lang.String name> 
(assert true)
(define-const var1909 String (append/1560614132 var2428 var1827)) ; Statement: $r6 = virtualinvoke $r5.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>($r4) 
(declare-const var2428!1 String)
(assert (str.prefixof var2428 var2428!1))
(assert true)
;(assert (append/1560614132 var1909 ".visitAnnotation(")) ; Statement: virtualinvoke $r6.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>(".visitAnnotation(") 
(declare-const var1909!1 String)
(assert (str.prefixof var1909 var1909!1))
(assert true)
;(assert (appendConstant/2119113448 var2109 (cast-from-String-to-var896 var3826))) ; Statement: virtualinvoke r0.<jdk.internal.org.objectweb.asm.util.ASMifier: void appendConstant(java.lang.Object)>(r7) 

(declare-const var2109!1 var1832)
(declare-const var3826!1 String)
(define-const var1794 String (buf/-10557480 (cast-from-var1832-to-var2220 var2109!1))) ; Statement: $r8 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.lang.StringBuffer buf> 
(assert true)
(define-const var480 String (append/1560614132 var1794 ", ")) ; Statement: $r9 = virtualinvoke $r8.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>(", ") 
(declare-const var1794!1 String)
(assert (str.prefixof var1794 var1794!1))
(assert true)
(define-const var3185 String (append/-1166642301 var480 var417)) ; Statement: $r10 = virtualinvoke $r9.<java.lang.StringBuffer: java.lang.StringBuffer append(boolean)>(z0) 
(assert true)
;(assert (append/1560614132 var3185 ");\n")) ; Statement: virtualinvoke $r10.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>(");\n") 
(declare-const var3185!1 String)
(assert (str.prefixof var3185 var3185!1))
(define-const var1266 var1366 (text/-10557480 (cast-from-var1832-to-var2220 var2109!1))) ; Statement: $r12 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.util.List text> 
(define-const var3190 String (buf/-10557480 (cast-from-var1832-to-var2220 var2109!1))) ; Statement: $r11 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.lang.StringBuffer buf> 
(assert true)
(define-const var1910 String (toString/-222306083 var3190)) ; Statement: $r13 = virtualinvoke $r11.<java.lang.StringBuffer: java.lang.String toString()>() 
;(assert (var1366_add/328494887 var1266 (cast-from-String-to-var896 var1910))) ; Statement: interfaceinvoke $r12.<java.util.List: boolean add(java.lang.Object)>($r13) 

(declare-const var1266!1 var1366)
(declare-const var1910!1 String)
(assert true)
(define-const var348 var1832 (createASMifier/-631099411 var2109!1 "av" 0)) ; Statement: r14 = virtualinvoke r0.<jdk.internal.org.objectweb.asm.util.ASMifier: jdk.internal.org.objectweb.asm.util.ASMifier createASMifier(java.lang.String,int)>("av", 0) 
(define-const var3177 var1366 (text/-10557480 (cast-from-var1832-to-var2220 var2109!1))) ; Statement: $r15 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.util.List text> 
(assert true)
(define-const var1548 var1366 (getText/-142638630 (cast-from-var1832-to-var2220 var348))) ; Statement: $r16 = virtualinvoke r14.<jdk.internal.org.objectweb.asm.util.ASMifier: java.util.List getText()>() 
;(assert (var1366_add/328494887 var3177 (cast-from-var1366-to-var896 var1548))) ; Statement: interfaceinvoke $r15.<java.util.List: boolean add(java.lang.Object)>($r16) 

(declare-const var3177!1 var1366)
(declare-const var1548!1 var1366)
(define-const var2290 var1366 (text/-10557480 (cast-from-var1832-to-var2220 var2109!1))) ; Statement: $r17 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.util.List text> 
;(assert (var1366_add/328494887 var2290 (cast-from-String-to-var896 "}\n"))) ; Statement: interfaceinvoke $r17.<java.util.List: boolean add(java.lang.Object)>("}\n") 

(declare-const var2290!1 var1366)
(declare-const var3328 String)
 ; Statement: return r14 
(check-sat)


; {buf/-10557480=([jdk.internal.org.objectweb.asm.util.Printer], java.lang.StringBuffer), cast-from-var1832-to-var2220=([jdk.internal.org.objectweb.asm.util.ASMifier], jdk.internal.org.objectweb.asm.util.Printer), setLength/163251007=([java.lang.StringBuffer, int], void), append/1560614132=([java.lang.StringBuffer, java.lang.String], java.lang.StringBuffer), name/1045876480=([jdk.internal.org.objectweb.asm.util.ASMifier], java.lang.String), appendConstant/2119113448=([jdk.internal.org.objectweb.asm.util.ASMifier, java.lang.Object], void), cast-from-String-to-var896=([java.lang.String], java.lang.Object), append/-1166642301=([java.lang.StringBuffer, boolean], java.lang.StringBuffer), text/-10557480=([jdk.internal.org.objectweb.asm.util.Printer], java.util.List), toString/-222306083=([java.lang.StringBuffer], java.lang.String), var1366_add/328494887=([java.util.List, java.lang.Object], boolean), createASMifier/-631099411=([jdk.internal.org.objectweb.asm.util.ASMifier, java.lang.String, int], jdk.internal.org.objectweb.asm.util.ASMifier), getText/-142638630=([jdk.internal.org.objectweb.asm.util.Printer], java.util.List), cast-from-var1366-to-var896=([java.util.List], java.lang.Object)}
; {var1832=jdk.internal.org.objectweb.asm.util.ASMifier, var2109=r0, var3826=r7, var3684=null_type, var417=z0, var2220=jdk.internal.org.objectweb.asm.util.Printer, var3926=$r1, var747=0, var2547=$r2, var1258=$r3, var2428=$r5, var1827=$r4, var1909=$r6, var896=java.lang.Object, var1794=$r8, var480=$r9, var3185=$r10, var1366=java.util.List, var1266=$r12, var3190=$r11, var1910=$r13, var348=r14, var3177=$r15, var1548=$r16, var2290=$r17, var3328="}\n"}
; {jdk.internal.org.objectweb.asm.util.ASMifier=var1832, r0=var2109, r7=var3826, null_type=var3684, z0=var417, jdk.internal.org.objectweb.asm.util.Printer=var2220, $r1=var3926, 0=var747, $r2=var2547, $r3=var1258, $r5=var2428, $r4=var1827, $r6=var1909, java.lang.Object=var896, $r8=var1794, $r9=var480, $r10=var3185, java.util.List=var1366, $r12=var1266, $r11=var3190, $r13=var1910, r14=var348, $r15=var3177, $r16=var1548, $r17=var2290, "}\n"=var3328}
;seq <java.lang.StringBuffer: void setLength(int)>;	<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>;	<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>;	<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>;	<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>;	<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>;	<java.lang.StringBuffer: java.lang.StringBuffer append(boolean)>;	<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>;	<java.lang.StringBuffer: java.lang.String toString()>
;cnt {"<java.lang.StringBuffer: void setLength(int)>": 1,"<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>": 6,"<java.lang.StringBuffer: java.lang.StringBuffer append(boolean)>": 1,"<java.lang.StringBuffer: java.lang.String toString()>": 1}
;stmts r0 := @this: jdk.internal.org.objectweb.asm.util.ASMifier;	r7 := @parameter0: java.lang.String;	z0 := @parameter1: boolean;	$r1 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.lang.StringBuffer buf>;	virtualinvoke $r1.<java.lang.StringBuffer: void setLength(int)>(0);	$r2 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.lang.StringBuffer buf>;	$r3 = virtualinvoke $r2.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("{\n");	$r5 = virtualinvoke $r3.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("av0 = ");	$r4 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.lang.String name>;	$r6 = virtualinvoke $r5.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>($r4);	virtualinvoke $r6.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>(".visitAnnotation(");	virtualinvoke r0.<jdk.internal.org.objectweb.asm.util.ASMifier: void appendConstant(java.lang.Object)>(r7);	$r8 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.lang.StringBuffer buf>;	$r9 = virtualinvoke $r8.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>(", ");	$r10 = virtualinvoke $r9.<java.lang.StringBuffer: java.lang.StringBuffer append(boolean)>(z0);	virtualinvoke $r10.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>(");\n");	$r12 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.util.List text>;	$r11 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.lang.StringBuffer buf>;	$r13 = virtualinvoke $r11.<java.lang.StringBuffer: java.lang.String toString()>();	interfaceinvoke $r12.<java.util.List: boolean add(java.lang.Object)>($r13);	r14 = virtualinvoke r0.<jdk.internal.org.objectweb.asm.util.ASMifier: jdk.internal.org.objectweb.asm.util.ASMifier createASMifier(java.lang.String,int)>("av", 0);	$r15 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.util.List text>;	$r16 = virtualinvoke r14.<jdk.internal.org.objectweb.asm.util.ASMifier: java.util.List getText()>();	interfaceinvoke $r15.<java.util.List: boolean add(java.lang.Object)>($r16);	$r17 = r0.<jdk.internal.org.objectweb.asm.util.ASMifier: java.util.List text>;	interfaceinvoke $r17.<java.util.List: boolean add(java.lang.Object)>("}\n");	return r14
;block_num 1