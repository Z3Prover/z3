; origin: https://github.com/iscas-projects/SCB : closure-compiler/smt/method-com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageSchema__newSchemaForRawMessageInfo__512412896/28897-deviant-1.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var2228 0)
(declare-sort var308 0)
(declare-sort var792 0)
(declare-sort var1398 0)
(declare-sort var2499 0)
(declare-sort var2201 0)
(declare-sort var1955 0)
(declare-sort var3775 0)
(declare-sort var1107 0)
(declare-sort var2562 0)
(declare-sort var1031 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun getSyntax/1678635008 (var2228) var1955)
(declare-fun getStringInfo/1706019720 (var2228) String)
(define-fun length/-134980193 ((s String)) Int (str.len s))
(define-fun charAt/698050440 ((s String) (index Int)) Int (str.to_code (str.at s index)))
(define-fun cast-from-Int-to-Int ((arg Int)) Int arg)
(declare-fun getObjects/1665629231 (var2228) (Array Int var2562))
(declare-fun getDefaultInstance/380878571 (var2228) var1031)
(declare-fun getClass/1258963082 (var2562) ClassObject)
(declare-fun cast-from-var1031-to-var2562 (var1031) var2562)
(declare-fun arr-Int-init () (Array Int Int))
(declare-fun arr-var2562-init () (Array Int var2562))
(declare-fun var3775-init () var3775)
(declare-fun <init>/-1806030460 (var3775 (Array Int Int) (Array Int var2562) Int Int var1031 Bool Bool (Array Int Int) Int Int var308 var792 var1398 var2499 var2201) void)
(declare-const null-var2228 var2228)
(declare-const null-var308 var308)
(declare-const null-var792 var792)
(declare-const null-var1398 var1398)
(declare-const null-var2499 var2499)
(declare-const null-var2201 var2201)
(declare-const var1955-PROTO3 var1955)
(declare-const var3775-EMPTY_INT_ARRAY (Array Int Int))
(declare-const var3775-UNSAFE var1107)
(declare-const var3807 var2228) ; Statement: r0 := @parameter0: com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo 
(assert (not (= var3807 null-var2228)))
(declare-const var2654 var308) ; Statement: r4 := @parameter1: com.google.javascript.jscomp.jarjar.com.google.protobuf.NewInstanceSchema 
(assert (not (= var2654 null-var308)))
(declare-const var638 var792) ; Statement: r5 := @parameter2: com.google.javascript.jscomp.jarjar.com.google.protobuf.ListFieldSchema 
(assert (not (= var638 null-var792)))
(declare-const var2812 var1398) ; Statement: r6 := @parameter3: com.google.javascript.jscomp.jarjar.com.google.protobuf.UnknownFieldSchema 
(assert (not (= var2812 null-var1398)))
(declare-const var1150 var2499) ; Statement: r7 := @parameter4: com.google.javascript.jscomp.jarjar.com.google.protobuf.ExtensionSchema 
(assert (not (= var1150 null-var2499)))
(declare-const var2386 var2201) ; Statement: r8 := @parameter5: com.google.javascript.jscomp.jarjar.com.google.protobuf.MapFieldSchema 
(assert (not (= var2386 null-var2201)))
(assert true)
(define-const var3133 var1955 (getSyntax/1678635008 var3807)) ; Statement: $r2 = virtualinvoke r0.<com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo: com.google.javascript.jscomp.jarjar.com.google.protobuf.ProtoSyntax getSyntax()>() 
(define-const var3353 var1955 var1955-PROTO3) ; Statement: $r1 = <com.google.javascript.jscomp.jarjar.com.google.protobuf.ProtoSyntax: com.google.javascript.jscomp.jarjar.com.google.protobuf.ProtoSyntax PROTO3> 
 ; Statement: if $r2 != $r1 goto $z3 = 0 
(assert (not (not (= var3133 var3353)))) ; Negate: Cond: $r2 != $r1  
(define-const var2639 Bool (ite (= 1 1) true false)) ; Statement: $z3 = 1 
 ; Statement: goto [?= z0 = $z3] 
(assert true) ; Non Conditional
(define-const var3030 Bool var2639) ; Statement: z0 = $z3 
(assert true)
(define-const var3639 String (getStringInfo/1706019720 var3807)) ; Statement: $r24 = virtualinvoke r0.<com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo: java.lang.String getStringInfo()>() 
(assert true)
(define-const var3154 Int (length/-134980193 var3639)) ; Statement: $i125 = virtualinvoke $r24.<java.lang.String: int length()>() 
(define-const var3717 Int 1) ; Statement: i127 = 1 
(assert (and true (and (> (str.len var3639) 0) (<= 0 0))))
(define-const var2590 Int (charAt/698050440 var3639 0)) ; Statement: $c126 = virtualinvoke $r24.<java.lang.String: char charAt(int)>(0) 
(define-const var3690 Int (cast-from-Int-to-Int var2590)) ; Statement: $i212 = (int) $c126 
(define-const var34 Int (cast-from-Int-to-Int 55296)) ; Statement: $i214 = (int) 55296 
 ; Statement: if $i212 < $i214 goto i128 = i127 + 1 
(assert (< var3690 var34)) ; Cond: $i212 < $i214 
(define-const var3118 Int (+ var3717 1)) ; Statement: i128 = i127 + 1 
(assert (not (and true (and (> (str.len var3639) var3717) (<= 0 var3717)))))
(check-sat)


; {getSyntax/1678635008=([com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo], com.google.javascript.jscomp.jarjar.com.google.protobuf.ProtoSyntax), getStringInfo/1706019720=([com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo], java.lang.String), length/-134980193=([java.lang.String], int), charAt/698050440=([java.lang.String, int], char), cast-from-Int-to-Int=([char], int), getObjects/1665629231=([com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo], java.lang.Object[]), getDefaultInstance/380878571=([com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo], com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageLite), getClass/1258963082=([java.lang.Object], java.lang.Class), cast-from-var1031-to-var2562=([com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageLite], java.lang.Object), arr-Int-init=([], int[]), arr-var2562-init=([], java.lang.Object[]), var3775-init=([], com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageSchema), <init>/-1806030460=([com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageSchema, int[], java.lang.Object[], int, int, com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageLite, boolean, boolean, int[], int, int, com.google.javascript.jscomp.jarjar.com.google.protobuf.NewInstanceSchema, com.google.javascript.jscomp.jarjar.com.google.protobuf.ListFieldSchema, com.google.javascript.jscomp.jarjar.com.google.protobuf.UnknownFieldSchema, com.google.javascript.jscomp.jarjar.com.google.protobuf.ExtensionSchema, com.google.javascript.jscomp.jarjar.com.google.protobuf.MapFieldSchema], void)}
; {var2228=com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo, var3807=r0, var308=com.google.javascript.jscomp.jarjar.com.google.protobuf.NewInstanceSchema, var2654=r4, var792=com.google.javascript.jscomp.jarjar.com.google.protobuf.ListFieldSchema, var638=r5, var1398=com.google.javascript.jscomp.jarjar.com.google.protobuf.UnknownFieldSchema, var2812=r6, var2499=com.google.javascript.jscomp.jarjar.com.google.protobuf.ExtensionSchema, var1150=r7, var2201=com.google.javascript.jscomp.jarjar.com.google.protobuf.MapFieldSchema, var2386=r8, var1955=com.google.javascript.jscomp.jarjar.com.google.protobuf.ProtoSyntax, var3133=$r2, var3353=$r1, var2639=$z3, var3030=z0, var3639=$r24, var3154=$i125, var3717=i127, var2590=$c126, var3690=$i212, var34=$i214, var3118=i128, var1137=$c124, var467=$i218, var3530=i129, var375=$i219, var3731=$i221, var1088=i132, var24=i133, var3505=i134, var1596=i135, var1522=i136, var1538=i137, var3775=com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageSchema, var2909=r25, var3700=i138, var1107=sun.misc.Unsafe, var2397=$r26, var2562=java.lang.Object, var1549=$r27, var2537=i172, var1031=com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageLite, var474=$r28, var1812=$r29, var1294=$i173, var2008=$r30, var698=$i174, var3982=$r31, var1905=i175, var1094=i176, var928=i177, var3042=$r37, var3843=$r9, var3559=$i3, var968=0}
; {com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo=var2228, r0=var3807, com.google.javascript.jscomp.jarjar.com.google.protobuf.NewInstanceSchema=var308, r4=var2654, com.google.javascript.jscomp.jarjar.com.google.protobuf.ListFieldSchema=var792, r5=var638, com.google.javascript.jscomp.jarjar.com.google.protobuf.UnknownFieldSchema=var1398, r6=var2812, com.google.javascript.jscomp.jarjar.com.google.protobuf.ExtensionSchema=var2499, r7=var1150, com.google.javascript.jscomp.jarjar.com.google.protobuf.MapFieldSchema=var2201, r8=var2386, com.google.javascript.jscomp.jarjar.com.google.protobuf.ProtoSyntax=var1955, $r2=var3133, $r1=var3353, $z3=var2639, z0=var3030, $r24=var3639, $i125=var3154, i127=var3717, $c126=var2590, $i212=var3690, $i214=var34, i128=var3118, $c124=var1137, $i218=var467, i129=var3530, $i219=var375, $i221=var3731, i132=var1088, i133=var24, i134=var3505, i135=var1596, i136=var1522, i137=var1538, com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageSchema=var3775, r25=var2909, i138=var3700, sun.misc.Unsafe=var1107, $r26=var2397, java.lang.Object=var2562, $r27=var1549, i172=var2537, com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageLite=var1031, $r28=var474, $r29=var1812, $i173=var1294, $r30=var2008, $i174=var698, $r31=var3982, i175=var1905, i176=var1094, i177=var928, $r37=var3042, $r9=var3843, $i3=var3559, 0=var968}
;seq <java.lang.String: int length()>;	<java.lang.String: char charAt(int)>;	<java.lang.String: char charAt(int)>
;cnt {"<java.lang.String: int length()>": 1,"<java.lang.String: char charAt(int)>": 2}
;stmts r0 := @parameter0: com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo;	r4 := @parameter1: com.google.javascript.jscomp.jarjar.com.google.protobuf.NewInstanceSchema;	r5 := @parameter2: com.google.javascript.jscomp.jarjar.com.google.protobuf.ListFieldSchema;	r6 := @parameter3: com.google.javascript.jscomp.jarjar.com.google.protobuf.UnknownFieldSchema;	r7 := @parameter4: com.google.javascript.jscomp.jarjar.com.google.protobuf.ExtensionSchema;	r8 := @parameter5: com.google.javascript.jscomp.jarjar.com.google.protobuf.MapFieldSchema;	$r2 = virtualinvoke r0.<com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo: com.google.javascript.jscomp.jarjar.com.google.protobuf.ProtoSyntax getSyntax()>();	$r1 = <com.google.javascript.jscomp.jarjar.com.google.protobuf.ProtoSyntax: com.google.javascript.jscomp.jarjar.com.google.protobuf.ProtoSyntax PROTO3>;	if $r2 != $r1 goto $z3 = 0;	$z3 = 1;	goto [?= z0 = $z3];	z0 = $z3;	$r24 = virtualinvoke r0.<com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo: java.lang.String getStringInfo()>();	$i125 = virtualinvoke $r24.<java.lang.String: int length()>();	i127 = 1;	$c126 = virtualinvoke $r24.<java.lang.String: char charAt(int)>(0);	$i212 = (int) $c126;	$i214 = (int) 55296;	if $i212 < $i214 goto i128 = i127 + 1;	i128 = i127 + 1;	$c124 = virtualinvoke $r24.<java.lang.String: char charAt(int)>(i127);	$i218 = (int) $c124;	i129 = $i218;	$i219 = (int) $c124;	$i221 = (int) 55296;	if $i219 < $i221 goto (branch);	if i129 != 0 goto i139 = i128 + 1;	i132 = 0;	i133 = 0;	i134 = 0;	i135 = 0;	i136 = 0;	i137 = 0;	r25 = <com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageSchema: int[] EMPTY_INT_ARRAY>;	i138 = 0;	goto [?= $r26 = <com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageSchema: sun.misc.Unsafe UNSAFE>];	$r26 = <com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageSchema: sun.misc.Unsafe UNSAFE>;	$r27 = virtualinvoke r0.<com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo: java.lang.Object[] getObjects()>();	i172 = 0;	$r28 = virtualinvoke r0.<com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo: com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageLite getDefaultInstance()>();	$r29 = virtualinvoke $r28.<java.lang.Object: java.lang.Class getClass()>();	$i173 = i135 * 3;	$r30 = newarray (int)[$i173];	$i174 = i135 * 2;	$r31 = newarray (java.lang.Object)[$i174];	i175 = i137;	i176 = i137 + i136;	i177 = 0;	if i128 >= $i125 goto $r37 = new com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageSchema;	$r37 = new com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageSchema;	$r9 = virtualinvoke r0.<com.google.javascript.jscomp.jarjar.com.google.protobuf.RawMessageInfo: com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageLite getDefaultInstance()>();	$i3 = i137 + i136;	specialinvoke $r37.<com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageSchema: void <init>(int[],java.lang.Object[],int,int,com.google.javascript.jscomp.jarjar.com.google.protobuf.MessageLite,boolean,boolean,int[],int,int,com.google.javascript.jscomp.jarjar.com.google.protobuf.NewInstanceSchema,com.google.javascript.jscomp.jarjar.com.google.protobuf.ListFieldSchema,com.google.javascript.jscomp.jarjar.com.google.protobuf.UnknownFieldSchema,com.google.javascript.jscomp.jarjar.com.google.protobuf.ExtensionSchema,com.google.javascript.jscomp.jarjar.com.google.protobuf.MapFieldSchema)>($r30, $r31, i133, i134, $r9, z0, 0, r25, i137, $i3, r4, r5, r6, r7, r8);	return $r37
;block_num 9