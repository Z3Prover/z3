; origin: https://github.com/iscas-projects/SCB : fastjson/smt/method-com.alibaba.fastjson2.writer.ObjectWriterCreatorASM__jitWriter__-325643115/6211.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3704 0)
(declare-sort var2021 0)
(declare-sort var2953 0)
(declare-sort var219 0)
(declare-sort var329 0)
(declare-sort var1858 0)
(declare-sort var2655 0)
(declare-sort var412 0)
(declare-sort var3883 0)
(declare-sort var1914 0)
(declare-sort var818 0)
(declare-sort var3912 0)
(declare-sort var3864 0)
(declare-sort var3083 0)
(declare-sort var300 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-const var3704!class ClassObject)
(declare-fun var329-init () var329)
(declare-fun <init>/1561585841 (var329 var1858) void)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun incrementAndGet/636047358 (var412) Int)
(declare-fun append/-901862667 (String Int) String)
(declare-fun var219_size/-959786421 (var219) Int)
(define-fun append/-1001720160 ((s String) (tail Int)) String (str.++ s (str.from_int tail)))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun getPackage/-1841711535 (ClassObject) var3883)
(declare-fun visit/1245821975 (var329 Int Int String String (Array Int String)) void)
(declare-fun genFields/-1901790442 (var3704 var219 var329 String) void)
(declare-fun genMethodInit/736566045 (var3704 var219 var329 String String) void)
(declare-fun genMethodWriteJSONB/-809205014 (var3704 var2021 ClassObject var219 var329 String Int) void)
(declare-fun mask/-2077367092 (var818) Int)
(declare-fun genMethodWriteArrayMapping/749331648 (var3704 var2021 String ClassObject Int var219 var329 String) void)
(declare-fun genMethodWriteArrayMappingJSONB/3756667 (var3704 var2021 ClassObject Int var219 var329 String Int) void)
(declare-fun toByteArray/1561254549 (var329) (Array Int Int))
(declare-fun classLoader/1229018461 (var3704) var3912)
(declare-fun getLength-Arr-Int-1 ((Array Int Int)) Int)
(declare-fun defineClassPublic/-885393557 (var3912 String (Array Int Int) Int Int) ClassObject)
(declare-fun var3083-init () var3083)
(declare-fun append/-1031950772 (String var300) String)
(declare-fun cast-from-ClassObject-to-var300 (ClassObject) var300)
(declare-fun <init>/-743866570 (var3083 String var3864) void)
(declare-const null-var3704 var3704)
(declare-const null-ClassObject ClassObject)
(declare-const null-var2021 var2021)
(declare-const null-var2953 var2953)
(declare-const null-var219 var219)
(declare-const null-Int Int)
(declare-const null-NullType var2655)
(declare-const null-var1858 var1858)
(declare-const var3704-seed var412)
(declare-const null-var3883 var3883)
(declare-const var1914-TYPE_OBJECT_WRITER_6 String)
(declare-const var3704-INTERFACES (Array Int String))
(declare-const var818-BeanToArray var818)
(declare-const null-var3864 var3864)
(declare-const var790 var3704) ; Statement: r15 := @this: com.alibaba.fastjson2.writer.ObjectWriterCreatorASM 
(assert (not (= var790 null-var3704)))
(declare-const var1497 ClassObject) ; Statement: r7 := @parameter0: java.lang.Class 
(assert (not (= var1497 null-ClassObject)))
(declare-const var998 var2021) ; Statement: r16 := @parameter1: com.alibaba.fastjson2.writer.ObjectWriterProvider 
(assert (not (= var998 null-var2021)))
(declare-const var2239 var2953) ; Statement: r21 := @parameter2: com.alibaba.fastjson2.codec.BeanInfo 
(assert (not (= var2239 null-var2953)))
(declare-const var2243 var219) ; Statement: r5 := @parameter3: java.util.List 
(assert (not (= var2243 null-var219)))
(declare-const var3858 Int) ; Statement: l3 := @parameter4: long 
(assert (not (= var3858 null-Int)))
(define-const var2876 var329 var329-init) ; Statement: $r49 = new com.alibaba.fastjson2.internal.asm.ClassWriter 
(assert true)
;(assert (<init>/1561585841 var2876 null-var1858)) ; Statement: specialinvoke $r49.<com.alibaba.fastjson2.internal.asm.ClassWriter: void <init>(java.util.function.Function)>(null) 

(declare-const var2876!1 var329)
(declare-const var67 var2655)
(define-const var981 String String-init) ; Statement: $r50 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var981)) ; Statement: specialinvoke $r50.<java.lang.StringBuilder: void <init>()>() 
(declare-const var981!1 String)
(assert (= var981!1 ""))
(assert true)
(define-const var1343 String (append/672562846 var981!1 "OWG_")) ; Statement: $r3 = virtualinvoke $r50.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("OWG_") 
(declare-const var981!2 String)
(assert (= var981!2 (str.++ var981!1 "OWG_")))
(define-const var3506 var412 var3704-seed) ; Statement: $r2 = <com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: java.util.concurrent.atomic.AtomicLong seed> 
(assert true)
(define-const var128 Int (incrementAndGet/636047358 var3506)) ; Statement: $l0 = virtualinvoke $r2.<java.util.concurrent.atomic.AtomicLong: long incrementAndGet()>() 
(assert true)
(define-const var2221 String (append/-901862667 var1343 var128)) ; Statement: $r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(long)>($l0) 
(declare-const var1343!1 String)
(assert (str.prefixof var1343 var1343!1))
(assert true)
(define-const var2725 String (append/672562846 var2221 "_")) ; Statement: $r6 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("_") 
(declare-const var2221!1 String)
(assert (= var2221!1 (str.++ var2221 "_")))
(define-const var3104 Int (var219_size/-959786421 var2243)) ; Statement: $i1 = interfaceinvoke r5.<java.util.List: int size()>() 
(assert true)
(define-const var167 String (append/-1001720160 var2725 var3104)) ; Statement: $r12 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i1) 
(declare-const var2725!1 String)
(assert (str.prefixof var2725 var2725!1))
 ; Statement: if r7 != null goto $r51 = new java.lang.StringBuilder 
(assert (not (not (= var1497 null-ClassObject)))) ; Negate: Cond: r7 != null  
(define-const var1212 String "") ; Statement: $r41 = "" 
 ; Statement: goto [?= $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r41)] 
(assert true) ; Non Conditional
(assert true)
(define-const var444 String (append/672562846 var167 var1212)) ; Statement: $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r41) 
(declare-const var167!1 String)
(assert (= var167!1 (str.++ var167 var1212)))
(assert true)
(define-const var1265 String (toString/-2075883882 var444)) ; Statement: $r33 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.String toString()>() 
(define-const var2901 ClassObject var3704!class) ; Statement: $r14 = class "Lcom/alibaba/fastjson2/writer/ObjectWriterCreatorASM;" 
(assert true)
(define-const var2010 var3883 (getPackage/-1841711535 var2901)) ; Statement: $r34 = virtualinvoke $r14.<java.lang.Class: java.lang.Package getPackage()>() 
 ; Statement: if $r34 == null goto r45 = $r33 
(assert (= var2010 null-var3883)) ; Cond: $r34 == null 
(define-const var3792 String var1265) ; Statement: r45 = $r33 
(define-const var1175 String var1265) ; Statement: r44 = $r33 
(assert true) ; Non Conditional
(define-const var32 Int (var219_size/-959786421 var2243)) ; Statement: $i2 = interfaceinvoke r5.<java.util.List: int size()>() 
 ; Statement: tableswitch($i2) {     case 1: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_1>;     case 2: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_2>;     case 3: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_3>;     case 4: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_4>;     case 5: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_5>;     case 6: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_6>;     case 7: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_7>;     case 8: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_8>;     case 9: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_9>;     case 10: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_10>;     case 11: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_11>;     case 12: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_12>;     default: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_ADAPTER>; } 
(assert (and (= var32 6) (and (not (= var32 5)) (and (not (= var32 4)) (and (not (= var32 3)) (and (not (= var32 2)) (and (not (= var32 1)) true))))))) ; Intersect: Cond: $i2 == 6  and Intersect: Negate: Cond: $i2 == 5   and Intersect: Negate: Cond: $i2 == 4   and Intersect: Negate: Cond: $i2 == 3   and Intersect: Negate: Cond: $i2 == 2   and Intersect: Negate: Cond: $i2 == 1   and Non Conditional      
(define-const var1558 String var1914-TYPE_OBJECT_WRITER_6) ; Statement: r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_6> 
 ; Statement: goto [?= $r47 = <com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: java.lang.String[] INTERFACES>] 
(assert true) ; Non Conditional
(define-const var1666 (Array Int String) var3704-INTERFACES) ; Statement: $r47 = <com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: java.lang.String[] INTERFACES> 
(assert true)
;(assert (visit/1245821975 var2876!1 52 49 var3792 var1558 var1666)) ; Statement: virtualinvoke $r49.<com.alibaba.fastjson2.internal.asm.ClassWriter: void visit(int,int,java.lang.String,java.lang.String,java.lang.String[])>(52, 49, r45, r46, $r47) 

(declare-const var2876!2 var329)
(declare-const var2369 Int)
(declare-const var2993 Int)
(declare-const var3792!1 String)
(declare-const var1558!1 String)
(declare-const var1666!1 (Array Int String))
(assert true)
;(assert (genFields/-1901790442 var790 var2243 var2876!2 var1558!1)) ; Statement: specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genFields(java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String)>(r5, $r49, r46) 

(declare-const var790!1 var3704)
(declare-const var2243!1 var219)
(declare-const var2876!3 var329)
(declare-const var1558!2 String)
(assert true)
;(assert (genMethodInit/736566045 var790!1 var2243!1 var2876!3 var3792!1 var1558!2)) ; Statement: specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodInit(java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String,java.lang.String)>(r5, $r49, r45, r46) 

(declare-const var790!2 var3704)
(declare-const var2243!2 var219)
(declare-const var2876!4 var329)
(declare-const var3792!2 String)
(declare-const var1558!3 String)
(assert true)
;(assert (genMethodWriteJSONB/-809205014 var790!2 var998 var1497 var2243!2 var2876!4 var3792!2 var3858)) ; Statement: specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWriteJSONB(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.Class,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String,long)>(r16, r7, r5, $r49, r45, l3) 

(declare-const var790!3 var3704)
(declare-const var998!1 var2021)
(declare-const var1497!1 ClassObject)
(declare-const var2243!3 var219)
(declare-const var2876!5 var329)
(declare-const var3792!3 String)
(declare-const var3858!1 Int)
(define-const var1811 var818 var818-BeanToArray) ; Statement: $r48 = <com.alibaba.fastjson2.JSONWriter$Feature: com.alibaba.fastjson2.JSONWriter$Feature BeanToArray> 
(define-const var1070 Int (mask/-2077367092 var1811)) ; Statement: $l14 = $r48.<com.alibaba.fastjson2.JSONWriter$Feature: long mask> 
(define-const var1098 Int (bv2nat (bvand ((_ int2bv 64) var3858!1) ((_ int2bv 64) var1070)))) ; Statement: $l15 = l3 & $l14 
(define-const var1440 Int (ite (> var1098 0) 1 (ite (< var1098 0) (- 1) 0))) ; Statement: $b16 = $l15 cmp 0L 
 ; Statement: if $b16 == 0 goto specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWrite(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.Class,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String,long)>(r16, r7, r5, $r49, r45, l3) 
(assert (not (= var1440 0))) ; Negate: Cond: $b16 == 0  
(assert true)
;(assert (genMethodWriteArrayMapping/749331648 var790!3 var998!1 "write" var1497!1 var3858!1 var2243!3 var2876!5 var3792!3)) ; Statement: specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWriteArrayMapping(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.String,java.lang.Class,long,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String)>(r16, "write", r7, l3, r5, $r49, r45) 

(declare-const var790!4 var3704)
(declare-const var998!2 var2021)
(declare-const var2118 String)
(declare-const var1497!2 ClassObject)
(declare-const var3858!2 Int)
(declare-const var2243!4 var219)
(declare-const var2876!6 var329)
(declare-const var3792!4 String)
 ; Statement: goto [?= specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWriteArrayMappingJSONB(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.Class,long,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String,long)>(r16, r7, l3, r5, $r49, r45, l3)] 
(assert true) ; Non Conditional
(assert true)
;(assert (genMethodWriteArrayMappingJSONB/3756667 var790!4 var998!2 var1497!2 var3858!2 var2243!4 var2876!6 var3792!4 var3858!2)) ; Statement: specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWriteArrayMappingJSONB(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.Class,long,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String,long)>(r16, r7, l3, r5, $r49, r45, l3) 

(declare-const var790!5 var3704)
(declare-const var998!3 var2021)
(declare-const var1497!3 ClassObject)
(declare-const var3858!3 Int)
(declare-const var2243!5 var219)
(declare-const var2876!7 var329)
(declare-const var3792!5 String)
(declare-const var3858!4 Int)
(assert true)
;(assert (genMethodWriteArrayMapping/749331648 var790!5 var998!3 "writeArrayMapping" var1497!3 var3858!4 var2243!5 var2876!7 var3792!5)) ; Statement: specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWriteArrayMapping(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.String,java.lang.Class,long,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String)>(r16, "writeArrayMapping", r7, l3, r5, $r49, r45) 

(declare-const var790!6 var3704)
(declare-const var998!4 var2021)
(declare-const var1680 String)
(declare-const var1497!4 ClassObject)
(declare-const var3858!5 Int)
(declare-const var2243!6 var219)
(declare-const var2876!8 var329)
(declare-const var3792!6 String)
(assert true)
(define-const var1323 (Array Int Int) (toByteArray/1561254549 var2876!8)) ; Statement: $r27 = virtualinvoke $r49.<com.alibaba.fastjson2.internal.asm.ClassWriter: byte[] toByteArray()>() 
(define-const var3660 var3912 (classLoader/1229018461 var790!6)) ; Statement: $r17 = r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: com.alibaba.fastjson2.util.DynamicClassLoader classLoader> 
(define-const var1131 Int (getLength-Arr-Int-1 var1323)) ; Statement: $i4 = lengthof $r27 
(assert true)
(define-const var980 ClassObject (defineClassPublic/-885393557 var3660 var1175 var1323 0 var1131)) ; Statement: $r28 = virtualinvoke $r17.<com.alibaba.fastjson2.util.DynamicClassLoader: java.lang.Class defineClassPublic(java.lang.String,byte[],int,int)>(r44, $r27, 0, $i4) 
(assert true) ; Handling Exception: java.lang.Throwable 
(declare-const var554 var3864) ; Statement: $r35 := @caughtexception 
(assert (not (= var554 null-var3864)))
(define-const var1509 var3083 var3083-init) ; Statement: $r55 = new com.alibaba.fastjson2.JSONException 
(define-const var778 String String-init) ; Statement: $r54 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var778)) ; Statement: specialinvoke $r54.<java.lang.StringBuilder: void <init>()>() 
(declare-const var778!1 String)
(assert (= var778!1 ""))
(assert true)
(define-const var333 String (append/672562846 var778!1 "create objectWriter error, objectType ")) ; Statement: $r38 = virtualinvoke $r54.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("create objectWriter error, objectType ") 
(declare-const var778!2 String)
(assert (= var778!2 (str.++ var778!1 "create objectWriter error, objectType ")))
(assert true)
(define-const var3749 String (append/-1031950772 var333 (cast-from-ClassObject-to-var300 var1497!4))) ; Statement: $r39 = virtualinvoke $r38.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r7) 
(declare-const var333!1 String)
(assert (str.prefixof var333 var333!1))
(assert true)
(define-const var1687 String (toString/-2075883882 var3749)) ; Statement: $r40 = virtualinvoke $r39.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert true)
;(assert (<init>/-743866570 var1509 var1687 var554)) ; Statement: specialinvoke $r55.<com.alibaba.fastjson2.JSONException: void <init>(java.lang.String,java.lang.Throwable)>($r40, $r35) 

(declare-const var1509!1 var3083)
(declare-const var1687!1 String)
(declare-const var554!1 var3864)
 ; Statement: throw $r55 
(check-sat)


; {var329-init=([], com.alibaba.fastjson2.internal.asm.ClassWriter), <init>/1561585841=([com.alibaba.fastjson2.internal.asm.ClassWriter, java.util.function.Function], void), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), incrementAndGet/636047358=([java.util.concurrent.atomic.AtomicLong], long), append/-901862667=([java.lang.StringBuilder, long], java.lang.StringBuilder), var219_size/-959786421=([java.util.List], int), append/-1001720160=([java.lang.StringBuilder, int], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), getPackage/-1841711535=([java.lang.Class], java.lang.Package), visit/1245821975=([com.alibaba.fastjson2.internal.asm.ClassWriter, int, int, java.lang.String, java.lang.String, java.lang.String[]], void), genFields/-1901790442=([com.alibaba.fastjson2.writer.ObjectWriterCreatorASM, java.util.List, com.alibaba.fastjson2.internal.asm.ClassWriter, java.lang.String], void), genMethodInit/736566045=([com.alibaba.fastjson2.writer.ObjectWriterCreatorASM, java.util.List, com.alibaba.fastjson2.internal.asm.ClassWriter, java.lang.String, java.lang.String], void), genMethodWriteJSONB/-809205014=([com.alibaba.fastjson2.writer.ObjectWriterCreatorASM, com.alibaba.fastjson2.writer.ObjectWriterProvider, java.lang.Class, java.util.List, com.alibaba.fastjson2.internal.asm.ClassWriter, java.lang.String, long], void), mask/-2077367092=([com.alibaba.fastjson2.JSONWriter$Feature], long), genMethodWriteArrayMapping/749331648=([com.alibaba.fastjson2.writer.ObjectWriterCreatorASM, com.alibaba.fastjson2.writer.ObjectWriterProvider, java.lang.String, java.lang.Class, long, java.util.List, com.alibaba.fastjson2.internal.asm.ClassWriter, java.lang.String], void), genMethodWriteArrayMappingJSONB/3756667=([com.alibaba.fastjson2.writer.ObjectWriterCreatorASM, com.alibaba.fastjson2.writer.ObjectWriterProvider, java.lang.Class, long, java.util.List, com.alibaba.fastjson2.internal.asm.ClassWriter, java.lang.String, long], void), toByteArray/1561254549=([com.alibaba.fastjson2.internal.asm.ClassWriter], byte[]), classLoader/1229018461=([com.alibaba.fastjson2.writer.ObjectWriterCreatorASM], com.alibaba.fastjson2.util.DynamicClassLoader), getLength-Arr-Int-1=([byte[]], int), defineClassPublic/-885393557=([com.alibaba.fastjson2.util.DynamicClassLoader, java.lang.String, byte[], int, int], java.lang.Class), var3083-init=([], com.alibaba.fastjson2.JSONException), append/-1031950772=([java.lang.StringBuilder, java.lang.Object], java.lang.StringBuilder), cast-from-ClassObject-to-var300=([java.lang.Class], java.lang.Object), <init>/-743866570=([com.alibaba.fastjson2.JSONException, java.lang.String, java.lang.Throwable], void)}
; {var3704=com.alibaba.fastjson2.writer.ObjectWriterCreatorASM, var790=r15, var1497=r7, var2021=com.alibaba.fastjson2.writer.ObjectWriterProvider, var998=r16, var2953=com.alibaba.fastjson2.codec.BeanInfo, var2239=r21, var219=java.util.List, var2243=r5, var3858=l3, var329=com.alibaba.fastjson2.internal.asm.ClassWriter, var2876=$r49, var1858=java.util.function.Function, var67=null, var2655=null_type, var981=$r50, var1343=$r3, var412=java.util.concurrent.atomic.AtomicLong, var3506=$r2, var128=$l0, var2221=$r4, var2725=$r6, var3104=$i1, var167=$r12, var1212=$r41, var444=$r13, var1265=$r33, var2901=$r14, var3883=java.lang.Package, var2010=$r34, var3792=r45, var1175=r44, var32=$i2, var1914=com.alibaba.fastjson2.internal.asm.ASMUtils, var1558=r46, var1666=$r47, var2369=52, var2993=49, var818=com.alibaba.fastjson2.JSONWriter$Feature, var1811=$r48, var1070=$l14, var1098=$l15, var1440=$b16, var2118="write", var1680="writeArrayMapping", var1323=$r27, var3912=com.alibaba.fastjson2.util.DynamicClassLoader, var3660=$r17, var1131=$i4, var980=$r28, var3864=java.lang.Throwable, var554=$r35, var3083=com.alibaba.fastjson2.JSONException, var1509=$r55, var778=$r54, var333=$r38, var300=java.lang.Object, var3749=$r39, var1687=$r40}
; {com.alibaba.fastjson2.writer.ObjectWriterCreatorASM=var3704, r15=var790, r7=var1497, com.alibaba.fastjson2.writer.ObjectWriterProvider=var2021, r16=var998, com.alibaba.fastjson2.codec.BeanInfo=var2953, r21=var2239, java.util.List=var219, r5=var2243, l3=var3858, com.alibaba.fastjson2.internal.asm.ClassWriter=var329, $r49=var2876, java.util.function.Function=var1858, null=var67, null_type=var2655, $r50=var981, $r3=var1343, java.util.concurrent.atomic.AtomicLong=var412, $r2=var3506, $l0=var128, $r4=var2221, $r6=var2725, $i1=var3104, $r12=var167, $r41=var1212, $r13=var444, $r33=var1265, $r14=var2901, java.lang.Package=var3883, $r34=var2010, r45=var3792, r44=var1175, $i2=var32, com.alibaba.fastjson2.internal.asm.ASMUtils=var1914, r46=var1558, $r47=var1666, 52=var2369, 49=var2993, com.alibaba.fastjson2.JSONWriter$Feature=var818, $r48=var1811, $l14=var1070, $l15=var1098, $b16=var1440, "write"=var2118, "writeArrayMapping"=var1680, $r27=var1323, com.alibaba.fastjson2.util.DynamicClassLoader=var3912, $r17=var3660, $i4=var1131, $r28=var980, java.lang.Throwable=var3864, $r35=var554, com.alibaba.fastjson2.JSONException=var3083, $r55=var1509, $r54=var778, $r38=var333, java.lang.Object=var300, $r39=var3749, $r40=var1687}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(long)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(int)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>;	<java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 2,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 4,"<java.lang.StringBuilder: java.lang.StringBuilder append(long)>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(int)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 2,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>": 1}
;stmts r15 := @this: com.alibaba.fastjson2.writer.ObjectWriterCreatorASM;	r7 := @parameter0: java.lang.Class;	r16 := @parameter1: com.alibaba.fastjson2.writer.ObjectWriterProvider;	r21 := @parameter2: com.alibaba.fastjson2.codec.BeanInfo;	r5 := @parameter3: java.util.List;	l3 := @parameter4: long;	$r49 = new com.alibaba.fastjson2.internal.asm.ClassWriter;	specialinvoke $r49.<com.alibaba.fastjson2.internal.asm.ClassWriter: void <init>(java.util.function.Function)>(null);	$r50 = new java.lang.StringBuilder;	specialinvoke $r50.<java.lang.StringBuilder: void <init>()>();	$r3 = virtualinvoke $r50.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("OWG_");	$r2 = <com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: java.util.concurrent.atomic.AtomicLong seed>;	$l0 = virtualinvoke $r2.<java.util.concurrent.atomic.AtomicLong: long incrementAndGet()>();	$r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(long)>($l0);	$r6 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("_");	$i1 = interfaceinvoke r5.<java.util.List: int size()>();	$r12 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i1);	if r7 != null goto $r51 = new java.lang.StringBuilder;	$r41 = "";	goto [?= $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r41)];	$r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r41);	$r33 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.String toString()>();	$r14 = class "Lcom/alibaba/fastjson2/writer/ObjectWriterCreatorASM;";	$r34 = virtualinvoke $r14.<java.lang.Class: java.lang.Package getPackage()>();	if $r34 == null goto r45 = $r33;	r45 = $r33;	r44 = $r33;	$i2 = interfaceinvoke r5.<java.util.List: int size()>();	tableswitch($i2) {     case 1: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_1>;     case 2: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_2>;     case 3: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_3>;     case 4: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_4>;     case 5: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_5>;     case 6: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_6>;     case 7: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_7>;     case 8: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_8>;     case 9: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_9>;     case 10: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_10>;     case 11: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_11>;     case 12: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_12>;     default: goto r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_ADAPTER>; };	r46 = <com.alibaba.fastjson2.internal.asm.ASMUtils: java.lang.String TYPE_OBJECT_WRITER_6>;	goto [?= $r47 = <com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: java.lang.String[] INTERFACES>];	$r47 = <com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: java.lang.String[] INTERFACES>;	virtualinvoke $r49.<com.alibaba.fastjson2.internal.asm.ClassWriter: void visit(int,int,java.lang.String,java.lang.String,java.lang.String[])>(52, 49, r45, r46, $r47);	specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genFields(java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String)>(r5, $r49, r46);	specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodInit(java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String,java.lang.String)>(r5, $r49, r45, r46);	specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWriteJSONB(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.Class,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String,long)>(r16, r7, r5, $r49, r45, l3);	$r48 = <com.alibaba.fastjson2.JSONWriter$Feature: com.alibaba.fastjson2.JSONWriter$Feature BeanToArray>;	$l14 = $r48.<com.alibaba.fastjson2.JSONWriter$Feature: long mask>;	$l15 = l3 & $l14;	$b16 = $l15 cmp 0L;	if $b16 == 0 goto specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWrite(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.Class,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String,long)>(r16, r7, r5, $r49, r45, l3);	specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWriteArrayMapping(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.String,java.lang.Class,long,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String)>(r16, "write", r7, l3, r5, $r49, r45);	goto [?= specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWriteArrayMappingJSONB(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.Class,long,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String,long)>(r16, r7, l3, r5, $r49, r45, l3)];	specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWriteArrayMappingJSONB(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.Class,long,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String,long)>(r16, r7, l3, r5, $r49, r45, l3);	specialinvoke r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: void genMethodWriteArrayMapping(com.alibaba.fastjson2.writer.ObjectWriterProvider,java.lang.String,java.lang.Class,long,java.util.List,com.alibaba.fastjson2.internal.asm.ClassWriter,java.lang.String)>(r16, "writeArrayMapping", r7, l3, r5, $r49, r45);	$r27 = virtualinvoke $r49.<com.alibaba.fastjson2.internal.asm.ClassWriter: byte[] toByteArray()>();	$r17 = r15.<com.alibaba.fastjson2.writer.ObjectWriterCreatorASM: com.alibaba.fastjson2.util.DynamicClassLoader classLoader>;	$i4 = lengthof $r27;	$r28 = virtualinvoke $r17.<com.alibaba.fastjson2.util.DynamicClassLoader: java.lang.Class defineClassPublic(java.lang.String,byte[],int,int)>(r44, $r27, 0, $i4);	$r35 := @caughtexception;	$r55 = new com.alibaba.fastjson2.JSONException;	$r54 = new java.lang.StringBuilder;	specialinvoke $r54.<java.lang.StringBuilder: void <init>()>();	$r38 = virtualinvoke $r54.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("create objectWriter error, objectType ");	$r39 = virtualinvoke $r38.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r7);	$r40 = virtualinvoke $r39.<java.lang.StringBuilder: java.lang.String toString()>();	specialinvoke $r55.<com.alibaba.fastjson2.JSONException: void <init>(java.lang.String,java.lang.Throwable)>($r40, $r35);	throw $r55
;block_num 10