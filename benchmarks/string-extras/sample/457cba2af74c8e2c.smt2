; origin: https://github.com/iscas-projects/SCB : closure-compiler/smt/method-com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder__parseMapping__-157232359/61676-deviant-1.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var333 0)
(declare-sort var1234 0)
(declare-sort var1549 0)
(declare-sort var0 0)
(declare-sort var1135 0)
(declare-sort var3980 0)
(declare-sort var2032 0)
(declare-sort var2630 0)
(declare-sort var691 0)
(declare-sort var1771 0)
(declare-sort var3653 0)
(declare-sort var2563 0)
(declare-sort var2652 0)
(declare-sort var2720 0)
(declare-sort var2999 0)
(declare-sort var590 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun var1234-init () var1234)
(declare-fun <init>/-1461814690 (var1234) void)
(declare-fun var1549_on/1427090730 (Int) var1549)
(declare-fun omitEmptyStrings/1427909429 (var1549) var1549)
(declare-fun splitToList/739613109 (var1549 String) var0)
(define-fun cast-from-String-to-String ((arg String)) String arg)
(declare-fun var0_size/-959786421 (var0) Int)
(declare-fun var1135_checkState/1095365836 (Bool String var3980) void)
(declare-fun cast-from-var0-to-var3980 (var0) var3980)
(declare-fun var0_get/-1216255739 (var0 Int) var3980)
(declare-fun cast-from-var3980-to-String (var3980) String)
(define-fun is-whitespace ((char String)) Bool (< (str.to_code char) 33))
(define-fun-rec trim-left ((s String)) String (ite (= s "") "" (ite (is-whitespace (str.substr s 0 1)) (trim-left (str.substr s 1 (- (str.len s) 1))) s)))
(define-fun-rec trim-right ((s String)) String (ite (= s "") "" (ite (is-whitespace (str.substr s (- (str.len s) 1) 1)) (trim-right (str.substr s 0 (- (str.len s) 1))) s)))
(define-fun trim/-847153721 ((s String)) String (trim-right (trim-left s)))
(define-fun startsWith/-1785782452 ((s String) (prefix String)) Bool (str.prefixof prefix s))
(declare-fun var1135_checkState/1431124798 (Bool) void)
(define-fun indexOf/-1209756239 ((s String) (subs String)) Int (str.indexof s subs 0))
(define-fun substring/850833817 ((s String) (begin Int)) String (str.substr s begin (- (str.len s) begin)))
(declare-fun var2032-init () var2032)
(declare-fun <init>/1196464854 (var2032) void)
(declare-fun getType/-733762398 (var2630) ClassObject)
(declare-fun cast-from-var2032-to-var2630 (var2032) var2630)
(declare-fun var691-init () var691)
(declare-fun <init>/-1728377939 (var691) void)
(declare-fun disableHtmlEscaping/-1001101450 (var691) var691)
(declare-fun create/-1678241402 (var691) var1771)
(declare-fun fromJson/-750099079 (var1771 String ClassObject) var3980)
(declare-fun cast-from-var3980-to-var0 (var3980) var0)
(declare-fun var2563_stream/-1288525013 (var2563) var3653)
(declare-fun cast-from-var0-to-var2563 (var0) var2563)
(declare-fun var2720_bootstrap$/-188630264 () var2652)
(declare-fun var3653_map/130902797 (var3653 var2652) var3653)
(declare-fun var590_toList/714215649 () var2999)
(declare-fun var3653_collect/-2050842585 (var3653 var2999) var3980)
(declare-const null-String String)
(declare-const var1265 String) ; Statement: r2 := @parameter0: java.lang.String 
(assert (not (= var1265 null-String)))
(define-const var512 var1234 var1234-init) ; Statement: $r0 = new java.util.LinkedHashMap 
(assert true)
;(assert (<init>/-1461814690 var512)) ; Statement: specialinvoke $r0.<java.util.LinkedHashMap: void <init>()>() 

(declare-const var512!1 var1234)
(define-const var2801 var1549 (var1549_on/1427090730 10)) ; Statement: $r1 = staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter: com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter on(char)>(10) 
(assert true)
(define-const var3303 var1549 (omitEmptyStrings/1427909429 var2801)) ; Statement: $r3 = virtualinvoke $r1.<com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter: com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter omitEmptyStrings()>() 
(assert true)
(define-const var1136 var0 (splitToList/739613109 var3303 (cast-from-String-to-String var1265))) ; Statement: r4 = virtualinvoke $r3.<com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter: java.util.List splitToList(java.lang.CharSequence)>(r2) 
(define-const var3112 Int (var0_size/-959786421 var1136)) ; Statement: $i0 = interfaceinvoke r4.<java.util.List: int size()>() 
 ; Statement: if $i0 < 3 goto $z3 = 0 
(assert (not (< var3112 3))) ; Negate: Cond: $i0 < 3  
(define-const var775 Bool (ite (= 1 1) true false)) ; Statement: $z3 = 1 
 ; Statement: goto [?= staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions: void checkState(boolean,java.lang.String,java.lang.Object)>($z3, "Malformed report %s", r4)] 
(assert true) ; Non Conditional
;(assert (var1135_checkState/1095365836 var775 "Malformed report %s" (cast-from-var0-to-var3980 var1136))) ; Statement: staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions: void checkState(boolean,java.lang.String,java.lang.Object)>($z3, "Malformed report %s", r4) 

(declare-const var775!1 Bool)
(declare-const var736 String)
(declare-const var1136!1 var0)
(define-const var3531 var3980 (var0_get/-1216255739 var1136!1 0)) ; Statement: $r5 = interfaceinvoke r4.<java.util.List: java.lang.Object get(int)>(0) 
(define-const var572 String (cast-from-var3980-to-String var3531)) ; Statement: $r6 = (java.lang.String) $r5 
(assert true)
(define-const var3599 String (trim/-847153721 var572)) ; Statement: $r40 = virtualinvoke $r6.<java.lang.String: java.lang.String trim()>() 
(define-const var1414 var3980 (var0_get/-1216255739 var1136!1 1)) ; Statement: $r7 = interfaceinvoke r4.<java.util.List: java.lang.Object get(int)>(1) 
(define-const var2260 String (cast-from-var3980-to-String var1414)) ; Statement: $r8 = (java.lang.String) $r7 
(assert true)
(define-const var2896 String (trim/-847153721 var2260)) ; Statement: $r41 = virtualinvoke $r8.<java.lang.String: java.lang.String trim()>() 
(define-const var2992 var3980 (var0_get/-1216255739 var1136!1 2)) ; Statement: $r9 = interfaceinvoke r4.<java.util.List: java.lang.Object get(int)>(2) 
(define-const var995 String (cast-from-var3980-to-String var2992)) ; Statement: $r10 = (java.lang.String) $r9 
(assert true)
(define-const var3889 String (trim/-847153721 var995)) ; Statement: $r42 = virtualinvoke $r10.<java.lang.String: java.lang.String trim()>() 
(assert true)
(define-const var1312 Bool (startsWith/-1785782452 var3599 "FileNames:")) ; Statement: $z0 = virtualinvoke $r40.<java.lang.String: boolean startsWith(java.lang.String)>("FileNames:") 
;(assert (var1135_checkState/1431124798 var1312)) ; Statement: staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions: void checkState(boolean)>($z0) 

(declare-const var1312!1 Bool)
(assert true)
(define-const var2065 Bool (startsWith/-1785782452 var2896 "FunctionNames:")) ; Statement: $z1 = virtualinvoke $r41.<java.lang.String: boolean startsWith(java.lang.String)>("FunctionNames:") 
;(assert (var1135_checkState/1431124798 var2065)) ; Statement: staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions: void checkState(boolean)>($z1) 

(declare-const var2065!1 Bool)
(assert true)
(define-const var309 Bool (startsWith/-1785782452 var3889 "Types:")) ; Statement: $z2 = virtualinvoke $r42.<java.lang.String: boolean startsWith(java.lang.String)>("Types:") 
;(assert (var1135_checkState/1431124798 var309)) ; Statement: staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions: void checkState(boolean)>($z2) 

(declare-const var309!1 Bool)
(assert true)
(define-const var2546 Int (indexOf/-1209756239 var3599 ":")) ; Statement: $i1 = virtualinvoke $r40.<java.lang.String: int indexOf(java.lang.String)>(":") 
(define-const var2026 Int (+ var2546 1)) ; Statement: $i2 = $i1 + 1 
(assert (and true (and (>= var2026 0) (>= (str.len var3599) var2026))))
(define-const var2161 String (substring/850833817 var3599 var2026)) ; Statement: $r43 = virtualinvoke $r40.<java.lang.String: java.lang.String substring(int)>($i2) 
(assert true)
(define-const var2122 Int (indexOf/-1209756239 var2896 ":")) ; Statement: $i3 = virtualinvoke $r41.<java.lang.String: int indexOf(java.lang.String)>(":") 
(define-const var2716 Int (+ var2122 1)) ; Statement: $i4 = $i3 + 1 
(assert (not (and true (and (>= var2716 0) (>= (str.len var2896) var2716)))))
(check-sat)


; {var1234-init=([], java.util.LinkedHashMap), <init>/-1461814690=([java.util.LinkedHashMap], void), var1549_on/1427090730=([char], com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter), omitEmptyStrings/1427909429=([com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter], com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter), splitToList/739613109=([com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter, java.lang.CharSequence], java.util.List), cast-from-String-to-String=([java.lang.String], java.lang.CharSequence), var0_size/-959786421=([java.util.List], int), var1135_checkState/1095365836=([boolean, java.lang.String, java.lang.Object], void), cast-from-var0-to-var3980=([java.util.List], java.lang.Object), var0_get/-1216255739=([java.util.List, int], java.lang.Object), cast-from-var3980-to-String=([java.lang.Object], java.lang.String), trim/-847153721=([java.lang.String], java.lang.String), startsWith/-1785782452=([java.lang.String, java.lang.String], boolean), var1135_checkState/1431124798=([boolean], void), indexOf/-1209756239=([java.lang.String, java.lang.String], int), substring/850833817=([java.lang.String, int], java.lang.String), var2032-init=([], com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder$1), <init>/1196464854=([com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder$1], void), getType/-733762398=([com.google.javascript.jscomp.jarjar.com.google.gson.reflect.TypeToken], java.lang.reflect.Type), cast-from-var2032-to-var2630=([com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder$1], com.google.javascript.jscomp.jarjar.com.google.gson.reflect.TypeToken), var691-init=([], com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder), <init>/-1728377939=([com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder], void), disableHtmlEscaping/-1001101450=([com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder], com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder), create/-1678241402=([com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder], com.google.javascript.jscomp.jarjar.com.google.gson.Gson), fromJson/-750099079=([com.google.javascript.jscomp.jarjar.com.google.gson.Gson, java.lang.String, java.lang.reflect.Type], java.lang.Object), cast-from-var3980-to-var0=([java.lang.Object], java.util.List), var2563_stream/-1288525013=([java.util.Collection], java.util.stream.Stream), cast-from-var0-to-var2563=([java.util.List], java.util.Collection), var2720_bootstrap$/-188630264=([], java.util.function.Function), var3653_map/130902797=([java.util.stream.Stream, java.util.function.Function], java.util.stream.Stream), var590_toList/714215649=([], java.util.stream.Collector), var3653_collect/-2050842585=([java.util.stream.Stream, java.util.stream.Collector], java.lang.Object)}
; {var1265=r2, var333=null_type, var1234=java.util.LinkedHashMap, var512=$r0, var1549=com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter, var2801=$r1, var3303=$r3, var0=java.util.List, var1136=r4, var3112=$i0, var775=$z3, var1135=com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions, var3980=java.lang.Object, var736="Malformed report %s", var3531=$r5, var572=$r6, var3599=$r40, var1414=$r7, var2260=$r8, var2896=$r41, var2992=$r9, var995=$r10, var3889=$r42, var1312=$z0, var2065=$z1, var309=$z2, var2546=$i1, var2026=$i2, var2161=$r43, var2122=$i3, var2716=$i4, var475=$r44, var3649=$i5, var2643=$i6, var928=$r45, var2032=com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder$1, var772=$r11, var2630=com.google.javascript.jscomp.jarjar.com.google.gson.reflect.TypeToken, var443=$r46, var691=com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder, var2498=$r12, var558=$r13, var1771=com.google.javascript.jscomp.jarjar.com.google.gson.Gson, var2077=$r47, var1661=$r14, var3782=$r48, var1506=$r15, var2121=$r49, var2012=$r16, var2485=$r50, var3653=java.util.stream.Stream, var2563=java.util.Collection, var1558=$r18, var2652=java.util.function.Function, var2720=com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder$valueOf__1011, var1067=$r17, var2916=$r20, var2999=java.util.stream.Collector, var590=java.util.stream.Collectors, var3246=$r19, var829=$r21, var3539=$r51, var3593=i15, var84=$i16}
; {r2=var1265, null_type=var333, java.util.LinkedHashMap=var1234, $r0=var512, com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter=var1549, $r1=var2801, $r3=var3303, java.util.List=var0, r4=var1136, $i0=var3112, $z3=var775, com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions=var1135, java.lang.Object=var3980, "Malformed report %s"=var736, $r5=var3531, $r6=var572, $r40=var3599, $r7=var1414, $r8=var2260, $r41=var2896, $r9=var2992, $r10=var995, $r42=var3889, $z0=var1312, $z1=var2065, $z2=var309, $i1=var2546, $i2=var2026, $r43=var2161, $i3=var2122, $i4=var2716, $r44=var475, $i5=var3649, $i6=var2643, $r45=var928, com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder$1=var2032, $r11=var772, com.google.javascript.jscomp.jarjar.com.google.gson.reflect.TypeToken=var2630, $r46=var443, com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder=var691, $r12=var2498, $r13=var558, com.google.javascript.jscomp.jarjar.com.google.gson.Gson=var1771, $r47=var2077, $r14=var1661, $r48=var3782, $r15=var1506, $r49=var2121, $r16=var2012, $r50=var2485, java.util.stream.Stream=var3653, java.util.Collection=var2563, $r18=var1558, java.util.function.Function=var2652, com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder$valueOf__1011=var2720, $r17=var1067, $r20=var2916, java.util.stream.Collector=var2999, java.util.stream.Collectors=var590, $r19=var3246, $r21=var829, $r51=var3539, i15=var3593, $i16=var84}
;seq <java.lang.String: java.lang.String trim()>;	<java.lang.String: java.lang.String trim()>;	<java.lang.String: java.lang.String trim()>;	<java.lang.String: boolean startsWith(java.lang.String)>;	<java.lang.String: boolean startsWith(java.lang.String)>;	<java.lang.String: boolean startsWith(java.lang.String)>;	<java.lang.String: int indexOf(java.lang.String)>;	<java.lang.String: java.lang.String substring(int)>;	<java.lang.String: int indexOf(java.lang.String)>;	<java.lang.String: java.lang.String substring(int)>;	<java.lang.String: int indexOf(java.lang.String)>;	<java.lang.String: java.lang.String substring(int)>
;cnt {"<java.lang.String: java.lang.String trim()>": 3,"<java.lang.String: boolean startsWith(java.lang.String)>": 3,"<java.lang.String: int indexOf(java.lang.String)>": 3,"<java.lang.String: java.lang.String substring(int)>": 3}
;stmts r2 := @parameter0: java.lang.String;	$r0 = new java.util.LinkedHashMap;	specialinvoke $r0.<java.util.LinkedHashMap: void <init>()>();	$r1 = staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter: com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter on(char)>(10);	$r3 = virtualinvoke $r1.<com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter: com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter omitEmptyStrings()>();	r4 = virtualinvoke $r3.<com.google.javascript.jscomp.jarjar.com.google.common.base.Splitter: java.util.List splitToList(java.lang.CharSequence)>(r2);	$i0 = interfaceinvoke r4.<java.util.List: int size()>();	if $i0 < 3 goto $z3 = 0;	$z3 = 1;	goto [?= staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions: void checkState(boolean,java.lang.String,java.lang.Object)>($z3, "Malformed report %s", r4)];	staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions: void checkState(boolean,java.lang.String,java.lang.Object)>($z3, "Malformed report %s", r4);	$r5 = interfaceinvoke r4.<java.util.List: java.lang.Object get(int)>(0);	$r6 = (java.lang.String) $r5;	$r40 = virtualinvoke $r6.<java.lang.String: java.lang.String trim()>();	$r7 = interfaceinvoke r4.<java.util.List: java.lang.Object get(int)>(1);	$r8 = (java.lang.String) $r7;	$r41 = virtualinvoke $r8.<java.lang.String: java.lang.String trim()>();	$r9 = interfaceinvoke r4.<java.util.List: java.lang.Object get(int)>(2);	$r10 = (java.lang.String) $r9;	$r42 = virtualinvoke $r10.<java.lang.String: java.lang.String trim()>();	$z0 = virtualinvoke $r40.<java.lang.String: boolean startsWith(java.lang.String)>("FileNames:");	staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions: void checkState(boolean)>($z0);	$z1 = virtualinvoke $r41.<java.lang.String: boolean startsWith(java.lang.String)>("FunctionNames:");	staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions: void checkState(boolean)>($z1);	$z2 = virtualinvoke $r42.<java.lang.String: boolean startsWith(java.lang.String)>("Types:");	staticinvoke <com.google.javascript.jscomp.jarjar.com.google.common.base.Preconditions: void checkState(boolean)>($z2);	$i1 = virtualinvoke $r40.<java.lang.String: int indexOf(java.lang.String)>(":");	$i2 = $i1 + 1;	$r43 = virtualinvoke $r40.<java.lang.String: java.lang.String substring(int)>($i2);	$i3 = virtualinvoke $r41.<java.lang.String: int indexOf(java.lang.String)>(":");	$i4 = $i3 + 1;	$r44 = virtualinvoke $r41.<java.lang.String: java.lang.String substring(int)>($i4);	$i5 = virtualinvoke $r42.<java.lang.String: int indexOf(java.lang.String)>(":");	$i6 = $i5 + 1;	$r45 = virtualinvoke $r42.<java.lang.String: java.lang.String substring(int)>($i6);	$r11 = new com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder$1;	specialinvoke $r11.<com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder$1: void <init>()>();	$r46 = virtualinvoke $r11.<com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder$1: java.lang.reflect.Type getType()>();	$r12 = new com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder;	specialinvoke $r12.<com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder: void <init>()>();	$r13 = virtualinvoke $r12.<com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder: com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder disableHtmlEscaping()>();	$r47 = virtualinvoke $r13.<com.google.javascript.jscomp.jarjar.com.google.gson.GsonBuilder: com.google.javascript.jscomp.jarjar.com.google.gson.Gson create()>();	$r14 = virtualinvoke $r47.<com.google.javascript.jscomp.jarjar.com.google.gson.Gson: java.lang.Object fromJson(java.lang.String,java.lang.reflect.Type)>($r43, $r46);	$r48 = (java.util.List) $r14;	$r15 = virtualinvoke $r47.<com.google.javascript.jscomp.jarjar.com.google.gson.Gson: java.lang.Object fromJson(java.lang.String,java.lang.reflect.Type)>($r44, $r46);	$r49 = (java.util.List) $r15;	$r16 = virtualinvoke $r47.<com.google.javascript.jscomp.jarjar.com.google.gson.Gson: java.lang.Object fromJson(java.lang.String,java.lang.reflect.Type)>($r45, $r46);	$r50 = (java.util.List) $r16;	$r18 = interfaceinvoke $r50.<java.util.List: java.util.stream.Stream stream()>();	$r17 = staticinvoke <com.google.javascript.jscomp.instrumentation.reporter.ReportDecoder$valueOf__1011: java.util.function.Function bootstrap$()>();	$r20 = interfaceinvoke $r18.<java.util.stream.Stream: java.util.stream.Stream map(java.util.function.Function)>($r17);	$r19 = staticinvoke <java.util.stream.Collectors: java.util.stream.Collector toList()>();	$r21 = interfaceinvoke $r20.<java.util.stream.Stream: java.lang.Object collect(java.util.stream.Collector)>($r19);	$r51 = (java.util.List) $r21;	i15 = 3;	$i16 = interfaceinvoke r4.<java.util.List: int size()>();	if i15 >= $i16 goto return $r0;	return $r0
;block_num 5