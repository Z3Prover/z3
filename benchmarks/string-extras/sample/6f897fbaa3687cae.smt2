; origin: https://github.com/iscas-projects/SCB : fastjson/smt/method-com.alibaba.fastjson2.schema.StringSchema__《init》__-1910538225/3583.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var2538 0)
(declare-sort var1219 0)
(declare-sort var2608 0)
(declare-sort var2134 0)
(declare-sort var203 0)
(declare-sort var3282 0)
(declare-sort var1572 0)
(declare-sort var553 0)
(declare-sort var1506 0)
(declare-sort var280 0)
(declare-sort var2905 0)
(declare-sort var2182 0)
(declare-sort var1770 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-const String!class ClassObject)
(declare-fun <init>/1415540230 (var2608 var1219) void)
(declare-fun cast-from-var2538-to-var2608 (var2538) var2608)
(declare-fun getString/1992452270 (var1219 String) String)
(define-fun equalsIgnoreCase/-92311102 ((this String) (another String)) Bool (let ((upper_this (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all this "a" "A") "b" "B") "c" "C") "d" "D") "e" "E") "f" "F") "g" "G") "h" "H") "i" "I") "j" "J") "k" "K") "l" "L") "m" "M") "n" "N") "o" "O") "p" "P") "q" "Q") "r" "R") "s" "S") "t" "T") "u" "U") "v" "V") "w" "W") "x" "X") "y" "Y") "z" "Z")) (upper_another (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all another "a" "A") "b" "B") "c" "C") "d" "D") "e" "E") "f" "F") "g" "G") "h" "H") "i" "I") "j" "J") "k" "K") "l" "L") "m" "M") "n" "N") "o" "O") "p" "P") "q" "Q") "r" "R") "s" "S") "t" "T") "u" "U") "v" "V") "w" "W") "x" "X") "y" "Y") "z" "Z"))) (= upper_this upper_another)))
(declare-fun typed/1588225568 (var2538) Bool)
(define-fun cast-from-Int-to-Int ((arg Int)) Int arg)
(declare-fun getIntValue/-1814717338 (var1219 String Int) Int)
(declare-fun minLength/1588225568 (var2538) Int)
(declare-fun maxLength/1588225568 (var2538) Int)
(declare-fun patternFormat/1588225568 (var2538) String)
(declare-fun pattern/1588225568 (var2538) var203)
(declare-fun format/1588225568 (var2538) String)
(declare-fun get/-1324468399 (var1219 String) var3282)
(declare-fun cast-from-var3282-to-var1572 (var3282) var1572)
(declare-fun var2608_anyOf/-686272272 (var1572 ClassObject) var553)
(declare-fun anyOf/1588225568 (var2538) var553)
(declare-fun var2608_oneOf/-178658204 (var1572 ClassObject) var1506)
(declare-fun oneOf/1588225568 (var2538) var1506)
(declare-fun constValue/1588225568 (var2538) String)
(declare-fun cast-from-var3282-to-var2905 (var3282) var2905)
(declare-fun var2182-init () var2182)
(declare-fun var2905_size/-390258357 (var2905) Int)
(declare-fun <init>/1974270677 (var2182 Int) void)
(declare-fun cast-from-var2182-to-var280 (var2182) var280)
(declare-fun var280_addAll/-907809033 (var280 var2905) Bool)
(declare-fun enumValues/1588225568 (var2538) var280)
(declare-fun formatValidator/1588225568 (var2538) var1770)
(declare-const null-var2538 var2538)
(declare-const null-var1219 var1219)
(declare-const null-String String)
(declare-const null-var203 var203)
(declare-const null-var280 var280)
(declare-const null-var1770 var1770)
(declare-const var1300 var2538) ; Statement: r0 := @this: com.alibaba.fastjson2.schema.StringSchema 
(assert (not (= var1300 null-var2538)))
(declare-const var139 var1219) ; Statement: r1 := @parameter0: com.alibaba.fastjson2.JSONObject 
(assert (not (= var139 null-var1219)))
(assert true)
;(assert (<init>/1415540230 (cast-from-var2538-to-var2608 var1300) var139)) ; Statement: specialinvoke r0.<com.alibaba.fastjson2.schema.JSONSchema: void <init>(com.alibaba.fastjson2.JSONObject)>(r1) 

(declare-const var1300!1 var2538)
(declare-const var139!1 var1219)
(define-const var2600 String "string") ; Statement: $r3 = "string" 
(assert true)
(define-const var701 String (getString/1992452270 var139!1 "type")) ; Statement: $r2 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.String getString(java.lang.String)>("type") 
(assert true)
(define-const var1974 Bool (equalsIgnoreCase/-92311102 var2600 var701)) ; Statement: $z0 = virtualinvoke $r3.<java.lang.String: boolean equalsIgnoreCase(java.lang.String)>($r2) 
(declare-const var1300!2 var2538)
(assert (not (= var1300!2 null-var2538)))
(assert (= (typed/1588225568 var1300!2) var1974)) ; Statement: r0.<com.alibaba.fastjson2.schema.StringSchema: boolean typed> = $z0 
(define-const var2327 Int (cast-from-Int-to-Int (- 1))) ; Statement: $i6 = (int) -1 
(assert true)
(define-const var1466 Int (getIntValue/-1814717338 var139!1 "minLength" var2327)) ; Statement: $i0 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: int getIntValue(java.lang.String,int)>("minLength", $i6) 
(declare-const var1300!3 var2538)
(assert (not (= var1300!3 null-var2538)))
(assert (= (minLength/1588225568 var1300!3) var1466)) ; Statement: r0.<com.alibaba.fastjson2.schema.StringSchema: int minLength> = $i0 
(define-const var394 Int (cast-from-Int-to-Int (- 1))) ; Statement: $i8 = (int) -1 
(assert true)
(define-const var1882 Int (getIntValue/-1814717338 var139!1 "maxLength" var394)) ; Statement: $i1 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: int getIntValue(java.lang.String,int)>("maxLength", $i8) 
(declare-const var1300!4 var2538)
(assert (not (= var1300!4 null-var2538)))
(assert (= (maxLength/1588225568 var1300!4) var1882)) ; Statement: r0.<com.alibaba.fastjson2.schema.StringSchema: int maxLength> = $i1 
(assert true)
(define-const var3650 String (getString/1992452270 var139!1 "pattern")) ; Statement: $r4 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.String getString(java.lang.String)>("pattern") 
(declare-const var1300!5 var2538)
(assert (not (= var1300!5 null-var2538)))
(assert (= (patternFormat/1588225568 var1300!5) var3650)) ; Statement: r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String patternFormat> = $r4 
(define-const var1948 String (patternFormat/1588225568 var1300!5)) ; Statement: $r5 = r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String patternFormat> 
 ; Statement: if $r5 != null goto $r6 = r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String patternFormat> 
(assert (not (not (= var1948 null-String)))) ; Negate: Cond: $r5 != null  
(define-const var3913 var203 null-var203) ; Statement: $r30 = null 
 ; Statement: goto [?= r0.<com.alibaba.fastjson2.schema.StringSchema: java.util.regex.Pattern pattern> = $r30] 
(assert true) ; Non Conditional
(declare-const var1300!6 var2538)
(assert (not (= var1300!6 null-var2538)))
(assert (= (pattern/1588225568 var1300!6) var3913)) ; Statement: r0.<com.alibaba.fastjson2.schema.StringSchema: java.util.regex.Pattern pattern> = $r30 
(assert true)
(define-const var964 String (getString/1992452270 var139!1 "format")) ; Statement: $r7 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.String getString(java.lang.String)>("format") 
(declare-const var1300!7 var2538)
(assert (not (= var1300!7 null-var2538)))
(assert (= (format/1588225568 var1300!7) var964)) ; Statement: r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String format> = $r7 
(assert true)
(define-const var3329 var3282 (get/-1324468399 var139!1 "anyOf")) ; Statement: $r29 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.Object get(java.lang.String)>("anyOf") 
(define-const var747 Bool false) ; Statement: $z1 = $r29 instanceof com.alibaba.fastjson2.JSONArray 
 ; Statement: if $z1 == 0 goto r0.<com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.AnyOf anyOf> = null 
(assert (not (= (ite var747 1 0) 0))) ; Negate: Cond: $z1 == 0  
(define-const var2139 var1572 (cast-from-var3282-to-var1572 var3329)) ; Statement: $r26 = (com.alibaba.fastjson2.JSONArray) $r29 
(define-const var2610 var553 (var2608_anyOf/-686272272 var2139 String!class)) ; Statement: $r27 = staticinvoke <com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.AnyOf anyOf(com.alibaba.fastjson2.JSONArray,java.lang.Class)>($r26, class "Ljava/lang/String;") 
(declare-const var1300!8 var2538)
(assert (not (= var1300!8 null-var2538)))
(assert (= (anyOf/1588225568 var1300!8) var2610)) ; Statement: r0.<com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.AnyOf anyOf> = $r27 
 ; Statement: goto [?= $r28 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.Object get(java.lang.String)>("oneOf")] 
(assert true) ; Non Conditional
(assert true)
(define-const var3133 var3282 (get/-1324468399 var139!1 "oneOf")) ; Statement: $r28 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.Object get(java.lang.String)>("oneOf") 
(define-const var1468 Bool false) ; Statement: $z2 = $r28 instanceof com.alibaba.fastjson2.JSONArray 
 ; Statement: if $z2 == 0 goto r0.<com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.OneOf oneOf> = null 
(assert (not (= (ite var1468 1 0) 0))) ; Negate: Cond: $z2 == 0  
(define-const var3064 var1572 (cast-from-var3282-to-var1572 var3133)) ; Statement: $r23 = (com.alibaba.fastjson2.JSONArray) $r28 
(define-const var2803 var1506 (var2608_oneOf/-178658204 var3064 String!class)) ; Statement: $r24 = staticinvoke <com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.OneOf oneOf(com.alibaba.fastjson2.JSONArray,java.lang.Class)>($r23, class "Ljava/lang/String;") 
(declare-const var1300!9 var2538)
(assert (not (= var1300!9 null-var2538)))
(assert (= (oneOf/1588225568 var1300!9) var2803)) ; Statement: r0.<com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.OneOf oneOf> = $r24 
 ; Statement: goto [?= $r8 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.String getString(java.lang.String)>("const")] 
(assert true) ; Non Conditional
(assert true)
(define-const var3143 String (getString/1992452270 var139!1 "const")) ; Statement: $r8 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.String getString(java.lang.String)>("const") 
(declare-const var1300!10 var2538)
(assert (not (= var1300!10 null-var2538)))
(assert (= (constValue/1588225568 var1300!10) var3143)) ; Statement: r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String constValue> = $r8 
(define-const var159 var280 null-var280) ; Statement: r31 = null 
(assert true)
(define-const var370 var3282 (get/-1324468399 var139!1 "enum")) ; Statement: $r25 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.Object get(java.lang.String)>("enum") 
(define-const var732 Bool false) ; Statement: $z3 = $r25 instanceof java.util.Collection 
 ; Statement: if $z3 == 0 goto $z4 = $r25 instanceof java.lang.Object[] 
(assert (not (= (ite var732 1 0) 0))) ; Negate: Cond: $z3 == 0  
(define-const var2732 var2905 (cast-from-var3282-to-var2905 var370)) ; Statement: r21 = (java.util.Collection) $r25 
(define-const var1650 var2182 var2182-init) ; Statement: $r34 = new java.util.LinkedHashSet 
(define-const var351 Int (var2905_size/-390258357 var2732)) ; Statement: $i3 = interfaceinvoke r21.<java.util.Collection: int size()>() 
(assert true)
;(assert (<init>/1974270677 var1650 var351)) ; Statement: specialinvoke $r34.<java.util.LinkedHashSet: void <init>(int)>($i3) 

(declare-const var1650!1 var2182)
(declare-const var351!1 Int)
(define-const var159!1 var280 (cast-from-var2182-to-var280 var1650!1)) ; Statement: r31 = $r34 
;(assert (var280_addAll/-907809033 (cast-from-var2182-to-var280 var1650!1) var2732)) ; Statement: interfaceinvoke $r34.<java.util.Set: boolean addAll(java.util.Collection)>(r21) 

(declare-const var1650!2 var2182)
(declare-const var2732!1 var2905)
 ; Statement: goto [?= r0.<com.alibaba.fastjson2.schema.StringSchema: java.util.Set enumValues> = r31] 
(assert true) ; Non Conditional
(declare-const var1300!11 var2538)
(assert (not (= var1300!11 null-var2538)))
(assert (= (enumValues/1588225568 var1300!11) var159!1)) ; Statement: r0.<com.alibaba.fastjson2.schema.StringSchema: java.util.Set enumValues> = r31 
(define-const var108 String (format/1588225568 var1300!11)) ; Statement: $r32 = r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String format> 
 ; Statement: if $r32 != null goto r33 = r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String format> 
(assert (not (not (= var108 null-String)))) ; Negate: Cond: $r32 != null  
(declare-const var1300!12 var2538)
(assert (not (= var1300!12 null-var2538)))
(assert (= (formatValidator/1588225568 var1300!12) null-var1770)) ; Statement: r0.<com.alibaba.fastjson2.schema.StringSchema: java.util.function.Predicate formatValidator> = null 
 ; Statement: goto [?= return] 
(assert true) ; Non Conditional
 ; Statement: return 
(check-sat)


; {<init>/1415540230=([com.alibaba.fastjson2.schema.JSONSchema, com.alibaba.fastjson2.JSONObject], void), cast-from-var2538-to-var2608=([com.alibaba.fastjson2.schema.StringSchema], com.alibaba.fastjson2.schema.JSONSchema), getString/1992452270=([com.alibaba.fastjson2.JSONObject, java.lang.String], java.lang.String), equalsIgnoreCase/-92311102=([java.lang.String, java.lang.String], boolean), typed/1588225568=([com.alibaba.fastjson2.schema.StringSchema], boolean), cast-from-Int-to-Int=([int], int), getIntValue/-1814717338=([com.alibaba.fastjson2.JSONObject, java.lang.String, int], int), minLength/1588225568=([com.alibaba.fastjson2.schema.StringSchema], int), maxLength/1588225568=([com.alibaba.fastjson2.schema.StringSchema], int), patternFormat/1588225568=([com.alibaba.fastjson2.schema.StringSchema], java.lang.String), pattern/1588225568=([com.alibaba.fastjson2.schema.StringSchema], java.util.regex.Pattern), format/1588225568=([com.alibaba.fastjson2.schema.StringSchema], java.lang.String), get/-1324468399=([com.alibaba.fastjson2.JSONObject, java.lang.String], java.lang.Object), cast-from-var3282-to-var1572=([java.lang.Object], com.alibaba.fastjson2.JSONArray), var2608_anyOf/-686272272=([com.alibaba.fastjson2.JSONArray, java.lang.Class], com.alibaba.fastjson2.schema.AnyOf), anyOf/1588225568=([com.alibaba.fastjson2.schema.StringSchema], com.alibaba.fastjson2.schema.AnyOf), var2608_oneOf/-178658204=([com.alibaba.fastjson2.JSONArray, java.lang.Class], com.alibaba.fastjson2.schema.OneOf), oneOf/1588225568=([com.alibaba.fastjson2.schema.StringSchema], com.alibaba.fastjson2.schema.OneOf), constValue/1588225568=([com.alibaba.fastjson2.schema.StringSchema], java.lang.String), cast-from-var3282-to-var2905=([java.lang.Object], java.util.Collection), var2182-init=([], java.util.LinkedHashSet), var2905_size/-390258357=([java.util.Collection], int), <init>/1974270677=([java.util.LinkedHashSet, int], void), cast-from-var2182-to-var280=([java.util.LinkedHashSet], java.util.Set), var280_addAll/-907809033=([java.util.Set, java.util.Collection], boolean), enumValues/1588225568=([com.alibaba.fastjson2.schema.StringSchema], java.util.Set), formatValidator/1588225568=([com.alibaba.fastjson2.schema.StringSchema], java.util.function.Predicate)}
; {var2538=com.alibaba.fastjson2.schema.StringSchema, var1300=r0, var1219=com.alibaba.fastjson2.JSONObject, var139=r1, var2608=com.alibaba.fastjson2.schema.JSONSchema, var2600=$r3, var701=$r2, var1974=$z0, var2327=$i6, var1466=$i0, var394=$i8, var1882=$i1, var3650=$r4, var1948=$r5, var2134=null_type, var203=java.util.regex.Pattern, var3913=$r30, var964=$r7, var3282=java.lang.Object, var3329=$r29, var747=$z1, var1572=com.alibaba.fastjson2.JSONArray, var2139=$r26, var553=com.alibaba.fastjson2.schema.AnyOf, var2610=$r27, var3133=$r28, var1468=$z2, var3064=$r23, var1506=com.alibaba.fastjson2.schema.OneOf, var2803=$r24, var3143=$r8, var280=java.util.Set, var159=r31, var370=$r25, var732=$z3, var2905=java.util.Collection, var2732=r21, var2182=java.util.LinkedHashSet, var1650=$r34, var351=$i3, var108=$r32, var1770=java.util.function.Predicate}
; {com.alibaba.fastjson2.schema.StringSchema=var2538, r0=var1300, com.alibaba.fastjson2.JSONObject=var1219, r1=var139, com.alibaba.fastjson2.schema.JSONSchema=var2608, $r3=var2600, $r2=var701, $z0=var1974, $i6=var2327, $i0=var1466, $i8=var394, $i1=var1882, $r4=var3650, $r5=var1948, null_type=var2134, java.util.regex.Pattern=var203, $r30=var3913, $r7=var964, java.lang.Object=var3282, $r29=var3329, $z1=var747, com.alibaba.fastjson2.JSONArray=var1572, $r26=var2139, com.alibaba.fastjson2.schema.AnyOf=var553, $r27=var2610, $r28=var3133, $z2=var1468, $r23=var3064, com.alibaba.fastjson2.schema.OneOf=var1506, $r24=var2803, $r8=var3143, java.util.Set=var280, r31=var159, $r25=var370, $z3=var732, java.util.Collection=var2905, r21=var2732, java.util.LinkedHashSet=var2182, $r34=var1650, $i3=var351, $r32=var108, java.util.function.Predicate=var1770}
;seq <java.lang.String: boolean equalsIgnoreCase(java.lang.String)>
;cnt {"<java.lang.String: boolean equalsIgnoreCase(java.lang.String)>": 1}
;stmts r0 := @this: com.alibaba.fastjson2.schema.StringSchema;	r1 := @parameter0: com.alibaba.fastjson2.JSONObject;	specialinvoke r0.<com.alibaba.fastjson2.schema.JSONSchema: void <init>(com.alibaba.fastjson2.JSONObject)>(r1);	$r3 = "string";	$r2 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.String getString(java.lang.String)>("type");	$z0 = virtualinvoke $r3.<java.lang.String: boolean equalsIgnoreCase(java.lang.String)>($r2);	r0.<com.alibaba.fastjson2.schema.StringSchema: boolean typed> = $z0;	$i6 = (int) -1;	$i0 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: int getIntValue(java.lang.String,int)>("minLength", $i6);	r0.<com.alibaba.fastjson2.schema.StringSchema: int minLength> = $i0;	$i8 = (int) -1;	$i1 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: int getIntValue(java.lang.String,int)>("maxLength", $i8);	r0.<com.alibaba.fastjson2.schema.StringSchema: int maxLength> = $i1;	$r4 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.String getString(java.lang.String)>("pattern");	r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String patternFormat> = $r4;	$r5 = r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String patternFormat>;	if $r5 != null goto $r6 = r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String patternFormat>;	$r30 = null;	goto [?= r0.<com.alibaba.fastjson2.schema.StringSchema: java.util.regex.Pattern pattern> = $r30];	r0.<com.alibaba.fastjson2.schema.StringSchema: java.util.regex.Pattern pattern> = $r30;	$r7 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.String getString(java.lang.String)>("format");	r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String format> = $r7;	$r29 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.Object get(java.lang.String)>("anyOf");	$z1 = $r29 instanceof com.alibaba.fastjson2.JSONArray;	if $z1 == 0 goto r0.<com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.AnyOf anyOf> = null;	$r26 = (com.alibaba.fastjson2.JSONArray) $r29;	$r27 = staticinvoke <com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.AnyOf anyOf(com.alibaba.fastjson2.JSONArray,java.lang.Class)>($r26, class "Ljava/lang/String;");	r0.<com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.AnyOf anyOf> = $r27;	goto [?= $r28 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.Object get(java.lang.String)>("oneOf")];	$r28 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.Object get(java.lang.String)>("oneOf");	$z2 = $r28 instanceof com.alibaba.fastjson2.JSONArray;	if $z2 == 0 goto r0.<com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.OneOf oneOf> = null;	$r23 = (com.alibaba.fastjson2.JSONArray) $r28;	$r24 = staticinvoke <com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.OneOf oneOf(com.alibaba.fastjson2.JSONArray,java.lang.Class)>($r23, class "Ljava/lang/String;");	r0.<com.alibaba.fastjson2.schema.StringSchema: com.alibaba.fastjson2.schema.OneOf oneOf> = $r24;	goto [?= $r8 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.String getString(java.lang.String)>("const")];	$r8 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.String getString(java.lang.String)>("const");	r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String constValue> = $r8;	r31 = null;	$r25 = virtualinvoke r1.<com.alibaba.fastjson2.JSONObject: java.lang.Object get(java.lang.String)>("enum");	$z3 = $r25 instanceof java.util.Collection;	if $z3 == 0 goto $z4 = $r25 instanceof java.lang.Object[];	r21 = (java.util.Collection) $r25;	$r34 = new java.util.LinkedHashSet;	$i3 = interfaceinvoke r21.<java.util.Collection: int size()>();	specialinvoke $r34.<java.util.LinkedHashSet: void <init>(int)>($i3);	r31 = $r34;	interfaceinvoke $r34.<java.util.Set: boolean addAll(java.util.Collection)>(r21);	goto [?= r0.<com.alibaba.fastjson2.schema.StringSchema: java.util.Set enumValues> = r31];	r0.<com.alibaba.fastjson2.schema.StringSchema: java.util.Set enumValues> = r31;	$r32 = r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String format>;	if $r32 != null goto r33 = r0.<com.alibaba.fastjson2.schema.StringSchema: java.lang.String format>;	r0.<com.alibaba.fastjson2.schema.StringSchema: java.util.function.Predicate formatValidator> = null;	goto [?= return];	return
;block_num 11