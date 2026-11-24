; origin: https://github.com/iscas-projects/SCB : fastjson/smt/method-com.alibaba.fastjson2.JSONReaderUTF16__info__-533695867/6228.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var1945 0)
(declare-sort var2447 0)
(declare-sort var22 0)
(declare-sort var2228 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun offset/1287024874 (var22) Int)
(declare-fun cast-from-var1945-to-var22 (var1945) var22)
(declare-fun end/-403530942 (var1945) Int)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(define-fun append/-1001720160 ((s String) (tail Int)) String (str.++ s (str.from_int tail)))
(declare-fun ch/1287024874 (var22) Int)
(declare-fun append/-1166366385 (String Int) String)
(declare-fun chars/-403530942 (var1945) (Array Int Int))
(declare-fun start/-403530942 (var1945) Int)
(declare-fun length/-403530942 (var1945) Int)
(define-fun cast-from-Int-to-Int ((arg Int)) Int arg)
(declare-fun var2228_min/-1112089438 (Int Int) Int)
(declare-fun append/-1748486345 (String (Array Int Int) Int Int) String)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-const null-var1945 var1945)
(declare-const null-String String)
(declare-const var3684 var1945) ; Statement: r0 := @this: com.alibaba.fastjson2.JSONReaderUTF16 
(assert (not (= var3684 null-var1945)))
(declare-const var695 String) ; Statement: r2 := @parameter0: java.lang.String 
(assert (not (= var695 null-String)))
(define-const var351 Int 1) ; Statement: i6 = 1 
(define-const var336 Int 0) ; Statement: i7 = 0 
(define-const var2137 Int 0) ; Statement: i8 = 0 
(assert true) ; Non Conditional
(define-const var3389 Int (offset/1287024874 (cast-from-var1945-to-var22 var3684))) ; Statement: $i0 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int offset> 
 ; Statement: if i8 >= $i0 goto $z1 = 0 
(assert (not (>= var2137 var3389))) ; Negate: Cond: i8 >= $i0  
(define-const var3075 Bool (ite (= 1 1) true false)) ; Statement: $z1 = 1 
 ; Statement: goto [?= $i1 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int end>] 
(assert true) ; Non Conditional
(define-const var1095 Int (end/-403530942 var3684)) ; Statement: $i1 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int end> 
 ; Statement: if i8 >= $i1 goto $z2 = 0 
(assert (not (>= var2137 var1095))) ; Negate: Cond: i8 >= $i1  
(define-const var3465 Bool (ite (= 1 1) true false)) ; Statement: $z2 = 1 
 ; Statement: goto [?= $z3 = $z1 & $z2] 
(assert true) ; Non Conditional
(define-const var2139 Bool (ite (= 1 (bv2nat (bvand ((_ int2bv 64) (ite var3075 1 0)) ((_ int2bv 64) (ite var3465 1 0))))) true false)) ; Statement: $z3 = $z1 & $z2 
 ; Statement: if $z3 == 0 goto $r17 = new java.lang.StringBuilder 
(assert (= (ite var2139 1 0) 0)) ; Cond: $z3 == 0 
(define-const var2935 String String-init) ; Statement: $r17 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var2935)) ; Statement: specialinvoke $r17.<java.lang.StringBuilder: void <init>()>() 
(declare-const var2935!1 String)
(assert (= var2935!1 ""))
 ; Statement: if r2 == null goto $r8 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("offset ") 
(assert (= var695 null-String)) ; Cond: r2 == null 
(assert true)
(define-const var498 String (append/672562846 var2935!1 "offset ")) ; Statement: $r8 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("offset ") 
(declare-const var2935!2 String)
(assert (= var2935!2 (str.++ var2935!1 "offset ")))
(define-const var2317 Int (offset/1287024874 (cast-from-var1945-to-var22 var3684))) ; Statement: $i9 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int offset> 
(assert true)
(define-const var3590 String (append/-1001720160 var498 var2317)) ; Statement: $r9 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i9) 
(declare-const var498!1 String)
(assert (str.prefixof var498 var498!1))
(assert true)
(define-const var1943 String (append/672562846 var3590 ", character ")) ; Statement: $r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", character ") 
(declare-const var3590!1 String)
(assert (= var3590!1 (str.++ var3590 ", character ")))
(define-const var2536 Int (ch/1287024874 (cast-from-var1945-to-var22 var3684))) ; Statement: $c10 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: char ch> 
(assert true)
(define-const var3127 String (append/-1166366385 var1943 var2536)) ; Statement: $r11 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>($c10) 
(declare-const var1943!1 String)
(assert (str.prefixof var1943 var1943!1))
(assert true)
(define-const var648 String (append/672562846 var3127 ", line ")) ; Statement: $r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", line ") 
(declare-const var3127!1 String)
(assert (= var3127!1 (str.++ var3127 ", line ")))
(assert true)
(define-const var1390 String (append/-1001720160 var648 var351)) ; Statement: $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>(i6) 
(declare-const var648!1 String)
(assert (str.prefixof var648 var648!1))
(assert true)
(define-const var1389 String (append/672562846 var1390 ", column ")) ; Statement: $r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", column ") 
(declare-const var1390!1 String)
(assert (= var1390!1 (str.++ var1390 ", column ")))
(assert true)
(define-const var1619 String (append/-1001720160 var1389 var336)) ; Statement: $r15 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>(i7) 
(declare-const var1389!1 String)
(assert (str.prefixof var1389 var1389!1))
(assert true)
(define-const var438 String (append/672562846 var1619 ", fastjson-version ")) ; Statement: $r16 = virtualinvoke $r15.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", fastjson-version ") 
(declare-const var1619!1 String)
(assert (= var1619!1 (str.++ var1619 ", fastjson-version ")))
(assert true)
(define-const var1609 String (append/672562846 var438 "2.0.48")) ; Statement: $r3 = virtualinvoke $r16.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("2.0.48") 
(declare-const var438!1 String)
(assert (= var438!1 (str.++ var438 "2.0.48")))
 ; Statement: if i6 <= 1 goto $c11 = 32 
(assert (not (<= var351 1))) ; Negate: Cond: i6 <= 1  
(define-const var2739 Int 10) ; Statement: $c11 = 10 
 ; Statement: goto [?= virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>($c11)] 
(assert true) ; Non Conditional
(assert true)
;(assert (append/-1166366385 var1609 var2739)) ; Statement: virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>($c11) 
(declare-const var1609!1 String)
(assert (str.prefixof var1609 var1609!1))
(define-const var1888 (Array Int Int) (chars/-403530942 var3684)) ; Statement: $r4 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: char[] chars> 
(define-const var1862 Int (start/-403530942 var3684)) ; Statement: $i3 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int start> 
(define-const var1572 Int (length/-403530942 var3684)) ; Statement: $i2 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int length> 
(define-const var2264 Int (cast-from-Int-to-Int 65535)) ; Statement: $i14 = (int) 65535 
(define-const var2853 Int (var2228_min/-1112089438 var1572 var2264)) ; Statement: $i4 = staticinvoke <java.lang.Math: int min(int,int)>($i2, $i14) 
(assert true)
;(assert (append/-1748486345 var2935!2 var1888 var1862 var2853)) ; Statement: virtualinvoke $r17.<java.lang.StringBuilder: java.lang.StringBuilder append(char[],int,int)>($r4, $i3, $i4) 
(declare-const var2935!3 String)
(assert (str.prefixof var2935!2 var2935!3))
(assert true)
(define-const var3154 String (toString/-2075883882 var2935!3)) ; Statement: $r5 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.String toString()>() 
 ; Statement: return $r5 
(check-sat)


; {offset/1287024874=([com.alibaba.fastjson2.JSONReader], int), cast-from-var1945-to-var22=([com.alibaba.fastjson2.JSONReaderUTF16], com.alibaba.fastjson2.JSONReader), end/-403530942=([com.alibaba.fastjson2.JSONReaderUTF16], int), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), append/-1001720160=([java.lang.StringBuilder, int], java.lang.StringBuilder), ch/1287024874=([com.alibaba.fastjson2.JSONReader], char), append/-1166366385=([java.lang.StringBuilder, char], java.lang.StringBuilder), chars/-403530942=([com.alibaba.fastjson2.JSONReaderUTF16], char[]), start/-403530942=([com.alibaba.fastjson2.JSONReaderUTF16], int), length/-403530942=([com.alibaba.fastjson2.JSONReaderUTF16], int), cast-from-Int-to-Int=([int], int), var2228_min/-1112089438=([int, int], int), append/-1748486345=([java.lang.StringBuilder, char[], int, int], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String)}
; {var1945=com.alibaba.fastjson2.JSONReaderUTF16, var3684=r0, var695=r2, var2447=null_type, var351=i6, var336=i7, var2137=i8, var22=com.alibaba.fastjson2.JSONReader, var3389=$i0, var3075=$z1, var1095=$i1, var3465=$z2, var2139=$z3, var2935=$r17, var498=$r8, var2317=$i9, var3590=$r9, var1943=$r10, var2536=$c10, var3127=$r11, var648=$r12, var1390=$r13, var1389=$r14, var1619=$r15, var438=$r16, var1609=$r3, var2739=$c11, var1888=$r4, var1862=$i3, var1572=$i2, var2264=$i14, var2228=java.lang.Math, var2853=$i4, var3154=$r5}
; {com.alibaba.fastjson2.JSONReaderUTF16=var1945, r0=var3684, r2=var695, null_type=var2447, i6=var351, i7=var336, i8=var2137, com.alibaba.fastjson2.JSONReader=var22, $i0=var3389, $z1=var3075, $i1=var1095, $z2=var3465, $z3=var2139, $r17=var2935, $r8=var498, $i9=var2317, $r9=var3590, $r10=var1943, $c10=var2536, $r11=var3127, $r12=var648, $r13=var1390, $r14=var1389, $r15=var1619, $r16=var438, $r3=var1609, $c11=var2739, $r4=var1888, $i3=var1862, $i2=var1572, $i14=var2264, java.lang.Math=var2228, $i4=var2853, $r5=var3154}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(int)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(char)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(int)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(int)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(char)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(char[],int,int)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 6,"<java.lang.StringBuilder: java.lang.StringBuilder append(int)>": 3,"<java.lang.StringBuilder: java.lang.StringBuilder append(char)>": 2,"<java.lang.StringBuilder: java.lang.StringBuilder append(char[],int,int)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r0 := @this: com.alibaba.fastjson2.JSONReaderUTF16;	r2 := @parameter0: java.lang.String;	i6 = 1;	i7 = 0;	i8 = 0;	$i0 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int offset>;	if i8 >= $i0 goto $z1 = 0;	$z1 = 1;	goto [?= $i1 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int end>];	$i1 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int end>;	if i8 >= $i1 goto $z2 = 0;	$z2 = 1;	goto [?= $z3 = $z1 & $z2];	$z3 = $z1 & $z2;	if $z3 == 0 goto $r17 = new java.lang.StringBuilder;	$r17 = new java.lang.StringBuilder;	specialinvoke $r17.<java.lang.StringBuilder: void <init>()>();	if r2 == null goto $r8 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("offset ");	$r8 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("offset ");	$i9 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int offset>;	$r9 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i9);	$r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", character ");	$c10 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: char ch>;	$r11 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>($c10);	$r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", line ");	$r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>(i6);	$r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", column ");	$r15 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>(i7);	$r16 = virtualinvoke $r15.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", fastjson-version ");	$r3 = virtualinvoke $r16.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("2.0.48");	if i6 <= 1 goto $c11 = 32;	$c11 = 10;	goto [?= virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>($c11)];	virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>($c11);	$r4 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: char[] chars>;	$i3 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int start>;	$i2 = r0.<com.alibaba.fastjson2.JSONReaderUTF16: int length>;	$i14 = (int) 65535;	$i4 = staticinvoke <java.lang.Math: int min(int,int)>($i2, $i14);	virtualinvoke $r17.<java.lang.StringBuilder: java.lang.StringBuilder append(char[],int,int)>($r4, $i3, $i4);	$r5 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.String toString()>();	return $r5
;block_num 10