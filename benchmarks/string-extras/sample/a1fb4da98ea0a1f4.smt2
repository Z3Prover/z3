; origin: https://github.com/iscas-projects/SCB : hutool/smt/method-cn.hutool.core.convert.NumberWordFormatter__format__1717433125/1853-deviant-1.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var1123 0)
(declare-sort var1643 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(define-fun indexOf/-1209756239 ((s String) (subs String)) Int (str.indexof s subs 0))
(define-fun cast-from-Int-to-Int ((arg Int)) Int arg)
(define-fun substring/-1240304868 ((s String) (begin Int) (end Int)) String (str.substr s begin (- end begin)))
(define-fun substring/850833817 ((s String) (begin Int)) String (str.substr s begin (- (str.len s) begin)))
(declare-fun var1643_reverse/-339691519 (String) String)
(declare-fun arr-String-init () (Array Int String))
(define-fun length/-134980193 ((s String)) Int (str.len s))
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun toString/-2075883882 ((s String)) String s)
(define-fun is-whitespace ((char String)) Bool (< (str.to_code char) 33))
(define-fun-rec trim-left ((s String)) String (ite (= s "") "" (ite (is-whitespace (str.substr s 0 1)) (trim-left (str.substr s 1 (- (str.len s) 1))) s)))
(define-fun-rec trim-right ((s String)) String (ite (= s "") "" (ite (is-whitespace (str.substr s (- (str.len s) 1) 1)) (trim-right (str.substr s 0 (- (str.len s) 1))) s)))
(define-fun trim/-847153721 ((s String)) String (trim-right (trim-left s)))
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-const null-String String)
(declare-const var3099 String) ; Statement: r0 := @parameter0: java.lang.String 
(assert (not (= var3099 null-String)))
(assert true)
(define-const var1879 Int (indexOf/-1209756239 var3099 ".")) ; Statement: i0 = virtualinvoke r0.<java.lang.String: int indexOf(java.lang.String)>(".") 
(define-const var1911 String "") ; Statement: r40 = "" 
(define-const var732 Int (cast-from-Int-to-Int (- 1))) ; Statement: $i11 = (int) -1 
 ; Statement: if i0 <= $i11 goto r41 = r0 
(assert (not (<= var1879 var732))) ; Negate: Cond: i0 <= $i11  
(assert (and true (and (>= 0 0) (>= (str.len var3099) var1879) (>= var1879 0))))
(define-const var2888 String (substring/-1240304868 var3099 0 var1879)) ; Statement: r41 = virtualinvoke r0.<java.lang.String: java.lang.String substring(int,int)>(0, i0) 
(define-const var774 Int (+ var1879 1)) ; Statement: $i6 = i0 + 1 
(assert (not (and true (and (>= var774 0) (>= (str.len var3099) var774)))))
(check-sat)


; {indexOf/-1209756239=([java.lang.String, java.lang.String], int), cast-from-Int-to-Int=([int], int), substring/-1240304868=([java.lang.String, int, int], java.lang.String), substring/850833817=([java.lang.String, int], java.lang.String), var1643_reverse/-339691519=([java.lang.String], java.lang.String), arr-String-init=([], java.lang.String[]), length/-134980193=([java.lang.String], int), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), trim/-847153721=([java.lang.String], java.lang.String), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder)}
; {var3099=r0, var1123=null_type, var1879=i0, var1911=r40, var732=$i11, var2888=r41, var774=$i6, var1643=cn.hutool.core.util.StrUtil, var129=$r38, var2758=r42, var3852=$r39, var690=$i1, var1040=$i2, var1748=$r48, var2429=r44, var1993=i7, var3553=$i8, var1735=$i9, var57=r45, var996=$i13, var3572=$r52, var2634=$r5, var3830=$r6, var550=$r7, var112=$r8, var3489=$r9, var2063=$r10, var3248=$r11}
; {r0=var3099, null_type=var1123, i0=var1879, r40=var1911, $i11=var732, r41=var2888, $i6=var774, cn.hutool.core.util.StrUtil=var1643, $r38=var129, r42=var2758, $r39=var3852, $i1=var690, $i2=var1040, $r48=var1748, r44=var2429, i7=var1993, $i8=var3553, $i9=var1735, r45=var57, $i13=var996, $r52=var3572, $r5=var2634, $r6=var3830, $r7=var550, $r8=var112, $r9=var3489, $r10=var2063, $r11=var3248}
;seq <java.lang.String: int indexOf(java.lang.String)>;	<java.lang.String: java.lang.String substring(int,int)>;	<java.lang.String: java.lang.String substring(int)>;	<java.lang.String: int length()>;	<java.lang.StringBuilder: void <init>()>;	<java.lang.String: int length()>;	<java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.String toString()>;	<java.lang.String: java.lang.String trim()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.String: int indexOf(java.lang.String)>": 1,"<java.lang.String: java.lang.String substring(int,int)>": 1,"<java.lang.String: java.lang.String substring(int)>": 1,"<java.lang.String: int length()>": 2,"<java.lang.StringBuilder: void <init>()>": 2,"<java.lang.StringBuilder: java.lang.String toString()>": 2,"<java.lang.String: java.lang.String trim()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 4}
;stmts r0 := @parameter0: java.lang.String;	i0 = virtualinvoke r0.<java.lang.String: int indexOf(java.lang.String)>(".");	r40 = "";	$i11 = (int) -1;	if i0 <= $i11 goto r41 = r0;	r41 = virtualinvoke r0.<java.lang.String: java.lang.String substring(int,int)>(0, i0);	$i6 = i0 + 1;	r40 = virtualinvoke r0.<java.lang.String: java.lang.String substring(int)>($i6);	goto [?= $r38 = staticinvoke <cn.hutool.core.util.StrUtil: java.lang.String reverse(java.lang.String)>(r41)];	$r38 = staticinvoke <cn.hutool.core.util.StrUtil: java.lang.String reverse(java.lang.String)>(r41);	r42 = $r38;	$r39 = newarray (java.lang.String)[5];	$i1 = virtualinvoke $r38.<java.lang.String: int length()>();	$i2 = $i1 % 3;	lookupswitch($i2) {     case 1: goto $r46 = new java.lang.StringBuilder;     case 2: goto $r47 = new java.lang.StringBuilder;     default: goto $r48 = new java.lang.StringBuilder; };	$r48 = new java.lang.StringBuilder;	specialinvoke $r48.<java.lang.StringBuilder: void <init>()>();	r44 = $r48;	i7 = 0;	$i8 = virtualinvoke r42.<java.lang.String: int length()>();	$i9 = $i8 / 3;	if i7 >= $i9 goto r45 = "";	r45 = "";	$i13 = (int) -1;	if i0 <= $i13 goto $r52 = new java.lang.StringBuilder;	$r52 = new java.lang.StringBuilder;	specialinvoke $r52.<java.lang.StringBuilder: void <init>()>();	$r5 = virtualinvoke r44.<java.lang.StringBuilder: java.lang.String toString()>();	$r6 = virtualinvoke $r5.<java.lang.String: java.lang.String trim()>();	$r7 = virtualinvoke $r52.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r6);	$r8 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(" ");	$r9 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r45);	$r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("ONLY");	$r11 = virtualinvoke $r10.<java.lang.StringBuilder: java.lang.String toString()>();	return $r11
;block_num 7