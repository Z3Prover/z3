; origin: https://github.com/iscas-projects/SCB : mybatis/smt/method-org.apache.ibatis.javassist.bytecode.Descriptor__appendParameter__-1627837033/6327-deviant-1.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3490 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(define-fun indexOf/-1037706067 ((s String) (c Int)) Int (str.indexof s (str.from_code c) 0))
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun substring/-1240304868 ((s String) (begin Int) (end Int)) String (str.substr s begin (- end begin)))
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun append/-1166366385 (String Int) String)
(define-fun replace/1524665721 ((s String) (old_char Int) (new_char Int)) String (str.replace_all s (str.from_code old_char) (str.from_code new_char)))
(define-fun substring/850833817 ((s String) (begin Int)) String (str.substr s begin (- (str.len s) begin)))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-const null-String String)
(declare-const var3245 String) ; Statement: r3 := @parameter0: java.lang.String 
(assert (not (= var3245 null-String)))
(declare-const var1414 String) ; Statement: r0 := @parameter1: java.lang.String 
(assert (not (= var1414 null-String)))
(assert true)
(define-const var2427 Int (indexOf/-1037706067 var1414 41)) ; Statement: i0 = virtualinvoke r0.<java.lang.String: int indexOf(int)>(41) 
 ; Statement: if i0 >= 0 goto $r1 = new java.lang.StringBuilder 
(assert (>= var2427 0)) ; Cond: i0 >= 0 
(define-const var770 String String-init) ; Statement: $r1 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var770)) ; Statement: specialinvoke $r1.<java.lang.StringBuilder: void <init>()>() 
(declare-const var770!1 String)
(assert (= var770!1 ""))
(assert (and true (and (>= 0 0) (>= (str.len var1414) var2427) (>= var2427 0))))
(define-const var1278 String (substring/-1240304868 var1414 0 var2427)) ; Statement: $r2 = virtualinvoke r0.<java.lang.String: java.lang.String substring(int,int)>(0, i0) 
(assert true)
;(assert (append/672562846 var770!1 var1278)) ; Statement: virtualinvoke $r1.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r2) 
(declare-const var770!2 String)
(assert (= var770!2 (str.++ var770!1 var1278)))
(assert true)
;(assert (append/-1166366385 var770!2 76)) ; Statement: virtualinvoke $r1.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(76) 
(declare-const var770!3 String)
(assert (str.prefixof var770!2 var770!3))
(assert true)
(define-const var1497 String (replace/1524665721 var3245 46 47)) ; Statement: $r4 = virtualinvoke r3.<java.lang.String: java.lang.String replace(char,char)>(46, 47) 
(assert true)
;(assert (append/672562846 var770!3 var1497)) ; Statement: virtualinvoke $r1.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r4) 
(declare-const var770!4 String)
(assert (= var770!4 (str.++ var770!3 var1497)))
(assert true)
;(assert (append/-1166366385 var770!4 59)) ; Statement: virtualinvoke $r1.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(59) 
(declare-const var770!5 String)
(assert (str.prefixof var770!4 var770!5))
(assert (not (and true (and (>= var2427 0) (>= (str.len var1414) var2427)))))
(check-sat)


; {indexOf/-1037706067=([java.lang.String, int], int), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), substring/-1240304868=([java.lang.String, int, int], java.lang.String), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), append/-1166366385=([java.lang.StringBuilder, char], java.lang.StringBuilder), replace/1524665721=([java.lang.String, char, char], java.lang.String), substring/850833817=([java.lang.String, int], java.lang.String), toString/-2075883882=([java.lang.StringBuilder], java.lang.String)}
; {var3245=r3, var3490=null_type, var1414=r0, var2427=i0, var770=$r1, var1278=$r2, var1497=$r4, var3377=$r5, var1448=$r6}
; {r3=var3245, null_type=var3490, r0=var1414, i0=var2427, $r1=var770, $r2=var1278, $r4=var1497, $r5=var3377, $r6=var1448}
;seq <java.lang.String: int indexOf(int)>;	<java.lang.StringBuilder: void <init>()>;	<java.lang.String: java.lang.String substring(int,int)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(char)>;	<java.lang.String: java.lang.String replace(char,char)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(char)>;	<java.lang.String: java.lang.String substring(int)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.String: int indexOf(int)>": 1,"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.String: java.lang.String substring(int,int)>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 3,"<java.lang.StringBuilder: java.lang.StringBuilder append(char)>": 2,"<java.lang.String: java.lang.String replace(char,char)>": 1,"<java.lang.String: java.lang.String substring(int)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r3 := @parameter0: java.lang.String;	r0 := @parameter1: java.lang.String;	i0 = virtualinvoke r0.<java.lang.String: int indexOf(int)>(41);	if i0 >= 0 goto $r1 = new java.lang.StringBuilder;	$r1 = new java.lang.StringBuilder;	specialinvoke $r1.<java.lang.StringBuilder: void <init>()>();	$r2 = virtualinvoke r0.<java.lang.String: java.lang.String substring(int,int)>(0, i0);	virtualinvoke $r1.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r2);	virtualinvoke $r1.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(76);	$r4 = virtualinvoke r3.<java.lang.String: java.lang.String replace(char,char)>(46, 47);	virtualinvoke $r1.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r4);	virtualinvoke $r1.<java.lang.StringBuilder: java.lang.StringBuilder append(char)>(59);	$r5 = virtualinvoke r0.<java.lang.String: java.lang.String substring(int)>(i0);	virtualinvoke $r1.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r5);	$r6 = virtualinvoke $r1.<java.lang.StringBuilder: java.lang.String toString()>();	return $r6
;block_num 2