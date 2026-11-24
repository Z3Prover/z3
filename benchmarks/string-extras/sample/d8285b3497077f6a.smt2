; origin: https://github.com/iscas-projects/SCB : jdk/smt/method-jdk.internal.org.objectweb.asm.commons.AnalyzerAdapter__pushDesc__-1026238458/1089.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var1899 0)
(declare-sort var226 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(define-fun charAt/698050440 ((s String) (index Int)) Int (str.to_code (str.at s index)))
(define-fun cast-from-Int-to-Int ((arg Int)) Int arg)
(define-fun indexOf/-1037706067 ((s String) (c Int)) Int (str.indexof s (str.from_code c) 0))
(declare-const null-var1899 var1899)
(declare-const null-String String)
(declare-const var541 var1899) ; Statement: r1 := @this: jdk.internal.org.objectweb.asm.commons.AnalyzerAdapter 
(assert (not (= var541 null-var1899)))
(declare-const var3533 String) ; Statement: r0 := @parameter0: java.lang.String 
(assert (not (= var3533 null-String)))
(assert (and true (and (> (str.len var3533) 0) (<= 0 0))))
(define-const var2435 Int (charAt/698050440 var3533 0)) ; Statement: $c0 = virtualinvoke r0.<java.lang.String: char charAt(int)>(0) 
(define-const var1340 Int (cast-from-Int-to-Int var2435)) ; Statement: $i10 = (int) $c0 
 ; Statement: if $i10 != 40 goto $i9 = 0 
(assert (not (not (= var1340 40)))) ; Negate: Cond: $i10 != 40  
(assert true)
(define-const var3360 Int (indexOf/-1037706067 var3533 41)) ; Statement: $i8 = virtualinvoke r0.<java.lang.String: int indexOf(int)>(41) 
(define-const var1500 Int (+ var3360 1)) ; Statement: $i9 = $i8 + 1 
 ; Statement: goto [?= $c1 = virtualinvoke r0.<java.lang.String: char charAt(int)>($i9)] 
(assert true) ; Non Conditional
(assert (and true (and (> (str.len var3533) var1500) (<= 0 var1500))))
(define-const var3166 Int (charAt/698050440 var3533 var1500)) ; Statement: $c1 = virtualinvoke r0.<java.lang.String: char charAt(int)>($i9) 
(define-const var1647 Int (cast-from-Int-to-Int var3166)) ; Statement: $i11 = (int) $c1 
 ; Statement: tableswitch($i11) {     case 66: goto $r8 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer INTEGER>;     case 67: goto $r8 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer INTEGER>;     case 68: goto $r6 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer DOUBLE>;     case 69: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 70: goto $r5 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer FLOAT>;     case 71: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 72: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 73: goto $r8 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer INTEGER>;     case 74: goto $r3 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer LONG>;     case 75: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 76: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 77: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 78: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 79: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 80: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 81: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 82: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 83: goto $r8 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer INTEGER>;     case 84: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 85: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 86: goto return;     case 87: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 88: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 89: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 90: goto $r8 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer INTEGER>;     case 91: goto if $i9 != 0 goto $i2 = virtualinvoke r0.<java.lang.String: int length()>();     default: goto if $i9 != 0 goto $i5 = $i9 + 1; } 
(assert (and (= var1647 86) (and (not (= var1647 85)) (and (not (= var1647 84)) (and (not (= var1647 83)) (and (not (= var1647 82)) (and (not (= var1647 81)) (and (not (= var1647 80)) (and (not (= var1647 79)) (and (not (= var1647 78)) (and (not (= var1647 77)) (and (not (= var1647 76)) (and (not (= var1647 75)) (and (not (= var1647 74)) (and (not (= var1647 73)) (and (not (= var1647 72)) (and (not (= var1647 71)) (and (not (= var1647 70)) (and (not (= var1647 69)) (and (not (= var1647 68)) (and (not (= var1647 67)) (and (not (= var1647 66)) true)))))))))))))))))))))) ; Intersect: Cond: $i11 == 86  and Intersect: Negate: Cond: $i11 == 85   and Intersect: Negate: Cond: $i11 == 84   and Intersect: Negate: Cond: $i11 == 83   and Intersect: Negate: Cond: $i11 == 82   and Intersect: Negate: Cond: $i11 == 81   and Intersect: Negate: Cond: $i11 == 80   and Intersect: Negate: Cond: $i11 == 79   and Intersect: Negate: Cond: $i11 == 78   and Intersect: Negate: Cond: $i11 == 77   and Intersect: Negate: Cond: $i11 == 76   and Intersect: Negate: Cond: $i11 == 75   and Intersect: Negate: Cond: $i11 == 74   and Intersect: Negate: Cond: $i11 == 73   and Intersect: Negate: Cond: $i11 == 72   and Intersect: Negate: Cond: $i11 == 71   and Intersect: Negate: Cond: $i11 == 70   and Intersect: Negate: Cond: $i11 == 69   and Intersect: Negate: Cond: $i11 == 68   and Intersect: Negate: Cond: $i11 == 67   and Intersect: Negate: Cond: $i11 == 66   and Non Conditional                     
 ; Statement: return 
(check-sat)


; {charAt/698050440=([java.lang.String, int], char), cast-from-Int-to-Int=([char], int), indexOf/-1037706067=([java.lang.String, int], int)}
; {var1899=jdk.internal.org.objectweb.asm.commons.AnalyzerAdapter, var541=r1, var3533=r0, var226=null_type, var2435=$c0, var1340=$i10, var3360=$i8, var1500=$i9, var3166=$c1, var1647=$i11}
; {jdk.internal.org.objectweb.asm.commons.AnalyzerAdapter=var1899, r1=var541, r0=var3533, null_type=var226, $c0=var2435, $i10=var1340, $i8=var3360, $i9=var1500, $c1=var3166, $i11=var1647}
;seq <java.lang.String: char charAt(int)>;	<java.lang.String: int indexOf(int)>;	<java.lang.String: char charAt(int)>
;cnt {"<java.lang.String: char charAt(int)>": 2,"<java.lang.String: int indexOf(int)>": 1}
;stmts r1 := @this: jdk.internal.org.objectweb.asm.commons.AnalyzerAdapter;	r0 := @parameter0: java.lang.String;	$c0 = virtualinvoke r0.<java.lang.String: char charAt(int)>(0);	$i10 = (int) $c0;	if $i10 != 40 goto $i9 = 0;	$i8 = virtualinvoke r0.<java.lang.String: int indexOf(int)>(41);	$i9 = $i8 + 1;	goto [?= $c1 = virtualinvoke r0.<java.lang.String: char charAt(int)>($i9)];	$c1 = virtualinvoke r0.<java.lang.String: char charAt(int)>($i9);	$i11 = (int) $c1;	tableswitch($i11) {     case 66: goto $r8 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer INTEGER>;     case 67: goto $r8 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer INTEGER>;     case 68: goto $r6 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer DOUBLE>;     case 69: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 70: goto $r5 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer FLOAT>;     case 71: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 72: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 73: goto $r8 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer INTEGER>;     case 74: goto $r3 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer LONG>;     case 75: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 76: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 77: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 78: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 79: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 80: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 81: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 82: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 83: goto $r8 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer INTEGER>;     case 84: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 85: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 86: goto return;     case 87: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 88: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 89: goto if $i9 != 0 goto $i5 = $i9 + 1;     case 90: goto $r8 = <jdk.internal.org.objectweb.asm.Opcodes: java.lang.Integer INTEGER>;     case 91: goto if $i9 != 0 goto $i2 = virtualinvoke r0.<java.lang.String: int length()>();     default: goto if $i9 != 0 goto $i5 = $i9 + 1; };	return
;block_num 4