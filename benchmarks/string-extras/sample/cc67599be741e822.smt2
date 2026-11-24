; origin: https://github.com/iscas-projects/SCB : javacc/smt/method-org.javacc.parser.Options__setCmdLineOption__-430146320/1333-deviant-1.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var276 0)
(declare-sort var3674 0)
(declare-sort var3394 0)
(declare-sort var1541 0)
(declare-sort var1554 0)
(declare-sort var512 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(define-fun charAt/698050440 ((s String) (index Int)) Int (str.to_code (str.at s index)))
(define-fun cast-from-Int-to-Int ((arg Int)) Int arg)
(define-fun substring/850833817 ((s String) (begin Int)) String (str.substr s begin (- (str.len s) begin)))
(define-fun indexOf/-1037706067 ((s String) (c Int)) Int (str.indexof s (str.from_code c) 0))
(define-fun toUpperCase/1156088314 ((s String)) String (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all s "a" "A") "b" "B") "c" "C") "d" "D") "e" "E") "f" "F") "g" "G") "h" "H") "i" "I") "j" "J") "k" "K") "l" "L") "m" "M") "n" "N") "o" "O") "p" "P") "q" "Q") "r" "R") "s" "S") "t" "T") "u" "U") "v" "V") "w" "W") "x" "X") "y" "Y") "z" "Z"))
(declare-fun var3674_containsKey/1715618542 (var3674 var1541) Bool)
(declare-fun cast-from-String-to-var1541 (String) var1541)
(define-fun length/-134980193 ((s String)) Int (str.len s))
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun println/1773605060 (var1554 String) void)
(declare-const null-String String)
(declare-const var3394-optionValues var3674)
(declare-const var512-out var1554)
(declare-const var889 String) ; Statement: r0 := @parameter0: java.lang.String 
(assert (not (= var889 null-String)))
(assert (and true (and (> (str.len var889) 0) (<= 0 0))))
(define-const var846 Int (charAt/698050440 var889 0)) ; Statement: $c0 = virtualinvoke r0.<java.lang.String: char charAt(int)>(0) 
(define-const var2258 Int (cast-from-Int-to-Int var846)) ; Statement: $i22 = (int) $c0 
 ; Statement: if $i22 != 45 goto r38 = r0 
(assert (not (not (= var2258 45)))) ; Negate: Cond: $i22 != 45  
(assert (not (and true (and (>= 1 0) (>= (str.len var889) 1)))))
(check-sat)


; {charAt/698050440=([java.lang.String, int], char), cast-from-Int-to-Int=([char], int), substring/850833817=([java.lang.String, int], java.lang.String), indexOf/-1037706067=([java.lang.String, int], int), toUpperCase/1156088314=([java.lang.String], java.lang.String), var3674_containsKey/1715618542=([java.util.Map, java.lang.Object], boolean), cast-from-String-to-var1541=([java.lang.String], java.lang.Object), length/-134980193=([java.lang.String], int), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), println/1773605060=([java.io.PrintStream, java.lang.String], void)}
; {var889=r0, var276=null_type, var846=$c0, var2258=$i22, var2113=r38, var2853=$i7, var2322=$i8, var790=i20, var3748=r39, var3674=java.util.Map, var3394=org.javacc.parser.Options, var3311=$r36, var1541=java.lang.Object, var794=$z4, var913=$i4, var1554=java.io.PrintStream, var512=java.lang.System, var2299=$r41, var490=$r50, var842=$r43, var1531=$r44, var1473=$r45, var589=$r46}
; {r0=var889, null_type=var276, $c0=var846, $i22=var2258, r38=var2113, $i7=var2853, $i8=var2322, i20=var790, r39=var3748, java.util.Map=var3674, org.javacc.parser.Options=var3394, $r36=var3311, java.lang.Object=var1541, $z4=var794, $i4=var913, java.io.PrintStream=var1554, java.lang.System=var512, $r41=var2299, $r50=var490, $r43=var842, $r44=var1531, $r45=var1473, $r46=var589}
;seq <java.lang.String: char charAt(int)>;	<java.lang.String: java.lang.String substring(int)>;	<java.lang.String: int indexOf(int)>;	<java.lang.String: int indexOf(int)>;	<java.lang.String: java.lang.String toUpperCase()>;	<java.lang.String: int length()>;	<java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.String: char charAt(int)>": 1,"<java.lang.String: java.lang.String substring(int)>": 1,"<java.lang.String: int indexOf(int)>": 2,"<java.lang.String: java.lang.String toUpperCase()>": 1,"<java.lang.String: int length()>": 1,"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 3,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r0 := @parameter0: java.lang.String;	$c0 = virtualinvoke r0.<java.lang.String: char charAt(int)>(0);	$i22 = (int) $c0;	if $i22 != 45 goto r38 = r0;	r38 = virtualinvoke r0.<java.lang.String: java.lang.String substring(int)>(1);	goto [?= $i7 = virtualinvoke r38.<java.lang.String: int indexOf(int)>(61)];	$i7 = virtualinvoke r38.<java.lang.String: int indexOf(int)>(61);	$i8 = virtualinvoke r38.<java.lang.String: int indexOf(int)>(58);	if $i7 >= 0 goto (branch);	i20 = $i8;	goto [?= (branch)];	if i20 >= 0 goto $r1 = virtualinvoke r38.<java.lang.String: java.lang.String substring(int,int)>(0, i20);	r39 = virtualinvoke r38.<java.lang.String: java.lang.String toUpperCase()>();	$r36 = <org.javacc.parser.Options: java.util.Map optionValues>;	$z4 = interfaceinvoke $r36.<java.util.Map: boolean containsKey(java.lang.Object)>(r39);	if $z4 == 0 goto $i4 = virtualinvoke r39.<java.lang.String: int length()>();	$i4 = virtualinvoke r39.<java.lang.String: int length()>();	if $i4 <= 2 goto $r41 = <java.lang.System: java.io.PrintStream out>;	$r41 = <java.lang.System: java.io.PrintStream out>;	$r50 = new java.lang.StringBuilder;	specialinvoke $r50.<java.lang.StringBuilder: void <init>()>();	$r43 = virtualinvoke $r50.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Warning: Bad option \"");	$r44 = virtualinvoke $r43.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r0);	$r45 = virtualinvoke $r44.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("\" will be ignored.");	$r46 = virtualinvoke $r45.<java.lang.StringBuilder: java.lang.String toString()>();	virtualinvoke $r41.<java.io.PrintStream: void println(java.lang.String)>($r46);	return
;block_num 8