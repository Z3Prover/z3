; origin: https://github.com/iscas-projects/SCB : mysql-connector-j/smt/method-com.mysql.cj.conf.HostInfo__getHostPortPair__582926859/550.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var2626 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(declare-fun host/-1521200206 (var2626) String)
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun port/-1521200206 (var2626) Int)
(define-fun append/-1001720160 ((s String) (tail Int)) String (str.++ s (str.from_int tail)))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-const null-var2626 var2626)
(declare-const var501 var2626) ; Statement: r1 := @this: com.mysql.cj.conf.HostInfo 
(assert (not (= var501 null-var2626)))
(define-const var1696 String String-init) ; Statement: $r0 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var1696)) ; Statement: specialinvoke $r0.<java.lang.StringBuilder: void <init>()>() 
(declare-const var1696!1 String)
(assert (= var1696!1 ""))
(define-const var3976 String (host/-1521200206 var501)) ; Statement: $r2 = r1.<com.mysql.cj.conf.HostInfo: java.lang.String host> 
(assert true)
(define-const var80 String (append/672562846 var1696!1 var3976)) ; Statement: $r3 = virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r2) 
(declare-const var1696!2 String)
(assert (= var1696!2 (str.++ var1696!1 var3976)))
(assert true)
(define-const var2044 String (append/672562846 var80 ":")) ; Statement: $r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(":") 
(declare-const var80!1 String)
(assert (= var80!1 (str.++ var80 ":")))
(define-const var1898 Int (port/-1521200206 var501)) ; Statement: $i0 = r1.<com.mysql.cj.conf.HostInfo: int port> 
(assert true)
(define-const var1149 String (append/-1001720160 var2044 var1898)) ; Statement: $r5 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i0) 
(declare-const var2044!1 String)
(assert (str.prefixof var2044 var2044!1))
(assert true)
(define-const var1643 String (toString/-2075883882 var1149)) ; Statement: $r6 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.String toString()>() 
 ; Statement: return $r6 
(check-sat)


; {String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), host/-1521200206=([com.mysql.cj.conf.HostInfo], java.lang.String), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), port/-1521200206=([com.mysql.cj.conf.HostInfo], int), append/-1001720160=([java.lang.StringBuilder, int], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String)}
; {var2626=com.mysql.cj.conf.HostInfo, var501=r1, var1696=$r0, var3976=$r2, var80=$r3, var2044=$r4, var1898=$i0, var1149=$r5, var1643=$r6}
; {com.mysql.cj.conf.HostInfo=var2626, r1=var501, $r0=var1696, $r2=var3976, $r3=var80, $r4=var2044, $i0=var1898, $r5=var1149, $r6=var1643}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(int)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 2,"<java.lang.StringBuilder: java.lang.StringBuilder append(int)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r1 := @this: com.mysql.cj.conf.HostInfo;	$r0 = new java.lang.StringBuilder;	specialinvoke $r0.<java.lang.StringBuilder: void <init>()>();	$r2 = r1.<com.mysql.cj.conf.HostInfo: java.lang.String host>;	$r3 = virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r2);	$r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(":");	$i0 = r1.<com.mysql.cj.conf.HostInfo: int port>;	$r5 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i0);	$r6 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.String toString()>();	return $r6
;block_num 1