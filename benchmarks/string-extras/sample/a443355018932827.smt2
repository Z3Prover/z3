; origin: https://github.com/iscas-projects/SCB : mysql-connector-j/smt/method-com.mysql.cj.protocol.a.NativeProtocol__findMysqlType__-1803892274/6763.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3357 0)
(declare-sort var3156 0)
(declare-sort var3657 0)
(declare-sort var2008 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(define-fun cast-from-Int-to-Int ((arg Int)) Int arg)
(declare-fun length/1489591041 (var3156) Int)
(define-fun equalsIgnoreCase/-92311102 ((this String) (another String)) Bool (let ((upper_this (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all this "a" "A") "b" "B") "c" "C") "d" "D") "e" "E") "f" "F") "g" "G") "h" "H") "i" "I") "j" "J") "k" "K") "l" "L") "m" "M") "n" "N") "o" "O") "p" "P") "q" "Q") "r" "R") "s" "S") "t" "T") "u" "U") "v" "V") "w" "W") "x" "X") "y" "Y") "z" "Z")) (upper_another (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all another "a" "A") "b" "B") "c" "C") "d" "D") "e" "E") "f" "F") "g" "G") "h" "H") "i" "I") "j" "J") "k" "K") "l" "L") "m" "M") "n" "N") "o" "O") "p" "P") "q" "Q") "r" "R") "s" "S") "t" "T") "u" "U") "v" "V") "w" "W") "x" "X") "y" "Y") "z" "Z"))) (= upper_this upper_another)))
(declare-const null-var3357 var3357)
(declare-const null-Int Int)
(declare-const null-var3156 var3156)
(declare-const null-String String)
(declare-const var2008-SET var2008)
(declare-const var1992 var3357) ; Statement: r5 := @parameter0: com.mysql.cj.conf.PropertySet 
(assert (not (= var1992 null-var3357)))
(declare-const var2082 Int) ; Statement: i5 := @parameter1: int 
(assert (not (= var2082 null-Int)))
(declare-const var3267 Int) ; Statement: s0 := @parameter2: short 
(assert (not (= var3267 null-Int)))
(declare-const var3750 Int) ; Statement: l6 := @parameter3: long 
(assert (not (= var3750 null-Int)))
(declare-const var2689 var3156) ; Statement: r1 := @parameter4: com.mysql.cj.util.LazyString 
(assert (not (= var2689 null-var3156)))
(declare-const var1011 var3156) ; Statement: r0 := @parameter5: com.mysql.cj.util.LazyString 
(assert (not (= var1011 null-var3156)))
(declare-const var2986 Int) ; Statement: i13 := @parameter6: int 
(assert (not (= var2986 null-Int)))
(declare-const var1936 String) ; Statement: r2 := @parameter7: java.lang.String 
(assert (not (= var1936 null-String)))
(define-const var1783 Int (bv2nat (bvand ((_ int2bv 64) var3267) ((_ int2bv 64) 32)))) ; Statement: $s1 = s0 & 32 
(define-const var984 Int (cast-from-Int-to-Int var1783)) ; Statement: $i16 = (int) $s1 
 ; Statement: if $i16 <= 0 goto $z17 = 0 
(assert (<= var984 0)) ; Cond: $i16 <= 0 
(define-const var2662 Bool (ite (= 1 0) true false)) ; Statement: $z17 = 0 
(assert true) ; Non Conditional
(define-const var365 Bool var2662) ; Statement: z0 = $z17 
(assert true)
(define-const var1592 Int (length/1489591041 var1011)) ; Statement: $i2 = virtualinvoke r0.<com.mysql.cj.util.LazyString: int length()>() 
 ; Statement: if $i2 != 0 goto $z18 = 0 
(assert (not (= var1592 0))) ; Cond: $i2 != 0 
(define-const var1704 Bool (ite (= 1 0) true false)) ; Statement: $z18 = 0 
(assert true) ; Non Conditional
(define-const var2367 Bool var1704) ; Statement: z1 = $z18 
(define-const var1458 Int (bv2nat (bvand ((_ int2bv 64) var3267) ((_ int2bv 64) 128)))) ; Statement: $s3 = s0 & 128 
(define-const var2445 Int (cast-from-Int-to-Int var1458)) ; Statement: $i17 = (int) $s3 
 ; Statement: if $i17 <= 0 goto $z19 = 0 
(assert (not (<= var2445 0))) ; Negate: Cond: $i17 <= 0  
(define-const var2090 Bool (ite (= 1 1) true false)) ; Statement: $z19 = 1 
 ; Statement: goto [?= z2 = $z19] 
(assert true) ; Non Conditional
(define-const var3202 Bool var2090) ; Statement: z2 = $z19 
(assert true)
(define-const var1948 Int (length/1489591041 var2689)) ; Statement: $i4 = virtualinvoke r1.<com.mysql.cj.util.LazyString: int length()>() 
 ; Statement: if $i4 <= 0 goto $z20 = 0 
(assert (<= var1948 0)) ; Cond: $i4 <= 0 
(define-const var3263 Bool (ite (= 1 0) true false)) ; Statement: $z20 = 0 
(assert true) ; Non Conditional
(define-const var3917 Bool var3263) ; Statement: z3 = $z20 
 ; Statement: if z2 == 0 goto $r82 = "binary" 
(assert (= (ite var3202 1 0) 0)) ; Cond: z2 == 0 
(define-const var1631 String "binary") ; Statement: $r82 = "binary" 
(assert true)
(define-const var701 Bool (equalsIgnoreCase/-92311102 var1631 var1936)) ; Statement: $z21 = virtualinvoke $r82.<java.lang.String: boolean equalsIgnoreCase(java.lang.String)>(r2) 
(assert true) ; Non Conditional
 ; Statement: lookupswitch(i5) {     case 0: goto if z0 == 0 goto $r83 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType DECIMAL>;     case 1: goto if z0 != 0 goto (branch);     case 2: goto if z0 == 0 goto $r85 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType SMALLINT>;     case 3: goto if z0 == 0 goto $r86 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType INT>;     case 4: goto if z0 == 0 goto $r87 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType FLOAT>;     case 5: goto if z0 == 0 goto $r88 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType DOUBLE>;     case 6: goto $r69 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType NULL>;     case 7: goto $r68 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType TIMESTAMP>;     case 8: goto if z0 == 0 goto $r89 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType BIGINT>;     case 9: goto if z0 == 0 goto $r90 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType MEDIUMINT>;     case 10: goto $r67 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType DATE>;     case 11: goto $r66 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType TIME>;     case 12: goto $r65 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType DATETIME>;     case 13: goto $r64 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType YEAR>;     case 15: goto if $z21 == 0 goto $r58 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType VARCHAR>;     case 16: goto $r57 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType BIT>;     case 242: goto $r56 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType VECTOR>;     case 245: goto $r55 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType JSON>;     case 246: goto if z0 == 0 goto $r83 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType DECIMAL>;     case 247: goto $r54 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType ENUM>;     case 248: goto $r53 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType SET>;     case 249: goto if z2 == 0 goto $r91 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType TINYTEXT>;     case 250: goto if z2 == 0 goto $r92 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType MEDIUMTEXT>;     case 251: goto if z2 == 0 goto $r93 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType LONGTEXT>;     case 252: goto $r11 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType TINYBLOB>;     case 253: goto if $z21 == 0 goto $r58 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType VARCHAR>;     case 254: goto if $z21 == 0 goto $r4 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType CHAR>;     case 255: goto $r3 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType GEOMETRY>;     default: goto $r80 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType UNKNOWN>; } 
(assert (and (= var2082 248) (and (not (= var2082 247)) (and (not (= var2082 246)) (and (not (= var2082 245)) (and (not (= var2082 242)) (and (not (= var2082 16)) (and (not (= var2082 15)) (and (not (= var2082 13)) (and (not (= var2082 12)) (and (not (= var2082 11)) (and (not (= var2082 10)) (and (not (= var2082 9)) (and (not (= var2082 8)) (and (not (= var2082 7)) (and (not (= var2082 6)) (and (not (= var2082 5)) (and (not (= var2082 4)) (and (not (= var2082 3)) (and (not (= var2082 2)) (and (not (= var2082 1)) (and (not (= var2082 0)) true)))))))))))))))))))))) ; Intersect: Cond: i5 == 248  and Intersect: Negate: Cond: i5 == 247   and Intersect: Negate: Cond: i5 == 246   and Intersect: Negate: Cond: i5 == 245   and Intersect: Negate: Cond: i5 == 242   and Intersect: Negate: Cond: i5 == 16   and Intersect: Negate: Cond: i5 == 15   and Intersect: Negate: Cond: i5 == 13   and Intersect: Negate: Cond: i5 == 12   and Intersect: Negate: Cond: i5 == 11   and Intersect: Negate: Cond: i5 == 10   and Intersect: Negate: Cond: i5 == 9   and Intersect: Negate: Cond: i5 == 8   and Intersect: Negate: Cond: i5 == 7   and Intersect: Negate: Cond: i5 == 6   and Intersect: Negate: Cond: i5 == 5   and Intersect: Negate: Cond: i5 == 4   and Intersect: Negate: Cond: i5 == 3   and Intersect: Negate: Cond: i5 == 2   and Intersect: Negate: Cond: i5 == 1   and Intersect: Negate: Cond: i5 == 0   and Non Conditional                     
(define-const var3817 var2008 var2008-SET) ; Statement: $r53 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType SET> 
 ; Statement: return $r53 
(check-sat)


; {cast-from-Int-to-Int=([short], int), length/1489591041=([com.mysql.cj.util.LazyString], int), equalsIgnoreCase/-92311102=([java.lang.String, java.lang.String], boolean)}
; {var3357=com.mysql.cj.conf.PropertySet, var1992=r5, var2082=i5, var3267=s0, var3750=l6, var3156=com.mysql.cj.util.LazyString, var2689=r1, var1011=r0, var2986=i13, var1936=r2, var3657=null_type, var1783=$s1, var984=$i16, var2662=$z17, var365=z0, var1592=$i2, var1704=$z18, var2367=z1, var1458=$s3, var2445=$i17, var2090=$z19, var3202=z2, var1948=$i4, var3263=$z20, var3917=z3, var1631=$r82, var701=$z21, var2008=com.mysql.cj.MysqlType, var3817=$r53}
; {com.mysql.cj.conf.PropertySet=var3357, r5=var1992, i5=var2082, s0=var3267, l6=var3750, com.mysql.cj.util.LazyString=var3156, r1=var2689, r0=var1011, i13=var2986, r2=var1936, null_type=var3657, $s1=var1783, $i16=var984, $z17=var2662, z0=var365, $i2=var1592, $z18=var1704, z1=var2367, $s3=var1458, $i17=var2445, $z19=var2090, z2=var3202, $i4=var1948, $z20=var3263, z3=var3917, $r82=var1631, $z21=var701, com.mysql.cj.MysqlType=var2008, $r53=var3817}
;seq <java.lang.String: boolean equalsIgnoreCase(java.lang.String)>
;cnt {"<java.lang.String: boolean equalsIgnoreCase(java.lang.String)>": 1}
;stmts r5 := @parameter0: com.mysql.cj.conf.PropertySet;	i5 := @parameter1: int;	s0 := @parameter2: short;	l6 := @parameter3: long;	r1 := @parameter4: com.mysql.cj.util.LazyString;	r0 := @parameter5: com.mysql.cj.util.LazyString;	i13 := @parameter6: int;	r2 := @parameter7: java.lang.String;	$s1 = s0 & 32;	$i16 = (int) $s1;	if $i16 <= 0 goto $z17 = 0;	$z17 = 0;	z0 = $z17;	$i2 = virtualinvoke r0.<com.mysql.cj.util.LazyString: int length()>();	if $i2 != 0 goto $z18 = 0;	$z18 = 0;	z1 = $z18;	$s3 = s0 & 128;	$i17 = (int) $s3;	if $i17 <= 0 goto $z19 = 0;	$z19 = 1;	goto [?= z2 = $z19];	z2 = $z19;	$i4 = virtualinvoke r1.<com.mysql.cj.util.LazyString: int length()>();	if $i4 <= 0 goto $z20 = 0;	$z20 = 0;	z3 = $z20;	if z2 == 0 goto $r82 = "binary";	$r82 = "binary";	$z21 = virtualinvoke $r82.<java.lang.String: boolean equalsIgnoreCase(java.lang.String)>(r2);	lookupswitch(i5) {     case 0: goto if z0 == 0 goto $r83 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType DECIMAL>;     case 1: goto if z0 != 0 goto (branch);     case 2: goto if z0 == 0 goto $r85 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType SMALLINT>;     case 3: goto if z0 == 0 goto $r86 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType INT>;     case 4: goto if z0 == 0 goto $r87 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType FLOAT>;     case 5: goto if z0 == 0 goto $r88 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType DOUBLE>;     case 6: goto $r69 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType NULL>;     case 7: goto $r68 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType TIMESTAMP>;     case 8: goto if z0 == 0 goto $r89 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType BIGINT>;     case 9: goto if z0 == 0 goto $r90 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType MEDIUMINT>;     case 10: goto $r67 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType DATE>;     case 11: goto $r66 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType TIME>;     case 12: goto $r65 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType DATETIME>;     case 13: goto $r64 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType YEAR>;     case 15: goto if $z21 == 0 goto $r58 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType VARCHAR>;     case 16: goto $r57 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType BIT>;     case 242: goto $r56 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType VECTOR>;     case 245: goto $r55 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType JSON>;     case 246: goto if z0 == 0 goto $r83 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType DECIMAL>;     case 247: goto $r54 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType ENUM>;     case 248: goto $r53 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType SET>;     case 249: goto if z2 == 0 goto $r91 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType TINYTEXT>;     case 250: goto if z2 == 0 goto $r92 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType MEDIUMTEXT>;     case 251: goto if z2 == 0 goto $r93 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType LONGTEXT>;     case 252: goto $r11 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType TINYBLOB>;     case 253: goto if $z21 == 0 goto $r58 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType VARCHAR>;     case 254: goto if $z21 == 0 goto $r4 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType CHAR>;     case 255: goto $r3 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType GEOMETRY>;     default: goto $r80 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType UNKNOWN>; };	$r53 = <com.mysql.cj.MysqlType: com.mysql.cj.MysqlType SET>;	return $r53
;block_num 12