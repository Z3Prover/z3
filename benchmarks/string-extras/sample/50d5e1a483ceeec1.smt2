; origin: https://github.com/iscas-projects/SCB : mybatis/smt/method-org.apache.ibatis.reflection.property.PropertyTokenizer__《init》__-1028628872/1892-deviant-0.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3071 0)
(declare-sort var1501 0)
(declare-sort var206 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun <init>/-279557996 (var206) void)
(declare-fun cast-from-var3071-to-var206 (var3071) var206)
(define-fun indexOf/-1037706067 ((s String) (c Int)) Int (str.indexof s (str.from_code c) 0))
(define-fun cast-from-Int-to-Int ((arg Int)) Int arg)
(define-fun substring/-1240304868 ((s String) (begin Int) (end Int)) String (str.substr s begin (- end begin)))
(declare-fun name/-1582476214 (var3071) String)
(define-fun substring/850833817 ((s String) (begin Int)) String (str.substr s begin (- (str.len s) begin)))
(declare-fun children/-1582476214 (var3071) String)
(declare-fun indexedName/-1582476214 (var3071) String)
(declare-const null-var3071 var3071)
(declare-const null-String String)
(declare-const var2416 var3071) ; Statement: r0 := @this: org.apache.ibatis.reflection.property.PropertyTokenizer 
(assert (not (= var2416 null-var3071)))
(declare-const var2424 String) ; Statement: r1 := @parameter0: java.lang.String 
(assert (not (= var2424 null-String)))
(assert true)
;(assert (<init>/-279557996 (cast-from-var3071-to-var206 var2416))) ; Statement: specialinvoke r0.<java.lang.Object: void <init>()>() 

(declare-const var2416!1 var3071)
(assert true)
(define-const var2887 Int (indexOf/-1037706067 var2424 46)) ; Statement: i5 = virtualinvoke r1.<java.lang.String: int indexOf(int)>(46) 
(define-const var3873 Int (cast-from-Int-to-Int (- 1))) ; Statement: $i7 = (int) -1 
 ; Statement: if i5 <= $i7 goto r0.<org.apache.ibatis.reflection.property.PropertyTokenizer: java.lang.String name> = r1 
(assert (not (<= var2887 var3873))) ; Negate: Cond: i5 <= $i7  
(assert (not (and true (and (>= 0 0) (>= (str.len var2424) var2887) (>= var2887 0)))))
(check-sat)


; {<init>/-279557996=([java.lang.Object], void), cast-from-var3071-to-var206=([org.apache.ibatis.reflection.property.PropertyTokenizer], java.lang.Object), indexOf/-1037706067=([java.lang.String, int], int), cast-from-Int-to-Int=([int], int), substring/-1240304868=([java.lang.String, int, int], java.lang.String), name/-1582476214=([org.apache.ibatis.reflection.property.PropertyTokenizer], java.lang.String), substring/850833817=([java.lang.String, int], java.lang.String), children/-1582476214=([org.apache.ibatis.reflection.property.PropertyTokenizer], java.lang.String), indexedName/-1582476214=([org.apache.ibatis.reflection.property.PropertyTokenizer], java.lang.String)}
; {var3071=org.apache.ibatis.reflection.property.PropertyTokenizer, var2416=r0, var2424=r1, var1501=null_type, var206=java.lang.Object, var2887=i5, var3873=$i7, var768=$r9, var3897=$i3, var3492=$r10, var778=$r2, var230=$r3, var3960=$i4, var2245=$i9}
; {org.apache.ibatis.reflection.property.PropertyTokenizer=var3071, r0=var2416, r1=var2424, null_type=var1501, java.lang.Object=var206, i5=var2887, $i7=var3873, $r9=var768, $i3=var3897, $r10=var3492, $r2=var778, $r3=var230, $i4=var3960, $i9=var2245}
;seq <java.lang.String: int indexOf(int)>;	<java.lang.String: java.lang.String substring(int,int)>;	<java.lang.String: java.lang.String substring(int)>;	<java.lang.String: int indexOf(int)>
;cnt {"<java.lang.String: int indexOf(int)>": 2,"<java.lang.String: java.lang.String substring(int,int)>": 1,"<java.lang.String: java.lang.String substring(int)>": 1}
;stmts r0 := @this: org.apache.ibatis.reflection.property.PropertyTokenizer;	r1 := @parameter0: java.lang.String;	specialinvoke r0.<java.lang.Object: void <init>()>();	i5 = virtualinvoke r1.<java.lang.String: int indexOf(int)>(46);	$i7 = (int) -1;	if i5 <= $i7 goto r0.<org.apache.ibatis.reflection.property.PropertyTokenizer: java.lang.String name> = r1;	$r9 = virtualinvoke r1.<java.lang.String: java.lang.String substring(int,int)>(0, i5);	r0.<org.apache.ibatis.reflection.property.PropertyTokenizer: java.lang.String name> = $r9;	$i3 = i5 + 1;	$r10 = virtualinvoke r1.<java.lang.String: java.lang.String substring(int)>($i3);	r0.<org.apache.ibatis.reflection.property.PropertyTokenizer: java.lang.String children> = $r10;	goto [?= $r2 = r0.<org.apache.ibatis.reflection.property.PropertyTokenizer: java.lang.String name>];	$r2 = r0.<org.apache.ibatis.reflection.property.PropertyTokenizer: java.lang.String name>;	r0.<org.apache.ibatis.reflection.property.PropertyTokenizer: java.lang.String indexedName> = $r2;	$r3 = r0.<org.apache.ibatis.reflection.property.PropertyTokenizer: java.lang.String name>;	$i4 = virtualinvoke $r3.<java.lang.String: int indexOf(int)>(91);	$i9 = (int) -1;	if $i4 <= $i9 goto return;	return
;block_num 4