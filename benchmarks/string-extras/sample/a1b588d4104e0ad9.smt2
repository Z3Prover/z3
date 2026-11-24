; origin: https://github.com/iscas-projects/SCB : hibernate-core/smt/method-org.hibernate.jpa.boot.internal.PersistenceXmlParser__extractInfo__1373278956/25763.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var1863 0)
(declare-sort var576 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun cast-from-var1863-to-var576 (var1863) var576)
(declare-fun getLineNumber/1890756870 (var576) Int)
(define-fun append/-1001720160 ((s String) (tail Int)) String (str.++ s (str.from_int tail)))
(declare-fun getColumnNumber/2042233444 (var576) Int)
(declare-fun getMessage/-2074868419 (var1863) String)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-const null-var1863 var1863)
(declare-const var2982 var1863) ; Statement: r0 := @parameter0: org.xml.sax.SAXException 
(assert (not (= var2982 null-var1863)))
(define-const var3514 Bool false) ; Statement: $z0 = r0 instanceof org.xml.sax.SAXParseException 
 ; Statement: if $z0 == 0 goto $r1 = new java.lang.StringBuilder 
(assert (not (= (ite var3514 1 0) 0))) ; Negate: Cond: $z0 == 0  
(define-const var2576 String String-init) ; Statement: $r6 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var2576)) ; Statement: specialinvoke $r6.<java.lang.StringBuilder: void <init>()>() 
(declare-const var2576!1 String)
(assert (= var2576!1 ""))
(assert true)
(define-const var3240 String (append/672562846 var2576!1 "Error parsing XML [line : ")) ; Statement: $r8 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Error parsing XML [line : ") 
(declare-const var2576!2 String)
(assert (= var2576!2 (str.++ var2576!1 "Error parsing XML [line : ")))
(define-const var1330 var576 (cast-from-var1863-to-var576 var2982)) ; Statement: $r7 = (org.xml.sax.SAXParseException) r0 
(assert true)
(define-const var3084 Int (getLineNumber/1890756870 var1330)) ; Statement: $i0 = virtualinvoke $r7.<org.xml.sax.SAXParseException: int getLineNumber()>() 
(assert true)
(define-const var685 String (append/-1001720160 var3240 var3084)) ; Statement: $r9 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i0) 
(declare-const var3240!1 String)
(assert (str.prefixof var3240 var3240!1))
(assert true)
(define-const var327 String (append/672562846 var685 ", column : ")) ; Statement: $r11 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", column : ") 
(declare-const var685!1 String)
(assert (= var685!1 (str.++ var685 ", column : ")))
(define-const var3885 var576 (cast-from-var1863-to-var576 var2982)) ; Statement: $r10 = (org.xml.sax.SAXParseException) r0 
(assert true)
(define-const var2204 Int (getColumnNumber/2042233444 var3885)) ; Statement: $i1 = virtualinvoke $r10.<org.xml.sax.SAXParseException: int getColumnNumber()>() 
(assert true)
(define-const var2047 String (append/-1001720160 var327 var2204)) ; Statement: $r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i1) 
(declare-const var327!1 String)
(assert (str.prefixof var327 var327!1))
(assert true)
(define-const var3068 String (append/672562846 var2047 "] : ")) ; Statement: $r14 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("] : ") 
(declare-const var2047!1 String)
(assert (= var2047!1 (str.++ var2047 "] : ")))
(assert true)
(define-const var239 String (getMessage/-2074868419 var2982)) ; Statement: $r13 = virtualinvoke r0.<org.xml.sax.SAXException: java.lang.String getMessage()>() 
(assert true)
(define-const var2541 String (append/672562846 var3068 var239)) ; Statement: $r15 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r13) 
(declare-const var3068!1 String)
(assert (= var3068!1 (str.++ var3068 var239)))
(assert true)
(define-const var1396 String (toString/-2075883882 var2541)) ; Statement: $r16 = virtualinvoke $r15.<java.lang.StringBuilder: java.lang.String toString()>() 
 ; Statement: return $r16 
(check-sat)


; {String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), cast-from-var1863-to-var576=([org.xml.sax.SAXException], org.xml.sax.SAXParseException), getLineNumber/1890756870=([org.xml.sax.SAXParseException], int), append/-1001720160=([java.lang.StringBuilder, int], java.lang.StringBuilder), getColumnNumber/2042233444=([org.xml.sax.SAXParseException], int), getMessage/-2074868419=([org.xml.sax.SAXException], java.lang.String), toString/-2075883882=([java.lang.StringBuilder], java.lang.String)}
; {var1863=org.xml.sax.SAXException, var2982=r0, var3514=$z0, var2576=$r6, var3240=$r8, var576=org.xml.sax.SAXParseException, var1330=$r7, var3084=$i0, var685=$r9, var327=$r11, var3885=$r10, var2204=$i1, var2047=$r12, var3068=$r14, var239=$r13, var2541=$r15, var1396=$r16}
; {org.xml.sax.SAXException=var1863, r0=var2982, $z0=var3514, $r6=var2576, $r8=var3240, org.xml.sax.SAXParseException=var576, $r7=var1330, $i0=var3084, $r9=var685, $r11=var327, $r10=var3885, $i1=var2204, $r12=var2047, $r14=var3068, $r13=var239, $r15=var2541, $r16=var1396}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(int)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(int)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 4,"<java.lang.StringBuilder: java.lang.StringBuilder append(int)>": 2,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r0 := @parameter0: org.xml.sax.SAXException;	$z0 = r0 instanceof org.xml.sax.SAXParseException;	if $z0 == 0 goto $r1 = new java.lang.StringBuilder;	$r6 = new java.lang.StringBuilder;	specialinvoke $r6.<java.lang.StringBuilder: void <init>()>();	$r8 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Error parsing XML [line : ");	$r7 = (org.xml.sax.SAXParseException) r0;	$i0 = virtualinvoke $r7.<org.xml.sax.SAXParseException: int getLineNumber()>();	$r9 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i0);	$r11 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", column : ");	$r10 = (org.xml.sax.SAXParseException) r0;	$i1 = virtualinvoke $r10.<org.xml.sax.SAXParseException: int getColumnNumber()>();	$r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>($i1);	$r14 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("] : ");	$r13 = virtualinvoke r0.<org.xml.sax.SAXException: java.lang.String getMessage()>();	$r15 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r13);	$r16 = virtualinvoke $r15.<java.lang.StringBuilder: java.lang.String toString()>();	return $r16
;block_num 2