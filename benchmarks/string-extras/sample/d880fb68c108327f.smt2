; origin: https://github.com/iscas-projects/SCB : hibernate-core/smt/method-org.hibernate.hql.internal.ast.tree.DotNode$1__buildIllegalCollectionDereferenceException__-233093643/20049.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var1015 0)
(declare-sort var3591 0)
(declare-sort var851 0)
(declare-sort var2256 0)
(declare-sort var509 0)
(declare-sort var1682 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun cast-from-var851-to-var2256 (var851) var2256)
(declare-fun var509_getPathText/-789293520 (var2256) String)
(declare-fun var1682-init () var1682)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun <init>/-1391884909 (var1682 String) void)
(declare-const null-var1015 var1015)
(declare-const null-String String)
(declare-const null-var851 var851)
(declare-const var80 var1015) ; Statement: r11 := @this: org.hibernate.hql.internal.ast.tree.DotNode$1 
(assert (not (= var80 null-var1015)))
(declare-const var459 String) ; Statement: r6 := @parameter0: java.lang.String 
(assert (not (= var459 null-String)))
(declare-const var1517 var851) ; Statement: r0 := @parameter1: org.hibernate.hql.internal.ast.tree.FromReferenceNode 
(assert (not (= var1517 null-var851)))
(define-const var2071 var2256 (cast-from-var851-to-var2256 var1517)) ; Statement: $r14 = (antlr.collections.AST) r0 
(define-const var915 String (var509_getPathText/-789293520 var2071)) ; Statement: r1 = staticinvoke <org.hibernate.hql.internal.ast.util.ASTUtil: java.lang.String getPathText(antlr.collections.AST)>($r14) 
(define-const var2266 var1682 var1682-init) ; Statement: $r13 = new org.hibernate.QueryException 
(define-const var1263 String String-init) ; Statement: $r12 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var1263)) ; Statement: specialinvoke $r12.<java.lang.StringBuilder: void <init>()>() 
(declare-const var1263!1 String)
(assert (= var1263!1 ""))
(assert true)
(define-const var3378 String (append/672562846 var1263!1 "illegal attempt to dereference collection [")) ; Statement: $r4 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("illegal attempt to dereference collection [") 
(declare-const var1263!2 String)
(assert (= var1263!2 (str.++ var1263!1 "illegal attempt to dereference collection [")))
(assert true)
(define-const var522 String (append/672562846 var3378 var915)) ; Statement: $r5 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r1) 
(declare-const var3378!1 String)
(assert (= var3378!1 (str.++ var3378 var915)))
(assert true)
(define-const var3063 String (append/672562846 var522 "] with element property reference [")) ; Statement: $r7 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("] with element property reference [") 
(declare-const var522!1 String)
(assert (= var522!1 (str.++ var522 "] with element property reference [")))
(assert true)
(define-const var2636 String (append/672562846 var3063 var459)) ; Statement: $r8 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r6) 
(declare-const var3063!1 String)
(assert (= var3063!1 (str.++ var3063 var459)))
(assert true)
(define-const var3252 String (append/672562846 var2636 "]")) ; Statement: $r9 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("]") 
(declare-const var2636!1 String)
(assert (= var2636!1 (str.++ var2636 "]")))
(assert true)
(define-const var3706 String (toString/-2075883882 var3252)) ; Statement: $r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert true)
;(assert (<init>/-1391884909 var2266 var3706)) ; Statement: specialinvoke $r13.<org.hibernate.QueryException: void <init>(java.lang.String)>($r10) 

(declare-const var2266!1 var1682)
(declare-const var3706!1 String)
 ; Statement: return $r13 
(check-sat)


; {cast-from-var851-to-var2256=([org.hibernate.hql.internal.ast.tree.FromReferenceNode], antlr.collections.AST), var509_getPathText/-789293520=([antlr.collections.AST], java.lang.String), var1682-init=([], org.hibernate.QueryException), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), <init>/-1391884909=([org.hibernate.QueryException, java.lang.String], void)}
; {var1015=org.hibernate.hql.internal.ast.tree.DotNode$1, var80=r11, var459=r6, var3591=null_type, var851=org.hibernate.hql.internal.ast.tree.FromReferenceNode, var1517=r0, var2256=antlr.collections.AST, var2071=$r14, var509=org.hibernate.hql.internal.ast.util.ASTUtil, var915=r1, var1682=org.hibernate.QueryException, var2266=$r13, var1263=$r12, var3378=$r4, var522=$r5, var3063=$r7, var2636=$r8, var3252=$r9, var3706=$r10}
; {org.hibernate.hql.internal.ast.tree.DotNode$1=var1015, r11=var80, r6=var459, null_type=var3591, org.hibernate.hql.internal.ast.tree.FromReferenceNode=var851, r0=var1517, antlr.collections.AST=var2256, $r14=var2071, org.hibernate.hql.internal.ast.util.ASTUtil=var509, r1=var915, org.hibernate.QueryException=var1682, $r13=var2266, $r12=var1263, $r4=var3378, $r5=var522, $r7=var3063, $r8=var2636, $r9=var3252, $r10=var3706}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 5,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r11 := @this: org.hibernate.hql.internal.ast.tree.DotNode$1;	r6 := @parameter0: java.lang.String;	r0 := @parameter1: org.hibernate.hql.internal.ast.tree.FromReferenceNode;	$r14 = (antlr.collections.AST) r0;	r1 = staticinvoke <org.hibernate.hql.internal.ast.util.ASTUtil: java.lang.String getPathText(antlr.collections.AST)>($r14);	$r13 = new org.hibernate.QueryException;	$r12 = new java.lang.StringBuilder;	specialinvoke $r12.<java.lang.StringBuilder: void <init>()>();	$r4 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("illegal attempt to dereference collection [");	$r5 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r1);	$r7 = virtualinvoke $r5.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("] with element property reference [");	$r8 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r6);	$r9 = virtualinvoke $r8.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("]");	$r10 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.String toString()>();	specialinvoke $r13.<org.hibernate.QueryException: void <init>(java.lang.String)>($r10);	return $r13
;block_num 1