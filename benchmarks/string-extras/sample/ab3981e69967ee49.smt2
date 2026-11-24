; origin: https://github.com/iscas-projects/SCB : hibernate-core/smt/method-org.hibernate.dialect.unique.DefaultUniqueDelegate__getAlterTableToAddUniqueKeyCommand__515348998/14643.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3263 0)
(declare-sort var2753 0)
(declare-sort var1234 0)
(declare-sort var3702 0)
(declare-sort var2902 0)
(declare-sort var1117 0)
(declare-sort var2393 0)
(declare-sort var2419 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun getTable/2028539592 (var1117) var2902)
(declare-fun cast-from-var2753-to-var1117 (var2753) var1117)
(declare-fun getQualifiedTableName/-853736433 (var2902) var2393)
(declare-fun var3702_format/1204537082 (var3702 var2393) String)
(declare-fun dialect/-331694648 (var3263) var2419)
(declare-fun getName/-2142322286 (var1117) String)
(declare-fun quote/1287717023 (var2419 String) String)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(declare-fun getAlterTableString/-573220996 (var2419 String) String)
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun uniqueConstraintSql/761474436 (var3263 var2753) String)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-const null-var3263 var3263)
(declare-const null-var2753 var2753)
(declare-const null-var1234 var1234)
(declare-const null-var3702 var3702)
(declare-const var819 var3263) ; Statement: r5 := @this: org.hibernate.dialect.unique.DefaultUniqueDelegate 
(assert (not (= var819 null-var3263)))
(declare-const var2438 var2753) ; Statement: r1 := @parameter0: org.hibernate.mapping.UniqueKey 
(assert (not (= var2438 null-var2753)))
(declare-const var3837 var1234) ; Statement: r19 := @parameter1: org.hibernate.boot.Metadata 
(assert (not (= var3837 null-var1234)))
(declare-const var3276 var3702) ; Statement: r0 := @parameter2: org.hibernate.boot.model.relational.SqlStringGenerationContext 
(assert (not (= var3276 null-var3702)))
(assert true)
(define-const var3813 var2902 (getTable/2028539592 (cast-from-var2753-to-var1117 var2438))) ; Statement: $r2 = virtualinvoke r1.<org.hibernate.mapping.UniqueKey: org.hibernate.mapping.Table getTable()>() 
(assert true)
(define-const var3796 var2393 (getQualifiedTableName/-853736433 var3813)) ; Statement: $r3 = virtualinvoke $r2.<org.hibernate.mapping.Table: org.hibernate.boot.model.relational.QualifiedTableName getQualifiedTableName()>() 
(define-const var940 String (var3702_format/1204537082 var3276 var3796)) ; Statement: r4 = interfaceinvoke r0.<org.hibernate.boot.model.relational.SqlStringGenerationContext: java.lang.String format(org.hibernate.boot.model.relational.QualifiedTableName)>($r3) 
(define-const var3392 var2419 (dialect/-331694648 var819)) ; Statement: $r6 = r5.<org.hibernate.dialect.unique.DefaultUniqueDelegate: org.hibernate.dialect.Dialect dialect> 
(assert true)
(define-const var442 String (getName/-2142322286 (cast-from-var2753-to-var1117 var2438))) ; Statement: $r7 = virtualinvoke r1.<org.hibernate.mapping.UniqueKey: java.lang.String getName()>() 
(assert true)
(define-const var2620 String (quote/1287717023 var3392 var442)) ; Statement: r8 = virtualinvoke $r6.<org.hibernate.dialect.Dialect: java.lang.String quote(java.lang.String)>($r7) 
(define-const var3119 String String-init) ; Statement: $r9 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var3119)) ; Statement: specialinvoke $r9.<java.lang.StringBuilder: void <init>()>() 
(declare-const var3119!1 String)
(assert (= var3119!1 ""))
(define-const var2937 var2419 (dialect/-331694648 var819)) ; Statement: $r10 = r5.<org.hibernate.dialect.unique.DefaultUniqueDelegate: org.hibernate.dialect.Dialect dialect> 
(assert true)
(define-const var3634 String (getAlterTableString/-573220996 var2937 var940)) ; Statement: $r11 = virtualinvoke $r10.<org.hibernate.dialect.Dialect: java.lang.String getAlterTableString(java.lang.String)>(r4) 
(assert true)
(define-const var3421 String (append/672562846 var3119!1 var3634)) ; Statement: $r12 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r11) 
(declare-const var3119!2 String)
(assert (= var3119!2 (str.++ var3119!1 var3634)))
(assert true)
(define-const var3011 String (append/672562846 var3421 " add constraint ")) ; Statement: $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(" add constraint ") 
(declare-const var3421!1 String)
(assert (= var3421!1 (str.++ var3421 " add constraint ")))
(assert true)
(define-const var1215 String (append/672562846 var3011 var2620)) ; Statement: $r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r8) 
(declare-const var3011!1 String)
(assert (= var3011!1 (str.++ var3011 var2620)))
(assert true)
(define-const var3212 String (append/672562846 var1215 " ")) ; Statement: $r16 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(" ") 
(declare-const var1215!1 String)
(assert (= var1215!1 (str.++ var1215 " ")))
(assert true)
(define-const var3601 String (uniqueConstraintSql/761474436 var819 var2438)) ; Statement: $r15 = virtualinvoke r5.<org.hibernate.dialect.unique.DefaultUniqueDelegate: java.lang.String uniqueConstraintSql(org.hibernate.mapping.UniqueKey)>(r1) 
(assert true)
(define-const var288 String (append/672562846 var3212 var3601)) ; Statement: $r17 = virtualinvoke $r16.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r15) 
(declare-const var3212!1 String)
(assert (= var3212!1 (str.++ var3212 var3601)))
(assert true)
(define-const var306 String (toString/-2075883882 var288)) ; Statement: $r18 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.String toString()>() 
 ; Statement: return $r18 
(check-sat)


; {getTable/2028539592=([org.hibernate.mapping.Constraint], org.hibernate.mapping.Table), cast-from-var2753-to-var1117=([org.hibernate.mapping.UniqueKey], org.hibernate.mapping.Constraint), getQualifiedTableName/-853736433=([org.hibernate.mapping.Table], org.hibernate.boot.model.relational.QualifiedTableName), var3702_format/1204537082=([org.hibernate.boot.model.relational.SqlStringGenerationContext, org.hibernate.boot.model.relational.QualifiedTableName], java.lang.String), dialect/-331694648=([org.hibernate.dialect.unique.DefaultUniqueDelegate], org.hibernate.dialect.Dialect), getName/-2142322286=([org.hibernate.mapping.Constraint], java.lang.String), quote/1287717023=([org.hibernate.dialect.Dialect, java.lang.String], java.lang.String), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), getAlterTableString/-573220996=([org.hibernate.dialect.Dialect, java.lang.String], java.lang.String), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), uniqueConstraintSql/761474436=([org.hibernate.dialect.unique.DefaultUniqueDelegate, org.hibernate.mapping.UniqueKey], java.lang.String), toString/-2075883882=([java.lang.StringBuilder], java.lang.String)}
; {var3263=org.hibernate.dialect.unique.DefaultUniqueDelegate, var819=r5, var2753=org.hibernate.mapping.UniqueKey, var2438=r1, var1234=org.hibernate.boot.Metadata, var3837=r19, var3702=org.hibernate.boot.model.relational.SqlStringGenerationContext, var3276=r0, var2902=org.hibernate.mapping.Table, var1117=org.hibernate.mapping.Constraint, var3813=$r2, var2393=org.hibernate.boot.model.relational.QualifiedTableName, var3796=$r3, var940=r4, var2419=org.hibernate.dialect.Dialect, var3392=$r6, var442=$r7, var2620=r8, var3119=$r9, var2937=$r10, var3634=$r11, var3421=$r12, var3011=$r13, var1215=$r14, var3212=$r16, var3601=$r15, var288=$r17, var306=$r18}
; {org.hibernate.dialect.unique.DefaultUniqueDelegate=var3263, r5=var819, org.hibernate.mapping.UniqueKey=var2753, r1=var2438, org.hibernate.boot.Metadata=var1234, r19=var3837, org.hibernate.boot.model.relational.SqlStringGenerationContext=var3702, r0=var3276, org.hibernate.mapping.Table=var2902, org.hibernate.mapping.Constraint=var1117, $r2=var3813, org.hibernate.boot.model.relational.QualifiedTableName=var2393, $r3=var3796, r4=var940, org.hibernate.dialect.Dialect=var2419, $r6=var3392, $r7=var442, r8=var2620, $r9=var3119, $r10=var2937, $r11=var3634, $r12=var3421, $r13=var3011, $r14=var1215, $r16=var3212, $r15=var3601, $r17=var288, $r18=var306}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 5,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r5 := @this: org.hibernate.dialect.unique.DefaultUniqueDelegate;	r1 := @parameter0: org.hibernate.mapping.UniqueKey;	r19 := @parameter1: org.hibernate.boot.Metadata;	r0 := @parameter2: org.hibernate.boot.model.relational.SqlStringGenerationContext;	$r2 = virtualinvoke r1.<org.hibernate.mapping.UniqueKey: org.hibernate.mapping.Table getTable()>();	$r3 = virtualinvoke $r2.<org.hibernate.mapping.Table: org.hibernate.boot.model.relational.QualifiedTableName getQualifiedTableName()>();	r4 = interfaceinvoke r0.<org.hibernate.boot.model.relational.SqlStringGenerationContext: java.lang.String format(org.hibernate.boot.model.relational.QualifiedTableName)>($r3);	$r6 = r5.<org.hibernate.dialect.unique.DefaultUniqueDelegate: org.hibernate.dialect.Dialect dialect>;	$r7 = virtualinvoke r1.<org.hibernate.mapping.UniqueKey: java.lang.String getName()>();	r8 = virtualinvoke $r6.<org.hibernate.dialect.Dialect: java.lang.String quote(java.lang.String)>($r7);	$r9 = new java.lang.StringBuilder;	specialinvoke $r9.<java.lang.StringBuilder: void <init>()>();	$r10 = r5.<org.hibernate.dialect.unique.DefaultUniqueDelegate: org.hibernate.dialect.Dialect dialect>;	$r11 = virtualinvoke $r10.<org.hibernate.dialect.Dialect: java.lang.String getAlterTableString(java.lang.String)>(r4);	$r12 = virtualinvoke $r9.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r11);	$r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(" add constraint ");	$r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r8);	$r16 = virtualinvoke $r14.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(" ");	$r15 = virtualinvoke r5.<org.hibernate.dialect.unique.DefaultUniqueDelegate: java.lang.String uniqueConstraintSql(org.hibernate.mapping.UniqueKey)>(r1);	$r17 = virtualinvoke $r16.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r15);	$r18 = virtualinvoke $r17.<java.lang.StringBuilder: java.lang.String toString()>();	return $r18
;block_num 1