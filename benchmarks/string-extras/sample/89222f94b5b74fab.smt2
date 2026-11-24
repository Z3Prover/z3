; origin: https://github.com/iscas-projects/SCB : poi-ooxml/smt/method-org.apache.poi.xssf.usermodel.XSSFSheet__createTable__1442319692/13757.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3103 0)
(declare-sort var1976 0)
(declare-sort var2460 0)
(declare-sort var2071 0)
(declare-sort var3043 0)
(declare-sort var858 0)
(declare-sort var995 0)
(declare-sort var1505 0)
(declare-sort var709 0)
(declare-sort var3849 0)
(declare-sort var3690 0)
(declare-sort var701 0)
(declare-sort var3430 0)
(declare-sort var2993 0)
(declare-sort var1618 0)
(declare-sort var1770 0)
(declare-sort var2603 0)
(declare-sort var3821 0)
(declare-sort var983 0)
(declare-sort var3078 0)
(declare-sort var1367 0)
(declare-sort var1280 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun worksheet/-1100774885 (var3103) var2460)
(declare-fun var2460_isSetTableParts/529019459 (var2460) Bool)
(declare-fun var2460_getTableParts/75695243 (var2460) var2071)
(declare-fun var2071_addNewTablePart/-2107157522 (var2071) var3043)
(declare-fun getPackagePart/-804310696 (var995) var858)
(declare-fun cast-from-var3103-to-var995 (var3103) var995)
(declare-fun getPackage/-674655752 (var858) var1505)
(declare-fun getContentType/-305056247 (var3849) String)
(declare-fun cast-from-var709-to-var3849 (var709) var3849)
(declare-fun getPartsByContentType/1630629848 (var1505 String) var3690)
(declare-fun size/-1863229846 (var3690) Int)
(declare-fun getWorkbook/803238250 (var3103) var701)
(declare-fun getXssfFactory/-1892579267 (var701) var3430)
(declare-fun createRelationship/-690834589 (var995 var3849 var1618 Int Bool) var2993)
(declare-fun cast-from-var3430-to-var1618 (var3430) var1618)
(declare-fun getDocumentPart/-1970130122 (var2993) var995)
(declare-fun cast-from-var995-to-var1770 (var995) var1770)
(declare-fun getRelationship/-613156679 (var2993) var2603)
(declare-fun getId/-2087847944 (var2603) String)
(declare-fun var3043_setId/-2088125658 (var3043 String) void)
(declare-fun getCTTable/1970813040 (var1770) var3821)
(define-fun cast-from-Int-to-Int ((arg Int)) Int arg)
(declare-fun var3821_setId/-237966992 (var3821 Int) void)
(declare-fun tables/-1100774885 (var3103) var983)
(declare-fun var3043_getId/466970204 (var3043) String)
(declare-fun var3078_put/1464166817 (var3078 var1367 var1367) var1367)
(declare-fun cast-from-var983-to-var3078 (var983) var3078)
(declare-fun cast-from-String-to-var1367 (String) var1367)
(declare-fun cast-from-var1770-to-var1367 (var1770) var1367)
(declare-fun supportsAreaReference/-1269201419 (var1770 var1976) Bool)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(define-fun append/-1001720160 ((s String) (tail Int)) String (str.++ s (str.from_int tail)))
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun getTable/-45928524 (var701 String) var1770)
(declare-fun getName/1133501234 (var701 String) var1280)
(declare-fun setDisplayName/-665487393 (var1770 String) void)
(declare-fun setName/-2101874579 (var1770 String) void)
(declare-const null-var3103 var3103)
(declare-const null-var1976 var1976)
(declare-const var709-TABLE var709)
(declare-const null-var1770 var1770)
(declare-const null-var1280 var1280)
(declare-const var2475 var3103) ; Statement: r0 := @this: org.apache.poi.xssf.usermodel.XSSFSheet 
(assert (not (= var2475 null-var3103)))
(declare-const var2097 var1976) ; Statement: r17 := @parameter0: org.apache.poi.ss.util.AreaReference 
(assert (not (= var2097 null-var1976)))
(define-const var2248 var2460 (worksheet/-1100774885 var2475)) ; Statement: $r1 = r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet worksheet> 
(define-const var2400 Bool (var2460_isSetTableParts/529019459 var2248)) ; Statement: $z0 = interfaceinvoke $r1.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet: boolean isSetTableParts()>() 
 ; Statement: if $z0 != 0 goto $r2 = r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet worksheet> 
(assert (not (= (ite var2400 1 0) 0))) ; Cond: $z0 != 0 
(define-const var3120 var2460 (worksheet/-1100774885 var2475)) ; Statement: $r2 = r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet worksheet> 
(define-const var438 var2071 (var2460_getTableParts/75695243 var3120)) ; Statement: $r35 = interfaceinvoke $r2.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTableParts getTableParts()>() 
(define-const var203 var3043 (var2071_addNewTablePart/-2107157522 var438)) ; Statement: $r36 = interfaceinvoke $r35.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTableParts: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTablePart addNewTablePart()>() 
(assert true)
(define-const var3687 var858 (getPackagePart/-804310696 (cast-from-var3103-to-var995 var2475))) ; Statement: $r3 = virtualinvoke r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.apache.poi.openxml4j.opc.PackagePart getPackagePart()>() 
(assert true)
(define-const var3317 var1505 (getPackage/-674655752 var3687)) ; Statement: $r6 = virtualinvoke $r3.<org.apache.poi.openxml4j.opc.PackagePart: org.apache.poi.openxml4j.opc.OPCPackage getPackage()>() 
(define-const var1856 var709 var709-TABLE) ; Statement: $r4 = <org.apache.poi.xssf.usermodel.XSSFRelation: org.apache.poi.xssf.usermodel.XSSFRelation TABLE> 
(assert true)
(define-const var3051 String (getContentType/-305056247 (cast-from-var709-to-var3849 var1856))) ; Statement: $r5 = virtualinvoke $r4.<org.apache.poi.xssf.usermodel.XSSFRelation: java.lang.String getContentType()>() 
(assert true)
(define-const var574 var3690 (getPartsByContentType/1630629848 var3317 var3051)) ; Statement: $r7 = virtualinvoke $r6.<org.apache.poi.openxml4j.opc.OPCPackage: java.util.ArrayList getPartsByContentType(java.lang.String)>($r5) 
(assert true)
(define-const var2411 Int (size/-1863229846 var574)) ; Statement: $i0 = virtualinvoke $r7.<java.util.ArrayList: int size()>() 
(define-const var3951 Int (+ var2411 1)) ; Statement: i2 = $i0 + 1 
(define-const var3539 Bool (ite (= 1 1) true false)) ; Statement: z4 = 1 
(assert true) ; Non Conditional
 ; Statement: if z4 == 0 goto $r8 = <org.apache.poi.xssf.usermodel.XSSFRelation: org.apache.poi.xssf.usermodel.XSSFRelation TABLE> 
(assert (= (ite var3539 1 0) 0)) ; Cond: z4 == 0 
(define-const var483 var709 var709-TABLE) ; Statement: $r8 = <org.apache.poi.xssf.usermodel.XSSFRelation: org.apache.poi.xssf.usermodel.XSSFRelation TABLE> 
(assert true)
(define-const var2629 var701 (getWorkbook/803238250 var2475)) ; Statement: $r9 = virtualinvoke r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.apache.poi.xssf.usermodel.XSSFWorkbook getWorkbook()>() 
(assert true)
(define-const var2512 var3430 (getXssfFactory/-1892579267 var2629)) ; Statement: $r10 = virtualinvoke $r9.<org.apache.poi.xssf.usermodel.XSSFWorkbook: org.apache.poi.xssf.usermodel.XSSFFactory getXssfFactory()>() 
(assert true)
(define-const var2214 var2993 (createRelationship/-690834589 (cast-from-var3103-to-var995 var2475) (cast-from-var709-to-var3849 var483) (cast-from-var3430-to-var1618 var2512) var3951 (ite (= 1 0) true false))) ; Statement: r40 = virtualinvoke r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.apache.poi.ooxml.POIXMLDocumentPart$RelationPart createRelationship(org.apache.poi.ooxml.POIXMLRelation,org.apache.poi.ooxml.POIXMLFactory,int,boolean)>($r8, $r10, i2, 0) 
(assert true)
(define-const var3243 var995 (getDocumentPart/-1970130122 var2214)) ; Statement: $r11 = virtualinvoke r40.<org.apache.poi.ooxml.POIXMLDocumentPart$RelationPart: org.apache.poi.ooxml.POIXMLDocumentPart getDocumentPart()>() 
(define-const var1941 var1770 (cast-from-var995-to-var1770 var3243)) ; Statement: r41 = (org.apache.poi.xssf.usermodel.XSSFTable) $r11 
(assert true)
(define-const var292 var2603 (getRelationship/-613156679 var2214)) ; Statement: $r12 = virtualinvoke r40.<org.apache.poi.ooxml.POIXMLDocumentPart$RelationPart: org.apache.poi.openxml4j.opc.PackageRelationship getRelationship()>() 
(assert true)
(define-const var3284 String (getId/-2087847944 var292)) ; Statement: $r13 = virtualinvoke $r12.<org.apache.poi.openxml4j.opc.PackageRelationship: java.lang.String getId()>() 
;(assert (var3043_setId/-2088125658 var203 var3284)) ; Statement: interfaceinvoke $r36.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTablePart: void setId(java.lang.String)>($r13) 

(declare-const var203!1 var3043)
(declare-const var3284!1 String)
(assert true)
(define-const var3605 var3821 (getCTTable/1970813040 var1941)) ; Statement: $r14 = virtualinvoke r41.<org.apache.poi.xssf.usermodel.XSSFTable: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTable getCTTable()>() 
(define-const var3245 Int (cast-from-Int-to-Int var3951)) ; Statement: $l1 = (long) i2 
;(assert (var3821_setId/-237966992 var3605 var3245)) ; Statement: interfaceinvoke $r14.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTable: void setId(long)>($l1) 

(declare-const var3605!1 var3821)
(declare-const var3245!1 Int)
(define-const var1653 var983 (tables/-1100774885 var2475)) ; Statement: $r15 = r0.<org.apache.poi.xssf.usermodel.XSSFSheet: java.util.SortedMap tables> 
(define-const var3583 String (var3043_getId/466970204 var203!1)) ; Statement: $r16 = interfaceinvoke $r36.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTablePart: java.lang.String getId()>() 
;(assert (var3078_put/1464166817 (cast-from-var983-to-var3078 var1653) (cast-from-String-to-var1367 var3583) (cast-from-var1770-to-var1367 var1941))) ; Statement: interfaceinvoke $r15.<java.util.SortedMap: java.lang.Object put(java.lang.Object,java.lang.Object)>($r16, r41) 

(declare-const var1653!1 var983)
(declare-const var3583!1 String)
(declare-const var1941!1 var1770)
 ; Statement: if r17 == null goto (branch) 
(assert (not (= var2097 null-var1976))) ; Negate: Cond: r17 == null  
(assert true)
(define-const var1753 Bool (supportsAreaReference/-1269201419 var1941!1 var2097)) ; Statement: $z1 = virtualinvoke r41.<org.apache.poi.xssf.usermodel.XSSFTable: boolean supportsAreaReference(org.apache.poi.ss.util.AreaReference)>(r17) 
 ; Statement: if $z1 == 0 goto (branch) 
(assert (= (ite var1753 1 0) 0)) ; Cond: $z1 == 0 
 ; Statement: if i2 >= 2147483647 goto return r41 
(assert (not (>= var3951 2147483647))) ; Negate: Cond: i2 >= 2147483647  
(define-const var2693 String String-init) ; Statement: $r18 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var2693)) ; Statement: specialinvoke $r18.<java.lang.StringBuilder: void <init>()>() 
(declare-const var2693!1 String)
(assert (= var2693!1 ""))
(assert true)
(define-const var1509 String (append/672562846 var2693!1 "Table")) ; Statement: $r19 = virtualinvoke $r18.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Table") 
(declare-const var2693!2 String)
(assert (= var2693!2 (str.++ var2693!1 "Table")))
(assert true)
(define-const var1703 String (append/-1001720160 var1509 var3951)) ; Statement: $r20 = virtualinvoke $r19.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>(i2) 
(declare-const var1509!1 String)
(assert (str.prefixof var1509 var1509!1))
(assert true)
(define-const var3017 String (toString/-2075883882 var1703)) ; Statement: r42 = virtualinvoke $r20.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert true)
(define-const var1891 var701 (getWorkbook/803238250 var2475)) ; Statement: $r21 = virtualinvoke r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.apache.poi.xssf.usermodel.XSSFWorkbook getWorkbook()>() 
(assert true)
(define-const var1327 var1770 (getTable/-45928524 var1891 var3017)) ; Statement: $r22 = virtualinvoke $r21.<org.apache.poi.xssf.usermodel.XSSFWorkbook: org.apache.poi.xssf.usermodel.XSSFTable getTable(java.lang.String)>(r42) 
 ; Statement: if $r22 != null goto i2 = i2 + 1 
(assert (not (not (= var1327 null-var1770)))) ; Negate: Cond: $r22 != null  
(assert true)
(define-const var2118 var701 (getWorkbook/803238250 var2475)) ; Statement: $r23 = virtualinvoke r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.apache.poi.xssf.usermodel.XSSFWorkbook getWorkbook()>() 
(assert true)
(define-const var2323 var1280 (getName/1133501234 var2118 var3017)) ; Statement: $r24 = virtualinvoke $r23.<org.apache.poi.xssf.usermodel.XSSFWorkbook: org.apache.poi.xssf.usermodel.XSSFName getName(java.lang.String)>(r42) 
 ; Statement: if $r24 != null goto i2 = i2 + 1 
(assert (not (not (= var2323 null-var1280)))) ; Negate: Cond: $r24 != null  
(assert true)
;(assert (setDisplayName/-665487393 var1941!1 var3017)) ; Statement: virtualinvoke r41.<org.apache.poi.xssf.usermodel.XSSFTable: void setDisplayName(java.lang.String)>(r42) 

(declare-const var1941!2 var1770)
(declare-const var3017!1 String)
(assert true)
;(assert (setName/-2101874579 var1941!2 var3017!1)) ; Statement: virtualinvoke r41.<org.apache.poi.xssf.usermodel.XSSFTable: void setName(java.lang.String)>(r42) 

(declare-const var1941!3 var1770)
(declare-const var3017!2 String)
 ; Statement: goto [?= return r41] 
(assert true) ; Non Conditional
 ; Statement: return r41 
(check-sat)


; {worksheet/-1100774885=([org.apache.poi.xssf.usermodel.XSSFSheet], org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet), var2460_isSetTableParts/529019459=([org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet], boolean), var2460_getTableParts/75695243=([org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet], org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTableParts), var2071_addNewTablePart/-2107157522=([org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTableParts], org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTablePart), getPackagePart/-804310696=([org.apache.poi.ooxml.POIXMLDocumentPart], org.apache.poi.openxml4j.opc.PackagePart), cast-from-var3103-to-var995=([org.apache.poi.xssf.usermodel.XSSFSheet], org.apache.poi.ooxml.POIXMLDocumentPart), getPackage/-674655752=([org.apache.poi.openxml4j.opc.PackagePart], org.apache.poi.openxml4j.opc.OPCPackage), getContentType/-305056247=([org.apache.poi.ooxml.POIXMLRelation], java.lang.String), cast-from-var709-to-var3849=([org.apache.poi.xssf.usermodel.XSSFRelation], org.apache.poi.ooxml.POIXMLRelation), getPartsByContentType/1630629848=([org.apache.poi.openxml4j.opc.OPCPackage, java.lang.String], java.util.ArrayList), size/-1863229846=([java.util.ArrayList], int), getWorkbook/803238250=([org.apache.poi.xssf.usermodel.XSSFSheet], org.apache.poi.xssf.usermodel.XSSFWorkbook), getXssfFactory/-1892579267=([org.apache.poi.xssf.usermodel.XSSFWorkbook], org.apache.poi.xssf.usermodel.XSSFFactory), createRelationship/-690834589=([org.apache.poi.ooxml.POIXMLDocumentPart, org.apache.poi.ooxml.POIXMLRelation, org.apache.poi.ooxml.POIXMLFactory, int, boolean], org.apache.poi.ooxml.POIXMLDocumentPart$RelationPart), cast-from-var3430-to-var1618=([org.apache.poi.xssf.usermodel.XSSFFactory], org.apache.poi.ooxml.POIXMLFactory), getDocumentPart/-1970130122=([org.apache.poi.ooxml.POIXMLDocumentPart$RelationPart], org.apache.poi.ooxml.POIXMLDocumentPart), cast-from-var995-to-var1770=([org.apache.poi.ooxml.POIXMLDocumentPart], org.apache.poi.xssf.usermodel.XSSFTable), getRelationship/-613156679=([org.apache.poi.ooxml.POIXMLDocumentPart$RelationPart], org.apache.poi.openxml4j.opc.PackageRelationship), getId/-2087847944=([org.apache.poi.openxml4j.opc.PackageRelationship], java.lang.String), var3043_setId/-2088125658=([org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTablePart, java.lang.String], void), getCTTable/1970813040=([org.apache.poi.xssf.usermodel.XSSFTable], org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTable), cast-from-Int-to-Int=([int], long), var3821_setId/-237966992=([org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTable, long], void), tables/-1100774885=([org.apache.poi.xssf.usermodel.XSSFSheet], java.util.SortedMap), var3043_getId/466970204=([org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTablePart], java.lang.String), var3078_put/1464166817=([java.util.Map, java.lang.Object, java.lang.Object], java.lang.Object), cast-from-var983-to-var3078=([java.util.SortedMap], java.util.Map), cast-from-String-to-var1367=([java.lang.String], java.lang.Object), cast-from-var1770-to-var1367=([org.apache.poi.xssf.usermodel.XSSFTable], java.lang.Object), supportsAreaReference/-1269201419=([org.apache.poi.xssf.usermodel.XSSFTable, org.apache.poi.ss.util.AreaReference], boolean), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), append/-1001720160=([java.lang.StringBuilder, int], java.lang.StringBuilder), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), getTable/-45928524=([org.apache.poi.xssf.usermodel.XSSFWorkbook, java.lang.String], org.apache.poi.xssf.usermodel.XSSFTable), getName/1133501234=([org.apache.poi.xssf.usermodel.XSSFWorkbook, java.lang.String], org.apache.poi.xssf.usermodel.XSSFName), setDisplayName/-665487393=([org.apache.poi.xssf.usermodel.XSSFTable, java.lang.String], void), setName/-2101874579=([org.apache.poi.xssf.usermodel.XSSFTable, java.lang.String], void)}
; {var3103=org.apache.poi.xssf.usermodel.XSSFSheet, var2475=r0, var1976=org.apache.poi.ss.util.AreaReference, var2097=r17, var2460=org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet, var2248=$r1, var2400=$z0, var3120=$r2, var2071=org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTableParts, var438=$r35, var3043=org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTablePart, var203=$r36, var858=org.apache.poi.openxml4j.opc.PackagePart, var995=org.apache.poi.ooxml.POIXMLDocumentPart, var3687=$r3, var1505=org.apache.poi.openxml4j.opc.OPCPackage, var3317=$r6, var709=org.apache.poi.xssf.usermodel.XSSFRelation, var1856=$r4, var3849=org.apache.poi.ooxml.POIXMLRelation, var3051=$r5, var3690=java.util.ArrayList, var574=$r7, var2411=$i0, var3951=i2, var3539=z4, var483=$r8, var701=org.apache.poi.xssf.usermodel.XSSFWorkbook, var2629=$r9, var3430=org.apache.poi.xssf.usermodel.XSSFFactory, var2512=$r10, var2993=org.apache.poi.ooxml.POIXMLDocumentPart$RelationPart, var1618=org.apache.poi.ooxml.POIXMLFactory, var2214=r40, var3243=$r11, var1770=org.apache.poi.xssf.usermodel.XSSFTable, var1941=r41, var2603=org.apache.poi.openxml4j.opc.PackageRelationship, var292=$r12, var3284=$r13, var3821=org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTable, var3605=$r14, var3245=$l1, var983=java.util.SortedMap, var1653=$r15, var3583=$r16, var3078=java.util.Map, var1367=java.lang.Object, var1753=$z1, var2693=$r18, var1509=$r19, var1703=$r20, var3017=r42, var1891=$r21, var1327=$r22, var2118=$r23, var1280=org.apache.poi.xssf.usermodel.XSSFName, var2323=$r24}
; {org.apache.poi.xssf.usermodel.XSSFSheet=var3103, r0=var2475, org.apache.poi.ss.util.AreaReference=var1976, r17=var2097, org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet=var2460, $r1=var2248, $z0=var2400, $r2=var3120, org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTableParts=var2071, $r35=var438, org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTablePart=var3043, $r36=var203, org.apache.poi.openxml4j.opc.PackagePart=var858, org.apache.poi.ooxml.POIXMLDocumentPart=var995, $r3=var3687, org.apache.poi.openxml4j.opc.OPCPackage=var1505, $r6=var3317, org.apache.poi.xssf.usermodel.XSSFRelation=var709, $r4=var1856, org.apache.poi.ooxml.POIXMLRelation=var3849, $r5=var3051, java.util.ArrayList=var3690, $r7=var574, $i0=var2411, i2=var3951, z4=var3539, $r8=var483, org.apache.poi.xssf.usermodel.XSSFWorkbook=var701, $r9=var2629, org.apache.poi.xssf.usermodel.XSSFFactory=var3430, $r10=var2512, org.apache.poi.ooxml.POIXMLDocumentPart$RelationPart=var2993, org.apache.poi.ooxml.POIXMLFactory=var1618, r40=var2214, $r11=var3243, org.apache.poi.xssf.usermodel.XSSFTable=var1770, r41=var1941, org.apache.poi.openxml4j.opc.PackageRelationship=var2603, $r12=var292, $r13=var3284, org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTable=var3821, $r14=var3605, $l1=var3245, java.util.SortedMap=var983, $r15=var1653, $r16=var3583, java.util.Map=var3078, java.lang.Object=var1367, $z1=var1753, $r18=var2693, $r19=var1509, $r20=var1703, r42=var3017, $r21=var1891, $r22=var1327, $r23=var2118, org.apache.poi.xssf.usermodel.XSSFName=var1280, $r24=var2323}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(int)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(int)>": 1,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r0 := @this: org.apache.poi.xssf.usermodel.XSSFSheet;	r17 := @parameter0: org.apache.poi.ss.util.AreaReference;	$r1 = r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet worksheet>;	$z0 = interfaceinvoke $r1.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet: boolean isSetTableParts()>();	if $z0 != 0 goto $r2 = r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet worksheet>;	$r2 = r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet worksheet>;	$r35 = interfaceinvoke $r2.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTWorksheet: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTableParts getTableParts()>();	$r36 = interfaceinvoke $r35.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTableParts: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTablePart addNewTablePart()>();	$r3 = virtualinvoke r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.apache.poi.openxml4j.opc.PackagePart getPackagePart()>();	$r6 = virtualinvoke $r3.<org.apache.poi.openxml4j.opc.PackagePart: org.apache.poi.openxml4j.opc.OPCPackage getPackage()>();	$r4 = <org.apache.poi.xssf.usermodel.XSSFRelation: org.apache.poi.xssf.usermodel.XSSFRelation TABLE>;	$r5 = virtualinvoke $r4.<org.apache.poi.xssf.usermodel.XSSFRelation: java.lang.String getContentType()>();	$r7 = virtualinvoke $r6.<org.apache.poi.openxml4j.opc.OPCPackage: java.util.ArrayList getPartsByContentType(java.lang.String)>($r5);	$i0 = virtualinvoke $r7.<java.util.ArrayList: int size()>();	i2 = $i0 + 1;	z4 = 1;	if z4 == 0 goto $r8 = <org.apache.poi.xssf.usermodel.XSSFRelation: org.apache.poi.xssf.usermodel.XSSFRelation TABLE>;	$r8 = <org.apache.poi.xssf.usermodel.XSSFRelation: org.apache.poi.xssf.usermodel.XSSFRelation TABLE>;	$r9 = virtualinvoke r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.apache.poi.xssf.usermodel.XSSFWorkbook getWorkbook()>();	$r10 = virtualinvoke $r9.<org.apache.poi.xssf.usermodel.XSSFWorkbook: org.apache.poi.xssf.usermodel.XSSFFactory getXssfFactory()>();	r40 = virtualinvoke r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.apache.poi.ooxml.POIXMLDocumentPart$RelationPart createRelationship(org.apache.poi.ooxml.POIXMLRelation,org.apache.poi.ooxml.POIXMLFactory,int,boolean)>($r8, $r10, i2, 0);	$r11 = virtualinvoke r40.<org.apache.poi.ooxml.POIXMLDocumentPart$RelationPart: org.apache.poi.ooxml.POIXMLDocumentPart getDocumentPart()>();	r41 = (org.apache.poi.xssf.usermodel.XSSFTable) $r11;	$r12 = virtualinvoke r40.<org.apache.poi.ooxml.POIXMLDocumentPart$RelationPart: org.apache.poi.openxml4j.opc.PackageRelationship getRelationship()>();	$r13 = virtualinvoke $r12.<org.apache.poi.openxml4j.opc.PackageRelationship: java.lang.String getId()>();	interfaceinvoke $r36.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTablePart: void setId(java.lang.String)>($r13);	$r14 = virtualinvoke r41.<org.apache.poi.xssf.usermodel.XSSFTable: org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTable getCTTable()>();	$l1 = (long) i2;	interfaceinvoke $r14.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTable: void setId(long)>($l1);	$r15 = r0.<org.apache.poi.xssf.usermodel.XSSFSheet: java.util.SortedMap tables>;	$r16 = interfaceinvoke $r36.<org.openxmlformats.schemas.spreadsheetml.x2006.main.CTTablePart: java.lang.String getId()>();	interfaceinvoke $r15.<java.util.SortedMap: java.lang.Object put(java.lang.Object,java.lang.Object)>($r16, r41);	if r17 == null goto (branch);	$z1 = virtualinvoke r41.<org.apache.poi.xssf.usermodel.XSSFTable: boolean supportsAreaReference(org.apache.poi.ss.util.AreaReference)>(r17);	if $z1 == 0 goto (branch);	if i2 >= 2147483647 goto return r41;	$r18 = new java.lang.StringBuilder;	specialinvoke $r18.<java.lang.StringBuilder: void <init>()>();	$r19 = virtualinvoke $r18.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("Table");	$r20 = virtualinvoke $r19.<java.lang.StringBuilder: java.lang.StringBuilder append(int)>(i2);	r42 = virtualinvoke $r20.<java.lang.StringBuilder: java.lang.String toString()>();	$r21 = virtualinvoke r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.apache.poi.xssf.usermodel.XSSFWorkbook getWorkbook()>();	$r22 = virtualinvoke $r21.<org.apache.poi.xssf.usermodel.XSSFWorkbook: org.apache.poi.xssf.usermodel.XSSFTable getTable(java.lang.String)>(r42);	if $r22 != null goto i2 = i2 + 1;	$r23 = virtualinvoke r0.<org.apache.poi.xssf.usermodel.XSSFSheet: org.apache.poi.xssf.usermodel.XSSFWorkbook getWorkbook()>();	$r24 = virtualinvoke $r23.<org.apache.poi.xssf.usermodel.XSSFWorkbook: org.apache.poi.xssf.usermodel.XSSFName getName(java.lang.String)>(r42);	if $r24 != null goto i2 = i2 + 1;	virtualinvoke r41.<org.apache.poi.xssf.usermodel.XSSFTable: void setDisplayName(java.lang.String)>(r42);	virtualinvoke r41.<org.apache.poi.xssf.usermodel.XSSFTable: void setName(java.lang.String)>(r42);	goto [?= return r41];	return r41
;block_num 10