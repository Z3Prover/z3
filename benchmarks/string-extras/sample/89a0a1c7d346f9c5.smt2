; origin: https://github.com/iscas-projects/SCB : log4j/smt/method-org.apache.log4j.lf5.viewer.LogBrokerMonitor__closeAfterConfirm__1005200335/2729.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3174 0)
(declare-sort var2806 0)
(declare-sort var2313 0)
(declare-sort var634 0)
(declare-sort var2478 0)
(declare-sort var84 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun String-init () String)
(declare-fun <init>/-1430969082 (String) void)
(declare-fun _callSystemExitOnClose/-1291859940 (var3174) Bool)
(define-fun append/1560614132 ((s String) (tail String)) String (str.++ s tail))
(declare-fun _logMonitorFrame/-1291859940 (var3174) var2806)
(define-fun toString/-222306083 ((s String)) String s)
(declare-fun var2313_showConfirmDialog/676369074 (var634 var2478 String Int Int var84) Int)
(declare-fun cast-from-var2806-to-var634 (var2806) var634)
(declare-fun cast-from-String-to-var2478 (String) var2478)
(declare-const null-var3174 var3174)
(declare-const null-var84 var84)
(declare-const var104 var3174) ; Statement: r1 := @this: org.apache.log4j.lf5.viewer.LogBrokerMonitor 
(assert (not (= var104 null-var3174)))
(define-const var176 String String-init) ; Statement: $r0 = new java.lang.StringBuffer 
(assert true)
;(assert (<init>/-1430969082 var176)) ; Statement: specialinvoke $r0.<java.lang.StringBuffer: void <init>()>() 

(declare-const var176!1 String)
(define-const var3845 Bool (_callSystemExitOnClose/-1291859940 var104)) ; Statement: $z0 = r1.<org.apache.log4j.lf5.viewer.LogBrokerMonitor: boolean _callSystemExitOnClose> 
 ; Statement: if $z0 != 0 goto virtualinvoke $r0.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("Are you sure you want to exit?\n") 
(assert (not (not (= (ite var3845 1 0) 0)))) ; Negate: Cond: $z0 != 0  
(assert true)
;(assert (append/1560614132 var176!1 "Are you sure you want to close the logging ")) ; Statement: virtualinvoke $r0.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("Are you sure you want to close the logging ") 
(declare-const var176!2 String)
(assert (str.prefixof var176!1 var176!2))
(assert true)
;(assert (append/1560614132 var176!2 "console?\n")) ; Statement: virtualinvoke $r0.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("console?\n") 
(declare-const var176!3 String)
(assert (str.prefixof var176!2 var176!3))
(assert true)
;(assert (append/1560614132 var176!3 "(Note: This will not shut down the Virtual Machine,\n")) ; Statement: virtualinvoke $r0.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("(Note: This will not shut down the Virtual Machine,\n") 
(declare-const var176!4 String)
(assert (str.prefixof var176!3 var176!4))
(assert true)
;(assert (append/1560614132 var176!4 "or the Swing event thread.)")) ; Statement: virtualinvoke $r0.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("or the Swing event thread.)") 
(declare-const var176!5 String)
(assert (str.prefixof var176!4 var176!5))
 ; Statement: goto [?= r4 = "Are you sure you want to dispose of the Logging Console?"] 
(assert true) ; Non Conditional
(define-const var2401 String "Are you sure you want to dispose of the Logging Console?") ; Statement: r4 = "Are you sure you want to dispose of the Logging Console?" 
(define-const var2991 Bool (_callSystemExitOnClose/-1291859940 var104)) ; Statement: $z1 = r1.<org.apache.log4j.lf5.viewer.LogBrokerMonitor: boolean _callSystemExitOnClose> 
 ; Statement: if $z1 != 1 goto $r2 = r1.<org.apache.log4j.lf5.viewer.LogBrokerMonitor: javax.swing.JFrame _logMonitorFrame> 
(assert (not (not (= (ite var2991 1 0) 1)))) ; Negate: Cond: $z1 != 1  
(define-const var2401!1 String "Are you sure you want to exit?") ; Statement: r4 = "Are you sure you want to exit?" 
(assert true) ; Non Conditional
(define-const var196 var2806 (_logMonitorFrame/-1291859940 var104)) ; Statement: $r2 = r1.<org.apache.log4j.lf5.viewer.LogBrokerMonitor: javax.swing.JFrame _logMonitorFrame> 
(assert true)
(define-const var597 String (toString/-222306083 var176!5)) ; Statement: $r3 = virtualinvoke $r0.<java.lang.StringBuffer: java.lang.String toString()>() 
(define-const var955 Int (var2313_showConfirmDialog/676369074 (cast-from-var2806-to-var634 var196) (cast-from-String-to-var2478 var597) var2401!1 2 3 null-var84)) ; Statement: $i0 = staticinvoke <javax.swing.JOptionPane: int showConfirmDialog(java.awt.Component,java.lang.Object,java.lang.String,int,int,javax.swing.Icon)>($r2, $r3, r4, 2, 3, null) 
 ; Statement: if $i0 != 0 goto return 
(assert (not (= var955 0))) ; Cond: $i0 != 0 
 ; Statement: return 
(check-sat)


; {String-init=([], java.lang.StringBuffer), <init>/-1430969082=([java.lang.StringBuffer], void), _callSystemExitOnClose/-1291859940=([org.apache.log4j.lf5.viewer.LogBrokerMonitor], boolean), append/1560614132=([java.lang.StringBuffer, java.lang.String], java.lang.StringBuffer), _logMonitorFrame/-1291859940=([org.apache.log4j.lf5.viewer.LogBrokerMonitor], javax.swing.JFrame), toString/-222306083=([java.lang.StringBuffer], java.lang.String), var2313_showConfirmDialog/676369074=([java.awt.Component, java.lang.Object, java.lang.String, int, int, javax.swing.Icon], int), cast-from-var2806-to-var634=([javax.swing.JFrame], java.awt.Component), cast-from-String-to-var2478=([java.lang.String], java.lang.Object)}
; {var3174=org.apache.log4j.lf5.viewer.LogBrokerMonitor, var104=r1, var176=$r0, var3845=$z0, var2401=r4, var2991=$z1, var2806=javax.swing.JFrame, var196=$r2, var597=$r3, var2313=javax.swing.JOptionPane, var634=java.awt.Component, var2478=java.lang.Object, var84=javax.swing.Icon, var955=$i0}
; {org.apache.log4j.lf5.viewer.LogBrokerMonitor=var3174, r1=var104, $r0=var176, $z0=var3845, r4=var2401, $z1=var2991, javax.swing.JFrame=var2806, $r2=var196, $r3=var597, javax.swing.JOptionPane=var2313, java.awt.Component=var634, java.lang.Object=var2478, javax.swing.Icon=var84, $i0=var955}
;seq <java.lang.StringBuffer: void <init>()>;	<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>;	<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>;	<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>;	<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>;	<java.lang.StringBuffer: java.lang.String toString()>
;cnt {"<java.lang.StringBuffer: void <init>()>": 1,"<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>": 4,"<java.lang.StringBuffer: java.lang.String toString()>": 1}
;stmts r1 := @this: org.apache.log4j.lf5.viewer.LogBrokerMonitor;	$r0 = new java.lang.StringBuffer;	specialinvoke $r0.<java.lang.StringBuffer: void <init>()>();	$z0 = r1.<org.apache.log4j.lf5.viewer.LogBrokerMonitor: boolean _callSystemExitOnClose>;	if $z0 != 0 goto virtualinvoke $r0.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("Are you sure you want to exit?\n");	virtualinvoke $r0.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("Are you sure you want to close the logging ");	virtualinvoke $r0.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("console?\n");	virtualinvoke $r0.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("(Note: This will not shut down the Virtual Machine,\n");	virtualinvoke $r0.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>("or the Swing event thread.)");	goto [?= r4 = "Are you sure you want to dispose of the Logging Console?"];	r4 = "Are you sure you want to dispose of the Logging Console?";	$z1 = r1.<org.apache.log4j.lf5.viewer.LogBrokerMonitor: boolean _callSystemExitOnClose>;	if $z1 != 1 goto $r2 = r1.<org.apache.log4j.lf5.viewer.LogBrokerMonitor: javax.swing.JFrame _logMonitorFrame>;	r4 = "Are you sure you want to exit?";	$r2 = r1.<org.apache.log4j.lf5.viewer.LogBrokerMonitor: javax.swing.JFrame _logMonitorFrame>;	$r3 = virtualinvoke $r0.<java.lang.StringBuffer: java.lang.String toString()>();	$i0 = staticinvoke <javax.swing.JOptionPane: int showConfirmDialog(java.awt.Component,java.lang.Object,java.lang.String,int,int,javax.swing.Icon)>($r2, $r3, r4, 2, 3, null);	if $i0 != 0 goto return;	return
;block_num 6