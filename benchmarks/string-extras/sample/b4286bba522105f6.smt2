; origin: https://github.com/iscas-projects/SCB : handlebars/smt/method-com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator__reportAmbiguity__-2027161227/3568.smt2
(set-option :produce-unsat-cores true) ; enable generation of unsat cores
(set-option :produce-models true) ; enable model generation
(set-logic ALL)
(declare-sort var3449 0)
(declare-sort var1258 0)
(declare-sort var2911 0)
(declare-sort var2755 0)
(declare-sort var3999 0)
(declare-sort var1444 0)
(declare-sort var1939 0)
(declare-sort var2633 0)
(declare-sort var12 0)
(declare-sort var1680 0)
(declare-sort var2126 0)
(declare-sort var1737 0)
(declare-sort var3345 0)
(declare-sort void 0)
(declare-sort Iterator 0)
(declare-sort ClassObject 0)
(declare-fun var1444_of/1114852800 (Int Int) var1444)
(declare-fun String-init () String)
(define-fun <init>/1968657023 () String "")
(define-fun append/672562846 ((s String) (tail String)) String (str.++ s tail))
(declare-fun append/-1031950772 (String var12) String)
(declare-fun cast-from-var2755-to-var12 (var2755) var12)
(declare-fun cast-from-var3999-to-var12 (var3999) var12)
(declare-fun parser/310440123 (var3449) var1680)
(declare-fun getTokenStream/1024418418 (var1680) var2126)
(declare-fun var2126_getText/1244185151 (var2126 var1444) String)
(define-fun toString/-2075883882 ((s String)) String s)
(declare-fun println/1773605060 (var1939 String) void)
(declare-fun getErrorListenerDispatch/1243680242 (var3345) var1737)
(declare-fun cast-from-var1680-to-var3345 (var1680) var3345)
(declare-fun var1737_reportAmbiguity/-381263513 (var1737 var1680 var1258 Int Int Bool var2755 var3999) void)
(declare-const null-var3449 var3449)
(declare-const null-var1258 var1258)
(declare-const null-var2911 var2911)
(declare-const null-Int Int)
(declare-const null-Bool Bool)
(declare-const null-var2755 var2755)
(declare-const null-var3999 var3999)
(declare-const var3449-debug Bool)
(declare-const var3449-retry_debug Bool)
(declare-const var2633-out var1939)
(declare-const null-var1680 var1680)
(declare-const var3849 var3449) ; Statement: r8 := @this: com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator 
(assert (not (= var3849 null-var3449)))
(declare-const var1568 var1258) ; Statement: r16 := @parameter0: com.github.jknack.handlebars.internal.antlr.dfa.DFA 
(assert (not (= var1568 null-var1258)))
(declare-const var983 var2911) ; Statement: r20 := @parameter1: com.github.jknack.handlebars.internal.antlr.dfa.DFAState 
(assert (not (= var983 null-var2911)))
(declare-const var1437 Int) ; Statement: i0 := @parameter2: int 
(assert (not (= var1437 null-Int)))
(declare-const var3211 Int) ; Statement: i1 := @parameter3: int 
(assert (not (= var3211 null-Int)))
(declare-const var882 Bool) ; Statement: z1 := @parameter4: boolean 
(assert (not (= var882 null-Bool)))
(declare-const var536 var2755) ; Statement: r2 := @parameter5: java.util.BitSet 
(assert (not (= var536 null-var2755)))
(declare-const var1949 var3999) ; Statement: r5 := @parameter6: com.github.jknack.handlebars.internal.antlr.atn.ATNConfigSet 
(assert (not (= var1949 null-var3999)))
(define-const var1927 Bool var3449-debug) ; Statement: $z0 = <com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: boolean debug> 
 ; Statement: if $z0 != 0 goto $r19 = staticinvoke <com.github.jknack.handlebars.internal.antlr.misc.Interval: com.github.jknack.handlebars.internal.antlr.misc.Interval of(int,int)>(i0, i1) 
(assert (not (not (= (ite var1927 1 0) 0)))) ; Negate: Cond: $z0 != 0  
(define-const var1347 Bool var3449-retry_debug) ; Statement: $z2 = <com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: boolean retry_debug> 
 ; Statement: if $z2 == 0 goto $r21 = r8.<com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: com.github.jknack.handlebars.internal.antlr.Parser parser> 
(assert (not (= (ite var1347 1 0) 0))) ; Negate: Cond: $z2 == 0  
(define-const var1513 var1444 (var1444_of/1114852800 var1437 var3211)) ; Statement: $r19 = staticinvoke <com.github.jknack.handlebars.internal.antlr.misc.Interval: com.github.jknack.handlebars.internal.antlr.misc.Interval of(int,int)>(i0, i1) 
(define-const var848 var1939 var2633-out) ; Statement: $r1 = <java.lang.System: java.io.PrintStream out> 
(define-const var3680 String String-init) ; Statement: $r0 = new java.lang.StringBuilder 
(assert true)
;(assert (<init>/1968657023 var3680)) ; Statement: specialinvoke $r0.<java.lang.StringBuilder: void <init>()>() 
(declare-const var3680!1 String)
(assert (= var3680!1 ""))
(assert true)
(define-const var1969 String (append/672562846 var3680!1 "reportAmbiguity ")) ; Statement: $r3 = virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("reportAmbiguity ") 
(declare-const var3680!2 String)
(assert (= var3680!2 (str.++ var3680!1 "reportAmbiguity ")))
(assert true)
(define-const var2000 String (append/-1031950772 var1969 (cast-from-var2755-to-var12 var536))) ; Statement: $r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r2) 
(declare-const var1969!1 String)
(assert (str.prefixof var1969 var1969!1))
(assert true)
(define-const var1673 String (append/672562846 var2000 ":")) ; Statement: $r6 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(":") 
(declare-const var2000!1 String)
(assert (= var2000!1 (str.++ var2000 ":")))
(assert true)
(define-const var1233 String (append/-1031950772 var1673 (cast-from-var3999-to-var12 var1949))) ; Statement: $r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r5) 
(declare-const var1673!1 String)
(assert (str.prefixof var1673 var1673!1))
(assert true)
(define-const var32 String (append/672562846 var1233 ", input=")) ; Statement: $r12 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", input=") 
(declare-const var1233!1 String)
(assert (= var1233!1 (str.++ var1233 ", input=")))
(define-const var2656 var1680 (parser/310440123 var3849)) ; Statement: $r9 = r8.<com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: com.github.jknack.handlebars.internal.antlr.Parser parser> 
(assert true)
(define-const var1322 var2126 (getTokenStream/1024418418 var2656)) ; Statement: $r10 = virtualinvoke $r9.<com.github.jknack.handlebars.internal.antlr.Parser: com.github.jknack.handlebars.internal.antlr.TokenStream getTokenStream()>() 
(define-const var45 String (var2126_getText/1244185151 var1322 var1513)) ; Statement: $r11 = interfaceinvoke $r10.<com.github.jknack.handlebars.internal.antlr.TokenStream: java.lang.String getText(com.github.jknack.handlebars.internal.antlr.misc.Interval)>($r19) 
(assert true)
(define-const var2934 String (append/672562846 var32 var45)) ; Statement: $r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r11) 
(declare-const var32!1 String)
(assert (= var32!1 (str.++ var32 var45)))
(assert true)
(define-const var77 String (toString/-2075883882 var2934)) ; Statement: $r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.String toString()>() 
(assert true)
;(assert (println/1773605060 var848 var77)) ; Statement: virtualinvoke $r1.<java.io.PrintStream: void println(java.lang.String)>($r14) 

(declare-const var848!1 var1939)
(declare-const var77!1 String)
(assert true) ; Non Conditional
(define-const var1420 var1680 (parser/310440123 var3849)) ; Statement: $r21 = r8.<com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: com.github.jknack.handlebars.internal.antlr.Parser parser> 
 ; Statement: if $r21 == null goto return 
(assert (not (= var1420 null-var1680))) ; Negate: Cond: $r21 == null  
(define-const var2331 var1680 (parser/310440123 var3849)) ; Statement: $r15 = r8.<com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: com.github.jknack.handlebars.internal.antlr.Parser parser> 
(assert true)
(define-const var621 var1737 (getErrorListenerDispatch/1243680242 (cast-from-var1680-to-var3345 var2331))) ; Statement: $r18 = virtualinvoke $r15.<com.github.jknack.handlebars.internal.antlr.Parser: com.github.jknack.handlebars.internal.antlr.ANTLRErrorListener getErrorListenerDispatch()>() 
(define-const var3707 var1680 (parser/310440123 var3849)) ; Statement: $r17 = r8.<com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: com.github.jknack.handlebars.internal.antlr.Parser parser> 
;(assert (var1737_reportAmbiguity/-381263513 var621 var3707 var1568 var1437 var3211 var882 var536 var1949)) ; Statement: interfaceinvoke $r18.<com.github.jknack.handlebars.internal.antlr.ANTLRErrorListener: void reportAmbiguity(com.github.jknack.handlebars.internal.antlr.Parser,com.github.jknack.handlebars.internal.antlr.dfa.DFA,int,int,boolean,java.util.BitSet,com.github.jknack.handlebars.internal.antlr.atn.ATNConfigSet)>($r17, r16, i0, i1, z1, r2, r5) 

(declare-const var621!1 var1737)
(declare-const var3707!1 var1680)
(declare-const var1568!1 var1258)
(declare-const var1437!1 Int)
(declare-const var3211!1 Int)
(declare-const var882!1 Bool)
(declare-const var536!1 var2755)
(declare-const var1949!1 var3999)
(assert true) ; Non Conditional
 ; Statement: return 
(check-sat)


; {var1444_of/1114852800=([int, int], com.github.jknack.handlebars.internal.antlr.misc.Interval), String-init=([], java.lang.StringBuilder), <init>/1968657023=([java.lang.StringBuilder], void), append/672562846=([java.lang.StringBuilder, java.lang.String], java.lang.StringBuilder), append/-1031950772=([java.lang.StringBuilder, java.lang.Object], java.lang.StringBuilder), cast-from-var2755-to-var12=([java.util.BitSet], java.lang.Object), cast-from-var3999-to-var12=([com.github.jknack.handlebars.internal.antlr.atn.ATNConfigSet], java.lang.Object), parser/310440123=([com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator], com.github.jknack.handlebars.internal.antlr.Parser), getTokenStream/1024418418=([com.github.jknack.handlebars.internal.antlr.Parser], com.github.jknack.handlebars.internal.antlr.TokenStream), var2126_getText/1244185151=([com.github.jknack.handlebars.internal.antlr.TokenStream, com.github.jknack.handlebars.internal.antlr.misc.Interval], java.lang.String), toString/-2075883882=([java.lang.StringBuilder], java.lang.String), println/1773605060=([java.io.PrintStream, java.lang.String], void), getErrorListenerDispatch/1243680242=([com.github.jknack.handlebars.internal.antlr.Recognizer], com.github.jknack.handlebars.internal.antlr.ANTLRErrorListener), cast-from-var1680-to-var3345=([com.github.jknack.handlebars.internal.antlr.Parser], com.github.jknack.handlebars.internal.antlr.Recognizer), var1737_reportAmbiguity/-381263513=([com.github.jknack.handlebars.internal.antlr.ANTLRErrorListener, com.github.jknack.handlebars.internal.antlr.Parser, com.github.jknack.handlebars.internal.antlr.dfa.DFA, int, int, boolean, java.util.BitSet, com.github.jknack.handlebars.internal.antlr.atn.ATNConfigSet], void)}
; {var3449=com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator, var3849=r8, var1258=com.github.jknack.handlebars.internal.antlr.dfa.DFA, var1568=r16, var2911=com.github.jknack.handlebars.internal.antlr.dfa.DFAState, var983=r20, var1437=i0, var3211=i1, var882=z1, var2755=java.util.BitSet, var536=r2, var3999=com.github.jknack.handlebars.internal.antlr.atn.ATNConfigSet, var1949=r5, var1927=$z0, var1347=$z2, var1444=com.github.jknack.handlebars.internal.antlr.misc.Interval, var1513=$r19, var1939=java.io.PrintStream, var2633=java.lang.System, var848=$r1, var3680=$r0, var1969=$r3, var12=java.lang.Object, var2000=$r4, var1673=$r6, var1233=$r7, var32=$r12, var1680=com.github.jknack.handlebars.internal.antlr.Parser, var2656=$r9, var2126=com.github.jknack.handlebars.internal.antlr.TokenStream, var1322=$r10, var45=$r11, var2934=$r13, var77=$r14, var1420=$r21, var2331=$r15, var1737=com.github.jknack.handlebars.internal.antlr.ANTLRErrorListener, var3345=com.github.jknack.handlebars.internal.antlr.Recognizer, var621=$r18, var3707=$r17}
; {com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator=var3449, r8=var3849, com.github.jknack.handlebars.internal.antlr.dfa.DFA=var1258, r16=var1568, com.github.jknack.handlebars.internal.antlr.dfa.DFAState=var2911, r20=var983, i0=var1437, i1=var3211, z1=var882, java.util.BitSet=var2755, r2=var536, com.github.jknack.handlebars.internal.antlr.atn.ATNConfigSet=var3999, r5=var1949, $z0=var1927, $z2=var1347, com.github.jknack.handlebars.internal.antlr.misc.Interval=var1444, $r19=var1513, java.io.PrintStream=var1939, java.lang.System=var2633, $r1=var848, $r0=var3680, $r3=var1969, java.lang.Object=var12, $r4=var2000, $r6=var1673, $r7=var1233, $r12=var32, com.github.jknack.handlebars.internal.antlr.Parser=var1680, $r9=var2656, com.github.jknack.handlebars.internal.antlr.TokenStream=var2126, $r10=var1322, $r11=var45, $r13=var2934, $r14=var77, $r21=var1420, $r15=var2331, com.github.jknack.handlebars.internal.antlr.ANTLRErrorListener=var1737, com.github.jknack.handlebars.internal.antlr.Recognizer=var3345, $r18=var621, $r17=var3707}
;seq <java.lang.StringBuilder: void <init>()>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>;	<java.lang.StringBuilder: java.lang.String toString()>
;cnt {"<java.lang.StringBuilder: void <init>()>": 1,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>": 4,"<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>": 2,"<java.lang.StringBuilder: java.lang.String toString()>": 1}
;stmts r8 := @this: com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator;	r16 := @parameter0: com.github.jknack.handlebars.internal.antlr.dfa.DFA;	r20 := @parameter1: com.github.jknack.handlebars.internal.antlr.dfa.DFAState;	i0 := @parameter2: int;	i1 := @parameter3: int;	z1 := @parameter4: boolean;	r2 := @parameter5: java.util.BitSet;	r5 := @parameter6: com.github.jknack.handlebars.internal.antlr.atn.ATNConfigSet;	$z0 = <com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: boolean debug>;	if $z0 != 0 goto $r19 = staticinvoke <com.github.jknack.handlebars.internal.antlr.misc.Interval: com.github.jknack.handlebars.internal.antlr.misc.Interval of(int,int)>(i0, i1);	$z2 = <com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: boolean retry_debug>;	if $z2 == 0 goto $r21 = r8.<com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: com.github.jknack.handlebars.internal.antlr.Parser parser>;	$r19 = staticinvoke <com.github.jknack.handlebars.internal.antlr.misc.Interval: com.github.jknack.handlebars.internal.antlr.misc.Interval of(int,int)>(i0, i1);	$r1 = <java.lang.System: java.io.PrintStream out>;	$r0 = new java.lang.StringBuilder;	specialinvoke $r0.<java.lang.StringBuilder: void <init>()>();	$r3 = virtualinvoke $r0.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>("reportAmbiguity ");	$r4 = virtualinvoke $r3.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r2);	$r6 = virtualinvoke $r4.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(":");	$r7 = virtualinvoke $r6.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.Object)>(r5);	$r12 = virtualinvoke $r7.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(", input=");	$r9 = r8.<com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: com.github.jknack.handlebars.internal.antlr.Parser parser>;	$r10 = virtualinvoke $r9.<com.github.jknack.handlebars.internal.antlr.Parser: com.github.jknack.handlebars.internal.antlr.TokenStream getTokenStream()>();	$r11 = interfaceinvoke $r10.<com.github.jknack.handlebars.internal.antlr.TokenStream: java.lang.String getText(com.github.jknack.handlebars.internal.antlr.misc.Interval)>($r19);	$r13 = virtualinvoke $r12.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>($r11);	$r14 = virtualinvoke $r13.<java.lang.StringBuilder: java.lang.String toString()>();	virtualinvoke $r1.<java.io.PrintStream: void println(java.lang.String)>($r14);	$r21 = r8.<com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: com.github.jknack.handlebars.internal.antlr.Parser parser>;	if $r21 == null goto return;	$r15 = r8.<com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: com.github.jknack.handlebars.internal.antlr.Parser parser>;	$r18 = virtualinvoke $r15.<com.github.jknack.handlebars.internal.antlr.Parser: com.github.jknack.handlebars.internal.antlr.ANTLRErrorListener getErrorListenerDispatch()>();	$r17 = r8.<com.github.jknack.handlebars.internal.antlr.atn.ParserATNSimulator: com.github.jknack.handlebars.internal.antlr.Parser parser>;	interfaceinvoke $r18.<com.github.jknack.handlebars.internal.antlr.ANTLRErrorListener: void reportAmbiguity(com.github.jknack.handlebars.internal.antlr.Parser,com.github.jknack.handlebars.internal.antlr.dfa.DFA,int,int,boolean,java.util.BitSet,com.github.jknack.handlebars.internal.antlr.atn.ATNConfigSet)>($r17, r16, i0, i1, z1, r2, r5);	return
;block_num 6