
; Copyright (c) 2015 Microsoft Corporation
; tokeneer3a/enclave/startadminactivity/adminopcanstart 1 
(set-option :print-success false )
(set-option :produce-unsat-cores true )
(set-logic AUFNIRA)
(declare-sort admin__t 0)
(declare-sort admintoken__statetype 0)
(define-sort statust () Int )
(declare-fun admintoken__state () admintoken__statetype )
(declare-fun admintoken__state___init ()
  admintoken__statetype
)
(declare-fun admintoken__state___loopinit ()
  admintoken__statetype
)
(declare-fun enclavequiescent () statust )
(declare-fun gotadmintoken () statust )
(declare-fun notenrolled () statust )
(declare-fun shutdown () statust )
(declare-fun status () statust )
(declare-fun status___init () statust )
(declare-fun status___loopinit () statust )
(declare-fun statust__base__first () statust )
(declare-fun statust__base__last () statust )
(declare-fun statust__first () statust )
(declare-fun statust__last () statust )
(declare-fun statust__size () Int )
(declare-fun theadmin () admin__t )
(declare-fun theadmin___init () admin__t )
(declare-fun theadmin___loopinit () admin__t )
(declare-fun waitingendenrol () statust )
(declare-fun waitingenrol () statust )
(declare-fun waitingfinishadminop () statust )
(declare-fun waitingremoveadmintokenfail () statust )
(declare-fun waitingstartadminop () statust )
(declare-fun admin__ispresent ( admin__t ) Bool )
(declare-fun admintoken__ispresent
  ( admintoken__statetype )
  Bool
)
(declare-fun bit__and ( Int Int ) Int )
(declare-fun bit__not ( Int Int ) Int )
(declare-fun bit__or ( Int Int ) Int )
(declare-fun bit__xor ( Int Int ) Int )
(declare-fun boolean__pos ( Bool ) Int )
(declare-fun boolean__val ( Int ) Bool )
(declare-fun character__pos ( Int ) Int )
(declare-fun character__val ( Int ) Int )
(declare-fun int___abs ( Int ) Int )
(declare-fun int___div ( Int Int ) Int )
(declare-fun int___exp ( Int Int ) Int )
(declare-fun int___mod ( Int Int ) Int )
(declare-fun int___odd ( Int ) Bool )
(declare-fun int___rem ( Int Int ) Int )
(declare-fun int___times ( Int Int ) Int )
(declare-fun int___to_real ( Int ) Real )
(declare-fun real___abs ( Real ) Real )
(declare-fun real___div ( Real Real ) Real )
(declare-fun real___exp ( Real Int ) Real )
(declare-fun real___minus ( Real Real ) Real )
(declare-fun real___plus ( Real Real ) Real )
(declare-fun real___times ( Real Real ) Real )
(declare-fun real___uminus ( Real ) Real )
(declare-fun round__ ( Real ) Int )
(declare-fun statust__LE ( statust statust ) Bool )
(declare-fun statust__LT ( statust statust ) Bool )
(declare-fun statust___member ( statust ) Bool )
(declare-fun statust__pos ( statust ) Int )
(declare-fun statust__pred ( statust ) statust )
(declare-fun statust__succ ( statust ) statust )
(declare-fun statust__val ( Int ) statust )
(assert
  (! (<= 0 statust__size ) :named adminopcanst_rules<1> )
)
(assert
  (!
    (= statust__first notenrolled )
    :named adminopcanst_rules<2>
  )
)
(assert
  (!
    (= statust__last shutdown )
    :named adminopcanst_rules<3>
  )
)
(assert
  (!
    (= statust__base__first notenrolled )
    :named adminopcanst_rules<4>
  )
)
(assert
  (!
    (= statust__base__last shutdown )
    :named adminopcanst_rules<5>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (< 0 Y ) (<= 0 (int___mod X Y ) ) )
    )
    :named divmod<1>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (< 0 Y ) (< (int___mod X Y ) Y ) )
    )
    :named divmod<2>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (< Y 0 ) (<= (int___mod X Y ) 0 ) )
    )
    :named divmod<3>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (< Y 0 ) (< Y (int___mod X Y ) ) )
    )
    :named divmod<4>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (< 0 Y ) )
        (< (- X Y ) (* Y (int___div X Y ) ) )
      )
    )
    :named divmod<5>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (< 0 Y ) )
        (<= (* Y (int___div X Y ) ) X )
      )
    )
    :named divmod<6>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= X 0 ) (< 0 Y ) )
        (<= X (* Y (int___div X Y ) ) )
      )
    )
    :named divmod<7>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= X 0 ) (< 0 Y ) )
        (< (* Y (int___div X Y ) ) (+ X Y ) )
      )
    )
    :named divmod<8>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (< Y 0 ) )
        (<= (* Y (int___div X Y ) ) X )
      )
    )
    :named divmod<9>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (< Y 0 ) )
        (< (+ X Y ) (* Y (int___div X Y ) ) )
      )
    )
    :named divmod<10>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= X 0 ) (< Y 0 ) )
        (< (* Y (int___div X Y ) ) (- X Y ) )
      )
    )
    :named divmod<11>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= X 0 ) (< Y 0 ) )
        (<= X (* Y (int___div X Y ) ) )
      )
    )
    :named divmod<12>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (= (+ (* Y (int___div X Y ) ) (int___rem X Y ) ) X )
    )
    :named divmod<13>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (= (int___rem X Y ) 0 ) (= (int___mod X Y ) 0 ) )
    )
    :named divmod<14>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (< 0 Y ) )
        (= (int___mod X Y ) (int___rem X Y ) )
      )
    )
    :named divmod<15>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= X 0 ) (< 0 Y ) (not (= (int___rem X Y ) 0 ) ) )
        (= (int___mod X Y ) (+ (int___rem X Y ) Y ) )
      )
    )
    :named divmod<16>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (< Y 0 ) (not (= (int___rem X Y ) 0 ) ) )
        (= (int___mod X Y ) (+ (int___rem X Y ) Y ) )
      )
    )
    :named divmod<17>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= X 0 ) (< Y 0 ) )
        (= (int___mod X Y ) (int___rem X Y ) )
      )
    )
    :named divmod<18>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (and (<= 0 X ) (< X Y ) ) (= (int___mod X Y ) X ) )
    )
    :named divmod<20>
  )
)
(assert
  (!
    (forall
      ( (X Int ) )
      (=> (<= 0 X ) (= (bit__and X X ) X ) )
    )
    :named bitwise<1>
  )
)
(assert
  (!
    (forall ( (X Int ) ) (=> (<= 0 X ) (= (bit__or X X ) X ) ) )
    :named bitwise<2>
  )
)
(assert
  (!
    (forall
      ( (X Int ) )
      (=> (<= 0 X ) (= (bit__xor X X ) 0 ) )
    )
    :named bitwise<3>
  )
)
(assert
  (!
    (forall
      ( (X Int ) )
      (=> (<= 0 X ) (= (bit__and X 0 ) 0 ) )
    )
    :named bitwise<11>
  )
)
(assert
  (!
    (forall ( (X Int ) ) (=> (<= 0 X ) (= (bit__or X 0 ) X ) ) )
    :named bitwise<12>
  )
)
(assert
  (!
    (forall
      ( (X Int ) )
      (=> (<= 0 X ) (= (bit__xor X 0 ) X ) )
    )
    :named bitwise<13>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (and (<= 0 X ) (<= 0 Y ) ) (<= 0 (bit__and X Y ) ) )
    )
    :named bitwise<51>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (and (<= 0 X ) (<= 0 Y ) ) (<= 0 (bit__or X Y ) ) )
    )
    :named bitwise<52>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (and (<= 0 X ) (<= 0 Y ) ) (<= 0 (bit__xor X Y ) ) )
    )
    :named bitwise<53>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (and (<= 0 X ) (<= 0 Y ) ) (<= X (bit__or X Y ) ) )
    )
    :named bitwise<54>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (and (<= 0 X ) (<= 0 Y ) ) (<= Y (bit__or X Y ) ) )
    )
    :named bitwise<55>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (<= 0 Y ) )
        (<= (- X Y ) (bit__xor X Y ) )
      )
    )
    :named bitwise<56>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (<= 0 Y ) )
        (<= (- Y X ) (bit__xor X Y ) )
      )
    )
    :named bitwise<57>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (and (<= 0 X ) (<= 0 Y ) ) (<= (bit__and X Y ) X ) )
    )
    :named bitwise<61>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=> (and (<= 0 X ) (<= 0 Y ) ) (<= (bit__and X Y ) Y ) )
    )
    :named bitwise<62>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (<= 0 Y ) )
        (<= (bit__or X Y ) (+ X Y ) )
      )
    )
    :named bitwise<63>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (<= 0 Y ) )
        (<= (bit__xor X Y ) (+ X Y ) )
      )
    )
    :named bitwise<64>
  )
)
(assert
  (!
    (forall
      ( (N Int ) (X Int ) (Y Int ) )
      (=>
        (and
          (<= 0 X )
          (<= 0 Y )
          (<= 0 N )
          (<= X (- (int___exp 2 N ) 1 ) )
          (<= Y (- (int___exp 2 N ) 1 ) )
        )
        (<= (bit__or X Y ) (- (int___exp 2 N ) 1 ) )
      )
    )
    :named bitwise<66>
  )
)
(assert
  (!
    (forall
      ( (N Int ) (X Int ) (Y Int ) )
      (=>
        (and
          (<= 0 X )
          (<= 0 Y )
          (<= 0 N )
          (<= X (- (int___exp 2 N ) 1 ) )
          (<= Y (- (int___exp 2 N ) 1 ) )
        )
        (<= (bit__xor X Y ) (- (int___exp 2 N ) 1 ) )
      )
    )
    :named bitwise<67>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (<= 0 Y ) )
        (<= (bit__and X Y ) (bit__or X Y ) )
      )
    )
    :named bitwise<81>
  )
)
(assert
  (!
    (forall
      ( (X Int ) (Y Int ) )
      (=>
        (and (<= 0 X ) (<= 0 Y ) )
        (<= (bit__xor X Y ) (bit__or X Y ) )
      )
    )
    :named bitwise<82>
  )
)
(assert
  (!
    (forall ( (X Int ) ) (=> (<= 0 X ) (= (int___abs X ) X ) ) )
    :named arith<10>
  )
)
(assert
  (!
    (forall
      ( (X Int ) )
      (=> (< X 0 ) (= (int___abs X ) (- X ) ) )
    )
    :named arith<11>
  )
)
(assert
  (!
    (forall
      ( (U Real ) )
      (=> (<= (to_real 0 ) U ) (= (real___abs U ) U ) )
    )
    :named arith<12>
  )
)
(assert
  (!
    (forall
      ( (U Real ) )
      (=> (< U (to_real 0 ) ) (= (real___abs U ) (- U ) ) )
    )
    :named arith<13>
  )
)
(assert
  (!
    (forall
      ( (X Int ) )
      (= (int___odd X ) (= (int___mod (int___abs X ) 2 ) 1 ) )
    )
    :named arith<20>
  )
)
(assert
  (!
    (forall
      ( (i statust ) )
      (=> (statust___member i ) (= (statust__pos i ) i ) )
    )
    :named enum-int-pos-id-<statust>
  )
)
(assert
  (!
    (forall
      ( (i statust ) )
      (=> (statust___member i ) (= (statust__val i ) i ) )
    )
    :named enum-int-val-id-<statust>
  )
)
(assert
  (!
    (forall
      ( (i statust ) )
      (=>
        (statust___member i )
        (=> (< i 8 ) (= (statust__succ i ) (+ i 1 ) ) )
      )
    )
    :named enum-int-succ-<statust>
  )
)
(assert
  (!
    (forall
      ( (i statust ) )
      (=>
        (statust___member i )
        (=> (< 0 i ) (= (statust__pred i ) (- i 1 ) ) )
      )
    )
    :named enum-int-pred-<statust>
  )
)
(assert
  (! (= notenrolled 0 ) :named enum-int-const-<notenrolled> )
)
(assert
  (!
    (= waitingenrol 1 )
    :named enum-int-const-<waitingenrol>
  )
)
(assert
  (!
    (= waitingendenrol 2 )
    :named enum-int-const-<waitingendenrol>
  )
)
(assert
  (!
    (= enclavequiescent 3 )
    :named enum-int-const-<enclavequiescent>
  )
)
(assert
  (!
    (= waitingremoveadmintokenfail 4 )
    :named enum-int-const-<waitingremoveadmintokenfail>
  )
)
(assert
  (!
    (= gotadmintoken 5 )
    :named enum-int-const-<gotadmintoken>
  )
)
(assert
  (!
    (= waitingstartadminop 6 )
    :named enum-int-const-<waitingstartadminop>
  )
)
(assert
  (!
    (= waitingfinishadminop 7 )
    :named enum-int-const-<waitingfinishadminop>
  )
)
(assert
  (! (= shutdown 8 ) :named enum-int-const-<shutdown> )
)
(assert
  (!
    (statust___member enclavequiescent )
    :named typeref-mem-const-<enclavequiescent>
  )
)
(assert
  (!
    (statust___member gotadmintoken )
    :named typeref-mem-const-<gotadmintoken>
  )
)
(assert
  (!
    (statust___member notenrolled )
    :named typeref-mem-const-<notenrolled>
  )
)
(assert
  (!
    (statust___member shutdown )
    :named typeref-mem-const-<shutdown>
  )
)
(assert
  (!
    (statust___member status )
    :named typeref-mem-const-<status>
  )
)
(assert
  (!
    (statust___member status___init )
    :named typeref-mem-const-<status___init>
  )
)
(assert
  (!
    (statust___member status___loopinit )
    :named typeref-mem-const-<status___loopinit>
  )
)
(assert
  (!
    (statust___member statust__base__first )
    :named typeref-mem-const-<statust__base__first>
  )
)
(assert
  (!
    (statust___member statust__base__last )
    :named typeref-mem-const-<statust__base__last>
  )
)
(assert
  (!
    (statust___member statust__first )
    :named typeref-mem-const-<statust__first>
  )
)
(assert
  (!
    (statust___member statust__last )
    :named typeref-mem-const-<statust__last>
  )
)
(assert
  (!
    (statust___member waitingendenrol )
    :named typeref-mem-const-<waitingendenrol>
  )
)
(assert
  (!
    (statust___member waitingenrol )
    :named typeref-mem-const-<waitingenrol>
  )
)
(assert
  (!
    (statust___member waitingfinishadminop )
    :named typeref-mem-const-<waitingfinishadminop>
  )
)
(assert
  (!
    (statust___member waitingremoveadmintokenfail )
    :named typeref-mem-const-<waitingremoveadmintokenfail>
  )
)
(assert
  (!
    (statust___member waitingstartadminop )
    :named typeref-mem-const-<waitingstartadminop>
  )
)
(assert
  (!
    (forall
      ( (x0 statust ) )
      (=>
        (statust___member x0 )
        (statust___member (statust__pred x0 ) )
      )
    )
    :named typeref-mem-fun-<statust__pred>
  )
)
(assert
  (!
    (forall
      ( (x0 statust ) )
      (=>
        (statust___member x0 )
        (statust___member (statust__succ x0 ) )
      )
    )
    :named typeref-mem-fun-<statust__succ>
  )
)
(assert
  (!
    (forall
      ( (x0 Int ) )
      (statust___member (statust__val x0 ) )
    )
    :named typeref-mem-fun-<statust__val>
  )
)
(assert
  (!
    (forall
      ( (x statust ) )
      (= (statust___member x ) (and (<= 0 x ) (<= x 8 ) ) )
    )
    :named typeref-mem-def-<statust>
  )
)
(assert (! (= (int___exp 2 1 ) 2 ) :named iexp-eval-2-1 ) )
(assert (! (= (int___exp 2 2 ) 4 ) :named iexp-eval-2-2 ) )
(assert (! (= (int___exp 2 3 ) 8 ) :named iexp-eval-2-3 ) )
(assert (! true :named H1 ) )
(assert (! (<= statust__first status ) :named H2 ) )
(assert (! (<= status statust__last ) :named H3 ) )
(assert (! true :named H4 ) )
(assert (! true :named H5 ) )
(assert
  (!
    (not
      (and
        (=>
          (and
            (admin__ispresent theadmin )
            (and
              (= status enclavequiescent )
              (admintoken__ispresent admintoken__state )
            )
          )
          (= status enclavequiescent )
        )
        (=>
          (and
            (admin__ispresent theadmin )
            (and
              (= status enclavequiescent )
              (admintoken__ispresent admintoken__state )
            )
          )
          (admin__ispresent theadmin )
        )
      )
    )
    :named C
  )
)
(check-sat)
(get-unsat-core)
