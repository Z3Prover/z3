(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sl/sl_filter.spl:35:3-4:An invariant might not be maintained by a loop in procedure filter
  tests/spl/sl/sl_filter.spl:18:14:Related location: This is the loop invariant that might not be maintained
  |)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun write$0 (FldLoc Loc Loc) FldLoc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_2$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_5$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun nondet_3$0 () Bool)
(declare-fun nondet_init$0 () Bool)
(declare-fun old_curr_2$0 () Loc)
(declare-fun old_curr_4$0 () Loc)
(declare-fun old_curr_init$0 () Loc)
(declare-fun prv_4$0 () Loc)
(declare-fun prv_5$0 () Loc)
(declare-fun prv_init$0 () Loc)
(declare-fun res_3$0 () Loc)
(declare-fun res_4$0 () Loc)
(declare-fun res_init$0 () Loc)
(declare-fun sk_?X_67$0 () SetLoc)
(declare-fun sk_?X_68$0 () SetLoc)
(declare-fun sk_?X_69$0 () SetLoc)
(declare-fun sk_?X_70$0 () SetLoc)
(declare-fun sk_?X_71$0 () SetLoc)
(declare-fun sk_?X_72$0 () SetLoc)
(declare-fun sk_?X_73$0 () SetLoc)
(declare-fun sk_?X_74$0 () SetLoc)
(declare-fun sk_?X_75$0 () SetLoc)
(declare-fun sk_?X_76$0 () SetLoc)
(declare-fun sk_?X_77$0 () SetLoc)
(declare-fun sk_?X_78$0 () SetLoc)
(declare-fun sk_?X_79$0 () SetLoc)
(declare-fun sk_?X_80$0 () SetLoc)
(declare-fun sk_?X_81$0 () SetLoc)
(declare-fun sk_?X_82$0 () SetLoc)
(declare-fun sk_?e_3$0 () Loc)
(declare-fun sk_?e_4$0 () Loc)
(declare-fun sk_FP_2$0 () SetLoc)
(declare-fun sk_FP_3$0 () SetLoc)

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y)
            (Btwn$0 next$0 prv_init$0 (read$0 next$0 prv_init$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y)
            (Btwn$0 next$0 old_curr_4$0 (read$0 next$0 old_curr_4$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_2$0 null$0 (read$0 next_2$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y)
            (Btwn$0 next_2$0 prv_init$0 (read$0 next_2$0 prv_init$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_init$0) prv_init$0))
            (not (Btwn$0 next$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 old_curr_4$0) old_curr_4$0))
            (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 null$0) null$0))
            (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 prv_init$0) prv_init$0))
            (not (Btwn$0 next_2$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y))))

(assert (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)))

(assert (Btwn$0 next$0 prv_init$0 (read$0 next$0 prv_init$0)
  (read$0 next$0 prv_init$0)))

(assert (Btwn$0 next$0 old_curr_4$0 (read$0 next$0 old_curr_4$0)
  (read$0 next$0 old_curr_4$0)))

(assert (Btwn$0 next_2$0 null$0 (read$0 next_2$0 null$0) (read$0 next_2$0 null$0)))

(assert (Btwn$0 next_2$0 prv_init$0 (read$0 next_2$0 prv_init$0)
  (read$0 next_2$0 prv_init$0)))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_71$0 sk_?X_69$0))
                 (or (in$0 x sk_?X_71$0) (in$0 x sk_?X_69$0)))
            (and (not (in$0 x sk_?X_71$0)) (not (in$0 x sk_?X_69$0))
                 (not (in$0 x (union$0 sk_?X_71$0 sk_?X_69$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_70$0 sk_?X_69$0))
                 (or (in$0 x sk_?X_70$0) (in$0 x sk_?X_69$0)))
            (and (not (in$0 x sk_?X_70$0)) (not (in$0 x sk_?X_69$0))
                 (not (in$0 x (union$0 sk_?X_70$0 sk_?X_69$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_74$0 sk_?X_73$0))
                 (or (in$0 x sk_?X_74$0) (in$0 x sk_?X_73$0)))
            (and (not (in$0 x sk_?X_74$0)) (not (in$0 x sk_?X_73$0))
                 (not (in$0 x (union$0 sk_?X_74$0 sk_?X_73$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_70$0 sk_?X_77$0))
                 (or (in$0 x sk_?X_70$0) (in$0 x sk_?X_77$0)))
            (and (not (in$0 x sk_?X_70$0)) (not (in$0 x sk_?X_77$0))
                 (not (in$0 x (union$0 sk_?X_70$0 sk_?X_77$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_82$0 sk_?X_73$0))
                 (or (in$0 x sk_?X_82$0) (in$0 x sk_?X_73$0)))
            (and (not (in$0 x sk_?X_82$0)) (not (in$0 x sk_?X_73$0))
                 (not (in$0 x (union$0 sk_?X_82$0 sk_?X_73$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_79$0 sk_?X_77$0))
                 (or (in$0 x sk_?X_79$0) (in$0 x sk_?X_77$0)))
            (and (not (in$0 x sk_?X_79$0)) (not (in$0 x sk_?X_77$0))
                 (not (in$0 x (union$0 sk_?X_79$0 sk_?X_77$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_70$0) (in$0 x sk_?X_69$0)
                 (in$0 x (intersection$0 sk_?X_70$0 sk_?X_69$0)))
            (and (or (not (in$0 x sk_?X_70$0)) (not (in$0 x sk_?X_69$0)))
                 (not (in$0 x (intersection$0 sk_?X_70$0 sk_?X_69$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_71$0) (in$0 x sk_?X_69$0)
                 (in$0 x (intersection$0 sk_?X_71$0 sk_?X_69$0)))
            (and (or (not (in$0 x sk_?X_71$0)) (not (in$0 x sk_?X_69$0)))
                 (not (in$0 x (intersection$0 sk_?X_71$0 sk_?X_69$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_74$0) (in$0 x sk_?X_73$0)
                 (in$0 x (intersection$0 sk_?X_74$0 sk_?X_73$0)))
            (and (or (not (in$0 x sk_?X_74$0)) (not (in$0 x sk_?X_73$0)))
                 (not (in$0 x (intersection$0 sk_?X_74$0 sk_?X_73$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_70$0) (in$0 x sk_?X_77$0)
                 (in$0 x (intersection$0 sk_?X_70$0 sk_?X_77$0)))
            (and (or (not (in$0 x sk_?X_70$0)) (not (in$0 x sk_?X_77$0)))
                 (not (in$0 x (intersection$0 sk_?X_70$0 sk_?X_77$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_79$0) (in$0 x sk_?X_77$0)
                 (in$0 x (intersection$0 sk_?X_79$0 sk_?X_77$0)))
            (and (or (not (in$0 x sk_?X_79$0)) (not (in$0 x sk_?X_77$0)))
                 (not (in$0 x (intersection$0 sk_?X_79$0 sk_?X_77$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_82$0) (in$0 x sk_?X_73$0)
                 (in$0 x (intersection$0 sk_?X_82$0 sk_?X_73$0)))
            (and (or (not (in$0 x sk_?X_82$0)) (not (in$0 x sk_?X_73$0)))
                 (not (in$0 x (intersection$0 sk_?X_82$0 sk_?X_73$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0)
                 (in$0 x (setminus$0 Alloc$0 (setenum$0 old_curr_4$0)))
                 (not (in$0 x (setenum$0 old_curr_4$0))))
            (and
                 (or (in$0 x (setenum$0 old_curr_4$0))
                     (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 (setenum$0 old_curr_4$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP$0)
                 (in$0 x (setminus$0 FP$0 (setenum$0 old_curr_4$0)))
                 (not (in$0 x (setenum$0 old_curr_4$0))))
            (and (or (in$0 x (setenum$0 old_curr_4$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 (setenum$0 old_curr_4$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))))

(assert (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (= (read$0 (write$0 next$0 prv_init$0 curr_5$0) prv_init$0) curr_5$0))

(assert (or (= null$0 prv_init$0)
    (= (read$0 next$0 null$0)
      (read$0 (write$0 next$0 prv_init$0 curr_5$0) null$0))))

(assert (or (= prv_init$0 prv_init$0)
    (= (read$0 next$0 prv_init$0)
      (read$0 (write$0 next$0 prv_init$0 curr_5$0) prv_init$0))))

(assert (or (= old_curr_4$0 prv_init$0)
    (= (read$0 next$0 old_curr_4$0)
      (read$0 (write$0 next$0 prv_init$0 curr_5$0) old_curr_4$0))))

(assert (= (read$0 next$0 null$0) null$0))

(assert (= (read$0 next_2$0 null$0) null$0))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (Btwn$0 next$0 curr_init$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_69$0 next$0 curr_init$0 null$0))))

(assert (or (Btwn$0 next_2$0 curr_5$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_77$0 next_2$0 curr_5$0 null$0))))

(assert (or
    (and
         (or
             (and
                  (= next_2$0
                    (write$0 next$0 prv_4$0 (read$0 next$0 old_curr_4$0)))
                  (not (= prv_4$0 null$0)))
             (and (= next_2$0 next$0) (= prv_4$0 null$0) (= res_3$0 res_4$0)
                  (= res_4$0 (read$0 next$0 old_curr_4$0))))
         (= Alloc_2$0 (setminus$0 Alloc$0 (setenum$0 old_curr_4$0)))
         (= FP_3$0 (setminus$0 FP$0 (setenum$0 old_curr_4$0))) nondet_3$0)
    (and (= Alloc_2$0 Alloc$0) (= FP_3$0 FP$0) (= next_2$0 next$0)
         (= prv_4$0 prv_5$0) (= prv_5$0 old_curr_4$0) (not nondet_3$0))))

(assert (= curr_4$0 curr_init$0))

(assert (= nondet_2$0 nondet_init$0))

(assert (= old_curr_4$0 curr_4$0))

(assert (= res_3$0 res_init$0))

(assert (= sk_?X_67$0 (union$0 sk_?X_71$0 sk_?X_69$0)))

(assert (= sk_?X_69$0 (lseg_domain$0 next$0 curr_init$0 null$0)))

(assert (= sk_?X_71$0 (union$0 sk_?X_74$0 sk_?X_72$0)))

(assert (= sk_?X_73$0 (setenum$0 prv_init$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (= sk_?X_75$0 (union$0 sk_?X_79$0 sk_?X_77$0)))

(assert (= sk_?X_77$0 (lseg_domain$0 next_2$0 curr_5$0 null$0)))

(assert (= sk_?X_79$0 (union$0 sk_?X_82$0 sk_?X_80$0)))

(assert (= sk_?X_81$0 (setenum$0 prv_4$0)))

(assert (= sk_FP_2$0 sk_?X_76$0))

(assert (or (in$0 sk_?e_3$0 (intersection$0 sk_?X_79$0 sk_?X_77$0))
    (in$0 sk_?e_3$0 (intersection$0 sk_?X_82$0 sk_?X_80$0))
    (and (in$0 sk_?e_3$0 sk_FP_3$0) (not (in$0 sk_?e_3$0 FP_3$0)))
    (not (= (read$0 next_2$0 prv_4$0) curr_5$0))
    (not (Btwn$0 next_2$0 curr_5$0 null$0 null$0))
    (not (Btwn$0 next_2$0 res_3$0 prv_4$0 prv_4$0))))

(assert (not (= curr_4$0 null$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_2$0 curr_5$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_2$0 curr_5$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next_2$0 curr_5$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_2$0 curr_5$0 null$0)))))))

(assert (or (Btwn$0 next$0 res_init$0 prv_init$0 prv_init$0)
    (not (lseg_struct$0 sk_?X_74$0 next$0 res_init$0 prv_init$0))))

(assert (or (Btwn$0 next_2$0 res_3$0 prv_4$0 prv_4$0)
    (not (lseg_struct$0 sk_?X_82$0 next_2$0 res_3$0 prv_4$0))))

(assert (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= curr_5$0 (read$0 next$0 curr_4$0)))

(assert (= old_curr_2$0 old_curr_init$0))

(assert (= prv_4$0 prv_init$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= sk_?X_68$0 (union$0 sk_?X_70$0 sk_?X_69$0)))

(assert (= sk_?X_70$0 emptyset$0))

(assert (= sk_?X_72$0 sk_?X_73$0))

(assert (= sk_?X_74$0 (lseg_domain$0 next$0 res_init$0 prv_init$0)))

(assert (or
    (and (= (read$0 next$0 prv_init$0) curr_init$0) (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_71$0 sk_?X_69$0))
         (= emptyset$0 (intersection$0 sk_?X_74$0 sk_?X_72$0))
         (= sk_?X_67$0 FP$0)
         (lseg_struct$0 sk_?X_69$0 next$0 curr_init$0 null$0)
         (lseg_struct$0 sk_?X_74$0 next$0 res_init$0 prv_init$0))
    (and (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_70$0 sk_?X_69$0))
         (= prv_init$0 null$0) (= res_init$0 curr_init$0) (= sk_?X_68$0 FP$0)
         (lseg_struct$0 sk_?X_69$0 next$0 curr_init$0 null$0))))

(assert (= sk_?X_76$0 (union$0 sk_?X_78$0 sk_?X_77$0)))

(assert (= sk_?X_78$0 emptyset$0))

(assert (= sk_?X_80$0 sk_?X_81$0))

(assert (= sk_?X_82$0 (lseg_domain$0 next_2$0 res_3$0 prv_4$0)))

(assert (= sk_FP_3$0 sk_?X_75$0))

(assert (or (in$0 sk_?e_4$0 (intersection$0 sk_?X_78$0 sk_?X_77$0))
    (and (in$0 sk_?e_4$0 sk_FP_2$0) (not (in$0 sk_?e_4$0 FP_3$0)))
    (not (= prv_4$0 null$0)) (not (= res_3$0 curr_5$0))
    (not (Btwn$0 next_2$0 curr_5$0 null$0 null$0))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 res_init$0 l1 prv_init$0)
                 (in$0 l1 (lseg_domain$0 next$0 res_init$0 prv_init$0))
                 (not (= l1 prv_init$0)))
            (and
                 (or (= l1 prv_init$0)
                     (not (Btwn$0 next$0 res_init$0 l1 prv_init$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 res_init$0 prv_init$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_2$0 res_3$0 l1 prv_4$0)
                 (in$0 l1 (lseg_domain$0 next_2$0 res_3$0 prv_4$0))
                 (not (= l1 prv_4$0)))
            (and
                 (or (= l1 prv_4$0)
                     (not (Btwn$0 next_2$0 res_3$0 l1 prv_4$0)))
                 (not (in$0 l1 (lseg_domain$0 next_2$0 res_3$0 prv_4$0)))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or
                 (Btwn$0
                   (write$0 next$0 prv_4$0 (read$0 next$0 old_curr_4$0)) ?z
                   ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v prv_4$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z prv_4$0
                                               prv_4$0)))))
                          (and (not (= prv_4$0 ?v))
                               (or (Btwn$0 next$0 ?z prv_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z prv_4$0 prv_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u prv_4$0)
                               (or
                                   (Btwn$0 next$0
                                     (read$0 next$0 old_curr_4$0) ?v prv_4$0)
                                   (and
                                        (Btwn$0 next$0
                                          (read$0 next$0 old_curr_4$0) ?v ?v)
                                        (not
                                             (Btwn$0 next$0
                                               (read$0 next$0 old_curr_4$0)
                                               prv_4$0 prv_4$0)))))
                          (and (not (= prv_4$0 ?v))
                               (or (Btwn$0 next$0 ?z prv_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z prv_4$0 prv_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?u
                                 ?v)
                               (or
                                   (Btwn$0 next$0
                                     (read$0 next$0 old_curr_4$0) ?v prv_4$0)
                                   (and
                                        (Btwn$0 next$0
                                          (read$0 next$0 old_curr_4$0) ?v ?v)
                                        (not
                                             (Btwn$0 next$0
                                               (read$0 next$0 old_curr_4$0)
                                               prv_4$0 prv_4$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v prv_4$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z prv_4$0 prv_4$0)))))
                 (and (not (= prv_4$0 ?v))
                      (or (Btwn$0 next$0 ?z prv_4$0 ?v)
                          (and (Btwn$0 next$0 ?z prv_4$0 prv_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u prv_4$0)
                      (or
                          (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?v
                            prv_4$0)
                          (and
                               (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?v
                                 ?v)
                               (not
                                    (Btwn$0 next$0
                                      (read$0 next$0 old_curr_4$0) prv_4$0
                                      prv_4$0)))))
                 (and (not (= prv_4$0 ?v))
                      (or (Btwn$0 next$0 ?z prv_4$0 ?v)
                          (and (Btwn$0 next$0 ?z prv_4$0 prv_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?u ?v)
                      (or
                          (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?v
                            prv_4$0)
                          (and
                               (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?v
                                 ?v)
                               (not
                                    (Btwn$0 next$0
                                      (read$0 next$0 old_curr_4$0) prv_4$0
                                      prv_4$0)))))
                 (not
                      (Btwn$0
                        (write$0 next$0 prv_4$0 (read$0 next$0 old_curr_4$0))
                        ?z ?u ?v))))))

(assert (forall ((?x Loc)) (Btwn$0 next_2$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_2$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?x ?z ?z))
            (Btwn$0 next_2$0 ?x ?y ?z) (Btwn$0 next_2$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?y) (Btwn$0 next_2$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?y ?z ?z))
            (Btwn$0 next_2$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?y ?u ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?u) (Btwn$0 next_2$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?x ?u ?y))
            (and (Btwn$0 next_2$0 ?x ?u ?z) (Btwn$0 next_2$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))))

(check-sat)
(exit)
